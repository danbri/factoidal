/*
 * audio.mjs — the host side of the engine. Owns the AudioContext, loads
 * the engine into an AudioWorklet (falling back to a ScriptProcessorNode
 * when the page's policy refuses worklet modules), routes an input
 * source into it, forwards note/transport/param events with audio-clock
 * timestamps, and relays meter data back to the caller.
 *
 * Runs on the main thread (uses `document`/`navigator`), unlike
 * dsp.mjs/worklet.js which run inside the AudioWorkletGlobalScope.
 * `ensureEngineNode()` loads the processor with
 * `audioWorklet.addModule(new URL('./worklet.js', import.meta.url))` --
 * a same-origin file URL, never a Blob or data URL, so it survives the
 * hub page's `script-src 'self'` Content-Security-Policy. WORKLET_NAME
 * below must match the string worklet.js passes to registerProcessor().
 *
 * This is the owner's clean-room JavaScript reimplementation of the
 * Valis synthesizer engine (https://github.com/danja/valis), built from
 * the Valis Turtle vocabulary (third_party/valis/vocabs/valis.ttl) and
 * its documentation, not from the upstream C++ (src/, include/).
 * Licensed with this repository (Apache-2.0). Derivation review:
 * https://github.com/danbri/factoidal/issues/687#issuecomment-5701030083
 */
'use strict';

import { Engine } from './dsp.mjs';

const L = () => console;
const WORKLET_NAME = 'valis-engine';

const state = {
  ctx: null, node: null, mode: null, analyser: null, master: null, inputGain: null,
  inputSource: 'none', inputNode: null, micStream: null, sampleBuffer: null, sampleBufferName: '',
  ready: false, compiled: null, meterHandlers: new Set(), errorHandlers: new Set(), unlocked: false, silent: null,
  engine: null, loadingCircuit: null, pendingSamples: [],
};

function ensureContext() {
  if (state.ctx) return state.ctx;
  const AC = globalThis.AudioContext || globalThis.webkitAudioContext;
  if (!AC) throw new Error('Web Audio is not available in this browser');
  const ctx = new AC({ latencyHint: 'interactive' });
  state.ctx = ctx;
  state.master = ctx.createGain(); state.master.gain.value = 0.8;
  state.analyser = ctx.createAnalyser(); state.analyser.fftSize = 2048; state.analyser.smoothingTimeConstant = 0.6;
  state.inputGain = ctx.createGain(); state.inputGain.gain.value = 1;
  state.master.connect(state.analyser); state.analyser.connect(ctx.destination);
  ctx.addEventListener('statechange', () => {
    L().info(`audio: context state → ${ctx.state}`);
    if (ctx.state === 'interrupted' || ctx.state === 'suspended') for (const fn of state.errorHandlers) fn({ type: 'state', state: ctx.state });
  });
  L().info(`audio: AudioContext created, sample rate ${ctx.sampleRate} Hz, base latency ${ctx.baseLatency != null ? (ctx.baseLatency * 1000).toFixed(1) + ' ms' : 'n/a'}`);
  return ctx;
}

// iOS: Web Audio starts silent until a user gesture resumes the context, and
// the ringer switch mutes it unless an HTMLMediaElement is also playing.
async function unlock() {
  const ctx = ensureContext();
  if (ctx.state !== 'running') { try { await ctx.resume(); } catch (e) { L().warn('audio: resume failed: ' + e.message); } }
  if (!state.silent) {
    try {
      const a = document.createElement('audio');
      a.setAttribute('playsinline', ''); a.loop = true; a.volume = 0.01;
      a.src = 'data:audio/wav;base64,UklGRjQAAABXQVZFZm10IBAAAAABAAEAgD4AAIA+AAABAAgAZGF0YRAAAACAgICAgICAgICAgICAgICA';
      const p = a.play(); if (p && p.catch) p.catch(() => {});
      state.silent = a;
    } catch (e) { /* optional */ }
  }
  if (!state.unlocked && ctx.state === 'running') { state.unlocked = true; L().info('audio: context unlocked by user gesture'); }
  return ctx.state === 'running';
}

async function ensureEngineNode() {
  const ctx = ensureContext();
  if (state.node) return state.node;
  let node = null;
  if (ctx.audioWorklet && typeof AudioWorkletNode !== 'undefined') {
    try {
      await ctx.audioWorklet.addModule(new URL('./worklet.js', import.meta.url));
      node = new AudioWorkletNode(ctx, WORKLET_NAME, { numberOfInputs: 1, numberOfOutputs: 1, outputChannelCount: [2] });
      node.port.onmessage = (e) => onEngineMessage(e.data);
      state.mode = 'worklet';
      L().info('audio: engine running in an AudioWorklet (module loaded from worklet.js)');
    } catch (e) { L().warn(`audio: AudioWorklet module refused: ${e.message}`); }
  } else L().warn('audio: AudioWorklet is not available in this browser');
  if (!node) {
    const sp = ctx.createScriptProcessor(1024, 2, 2);
    const local = { engine: null, acc: 0 };
    sp.onaudioprocess = (ev) => {
      const outL = ev.outputBuffer.getChannelData(0), outR = ev.outputBuffer.getChannelData(1);
      const inL = ev.inputBuffer.numberOfChannels > 0 ? ev.inputBuffer.getChannelData(0) : null;
      const inR = ev.inputBuffer.numberOfChannels > 1 ? ev.inputBuffer.getChannelData(1) : null;
      const eng = local.engine;
      if (!eng) { outL.fill(0); outR.fill(0); return; }
      try { eng.process(inL, inR, outL, outR, outL.length, ev.playbackTime); }
      catch (err) { local.engine = null; onEngineMessage({ type: 'error', message: String(err && err.stack || err) }); return; }
      local.acc += outL.length;
      if (local.acc >= 2048) { local.acc = 0; onEngineMessage({ type: 'meters', peaks: eng.takePeaks(), readouts: eng.readouts(), host: { gate: eng.host.gate, note: eng.host.note, ppq: eng.host.ppq }, warnings: eng.warnings.splice(0) }); }
    };
    // Emulate the worklet's message port so the rest of the host does not care which mode it is in.
    sp.port = { postMessage(m) {
      try {
        switch (m.type) {
          case 'circuit': local.engine = new Engine(m.compiled, ctx.sampleRate); onEngineMessage({ type: 'ready', nodes: local.engine.nodes.length, sr: ctx.sampleRate }); break;
          case 'sample': if (local.engine) local.engine.setSample(m.node, m.data, m.sr); break;
          case 'event': if (local.engine) local.engine.pushEvent(m.event); break;
          case 'events': if (local.engine) for (const ev of m.events) local.engine.pushEvent(ev); break;
          case 'param': if (local.engine) local.engine.setParam(m.node, m.ci, m.value); break;
          case 'stop': local.engine = null; break;
        }
      } catch (err) { onEngineMessage({ type: 'error', message: String(err && err.stack || err) }); }
    } };
    node = sp; state.mode = 'scriptprocessor';
    L().warn('audio: falling back to a ScriptProcessorNode on the main thread (1024-sample buffers; expect higher latency and dropouts while the UI is busy)');
  }
  state.inputGain.connect(node);
  node.connect(state.master);
  state.node = node;
  return node;
}

function onEngineMessage(m) {
  switch (m.type) {
    case 'ready':
      state.ready = true;
      L().info(`engine: circuit instantiated in the ${state.mode} — ${m.nodes} elements at ${m.sr} Hz`);
      if (state.loadingCircuit) { state.loadingCircuit.resolve(); state.loadingCircuit = null; }
      for (const s of state.pendingSamples.splice(0)) post(s);
      break;
    case 'meters':
      for (const fn of state.meterHandlers) fn(m);
      if (m.warnings && m.warnings.length) for (const w of m.warnings) L().warn('engine: ' + w);
      break;
    case 'error':
      L().error('engine: ' + m.message);
      state.ready = false;
      if (state.loadingCircuit) { state.loadingCircuit.reject(new Error(m.message)); state.loadingCircuit = null; }
      for (const fn of state.errorHandlers) fn({ type: 'engine', message: m.message });
      break;
    default: break;
  }
}
function post(m, transfer) { if (state.node) state.node.port.postMessage(m, transfer); }

async function loadCircuit(compiled) {
  await ensureEngineNode();
  state.compiled = compiled; state.ready = false;
  return new Promise((resolve, reject) => {
    state.loadingCircuit = { resolve, reject };
    post({ type: 'circuit', compiled });
    setTimeout(() => { if (state.loadingCircuit) { state.loadingCircuit = null; reject(new Error('engine did not confirm the circuit within 5 s')); } }, 5000);
  });
}

function now() { return state.ctx ? state.ctx.currentTime : 0; }
function sendEvent(ev) { post({ type: 'event', event: ev }); }
function sendEvents(evs) { if (evs.length) post({ type: 'events', events: evs }); }
function setParam(nodeIdx, ci, value) { post({ type: 'param', node: nodeIdx, ci, value }); }
function noteOn(note, vel, when) { sendEvent({ type: 'note', on: true, note, vel, when: when == null ? now() : when }); }
function noteOff(note, when) { sendEvent({ type: 'note', on: false, note, when: when == null ? now() : when }); }
function panic() { sendEvent({ type: 'panic', when: 0 }); }
function setTransport(t) { sendEvent(Object.assign({ type: 'transport', when: now() }, t)); }
function setMaster(v) { if (state.master) state.master.gain.setTargetAtTime(v, now(), 0.02); }

async function decodeToMono(arrayBuffer) {
  const ctx = ensureContext();
  const buf = await new Promise((res, rej) => { const p = ctx.decodeAudioData(arrayBuffer.slice(0), res, rej); if (p && p.then) p.then(res, rej); });
  const n = buf.length, ch = buf.numberOfChannels, out = new Float32Array(n);
  for (let c = 0; c < ch; c++) { const d = buf.getChannelData(c); for (let i = 0; i < n; i++) out[i] += d[i] / ch; }
  return { data: out, sr: buf.sampleRate, seconds: buf.duration, buffer: buf };
}
function sendSample(nodeIdx, mono) {
  const data = Float32Array.from(mono.data);
  const msg = { type: 'sample', node: nodeIdx, data, sr: mono.sr };
  if (state.ready) post(msg, state.mode === 'worklet' ? [data.buffer] : undefined); else state.pendingSamples.push(msg);
}

// ---- Input source for circuits with val:Input ----
async function setInputSource(kind) {
  const ctx = ensureContext();
  if (state.inputNode) { try { state.inputNode.disconnect(); if (state.inputNode.stop) state.inputNode.stop(); } catch (e) { /* already stopped */ } state.inputNode = null; }
  if (state.micStream && kind !== 'mic') { for (const t of state.micStream.getTracks()) t.stop(); state.micStream = null; }
  state.inputSource = kind;
  if (kind === 'none') { L().info('input: silence'); return kind; }
  if (kind === 'tone') {
    const o = ctx.createOscillator(); o.type = 'sawtooth'; o.frequency.value = 110;
    const g = ctx.createGain(); g.gain.value = 0.4; o.connect(g); g.connect(state.inputGain); o.start();
    state.inputNode = o; L().info('input: 110 Hz sawtooth test tone'); return kind;
  }
  if (kind === 'sample') {
    if (!state.sampleBuffer) { L().warn('input: no sample decoded yet'); return 'none'; }
    const s = ctx.createBufferSource(); s.buffer = state.sampleBuffer; s.loop = true; s.connect(state.inputGain); s.start();
    state.inputNode = s; L().info(`input: looping ${state.sampleBufferName} (${state.sampleBuffer.duration.toFixed(2)} s)`); return kind;
  }
  if (kind === 'mic') {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) { L().warn('input: microphone access is not available here'); return 'none'; }
    try {
      const stream = await navigator.mediaDevices.getUserMedia({ audio: { echoCancellation: false, noiseSuppression: false, autoGainControl: false }, video: false });
      state.micStream = stream;
      const src = ctx.createMediaStreamSource(stream); src.connect(state.inputGain); state.inputNode = src;
      L().info('input: microphone (echo cancellation off). Use headphones to avoid feedback.');
      return kind;
    } catch (e) { L().warn('input: microphone refused: ' + e.message); state.inputSource = 'none'; return 'none'; }
  }
  return 'none';
}

function onMeters(fn) { state.meterHandlers.add(fn); return () => state.meterHandlers.delete(fn); }
function onError(fn) { state.errorHandlers.add(fn); return () => state.errorHandlers.delete(fn); }
function analyser() { return state.analyser; }
function mode() { return state.mode; }

export {
  state, ensureContext, unlock, loadCircuit, now, noteOn, noteOff, panic, setTransport, setParam, sendEvents, setMaster,
  decodeToMono, sendSample, setInputSource, onMeters, onError, analyser, mode,
};
