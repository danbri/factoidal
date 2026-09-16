/*
 * sequencer.mjs — the host transport. A lookahead scheduler stamps note
 * events with audio-clock times and hands them to audio.mjs; the caller
 * follows the playhead through onStep. Two pattern kinds: drum rows keyed
 * by MIDI note (one per val:NoteGate) and a monophonic note sequence for
 * circuits driven by the host gate (val:MidiPitch, host-gated envelopes).
 *
 * This is the owner's clean-room JavaScript reimplementation of the
 * Valis synthesizer engine (https://github.com/danja/valis), built from
 * the Valis Turtle vocabulary (third_party/valis/vocabs/valis.ttl) and
 * its documentation, not from the upstream C++ (src/, include/).
 * Licensed with this repository (Apache-2.0). Derivation review:
 * https://github.com/danbri/factoidal/issues/687#issuecomment-5701030083
 */
'use strict';

import * as Audio from './audio.mjs';

const STEPS = 16;
const LOOKAHEAD = 0.12, TICK_MS = 25;
const GM = { 35: 'Kick 2', 36: 'Kick', 37: 'Rim', 38: 'Snare', 39: 'Clap', 40: 'Snare 2', 41: 'Low tom', 42: 'Closed hat', 43: 'Mid tom', 44: 'Pedal hat', 45: 'Low tom 2', 46: 'Open hat', 47: 'Mid tom 2', 48: 'High tom 2', 49: 'Crash', 50: 'High tom', 51: 'Ride', 52: 'China', 53: 'Ride bell', 54: 'Tambourine', 55: 'Splash', 56: 'Cowbell', 57: 'Crash 2', 58: 'Vibraslap', 59: 'Ride 2', 60: 'High bongo', 61: 'Low bongo', 62: 'Mute conga', 63: 'High conga', 64: 'Low conga', 65: 'High timbale', 66: 'Low timbale', 67: 'High agogo', 68: 'Low agogo', 69: 'Cabasa', 70: 'Maracas', 75: 'Claves', 76: 'High woodblock', 77: 'Low woodblock' };
const NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];

const S = {
  bpm: 120, playing: false, mode: 'drums', rows: [], notes: [], step: -1,
  timer: null, nextTime: 0, nextStep: 0, queue: [], stepListeners: new Set(), changeListeners: new Set(),
  velocities: [0, 0.8, 1.0],
};

function noteName(n) { return NOTE_NAMES[((n % 12) + 12) % 12] + (Math.floor(n / 12) - 1); }
function stepSeconds() { return 60 / S.bpm / 4; }
function emitChange() { for (const fn of S.changeListeners) fn(); }

function configure(compiled, sectionNames) {
  const gates = compiled.nodes.filter((n) => n.type === 'NoteGate').map((n) => ({ node: n, note: Math.round(n.ciBase[n.ci.indexOf('note')]) }));
  S.rows = []; S.notes = [];
  if (gates.length) {
    S.mode = 'drums';
    gates.sort((a, b) => a.note - b.note);
    for (const g of gates) {
      const name = (sectionNames && sectionNames[g.node.idx]) || GM[g.note] || g.node.local;
      S.rows.push({ note: g.note, name, local: g.node.local, pattern: new Uint8Array(STEPS), mute: false, idx: g.node.idx });
    }
    const seed = { 36: [0, 4, 8, 12], 35: [0, 4, 8, 12], 38: [4, 12], 40: [4, 12], 42: [0, 2, 4, 6, 8, 10, 12], 39: [4, 12], 46: [14] };
    for (const r of S.rows) if (seed[r.note]) for (const st of seed[r.note]) r.pattern[st] = st % 4 === 0 ? 2 : 1;
  } else {
    // Host-gated circuits: anything reading MIDI pitch/velocity, or a port left at the -1 "follow the host" sentinel.
    const hostGated = compiled.nodes.some((n) => ['MidiPitch', 'MidiVelocity', 'MidiInterval'].includes(n.type) || n.ci.some((sym, k) => ['gate', 'trigger', 'velocity'].includes(sym) && n.ciBase[k] < 0));
    S.mode = hostGated ? 'notes' : 'effect';
    const melody = [45, 0, 57, 45, 48, 0, 45, 57, 43, 0, 55, 43, 46, 0, 43, 55];
    for (let i = 0; i < STEPS; i++) S.notes.push({ note: melody[i] || 45, vel: 0.85, on: melody[i] > 0, gate: 0.6 });
  }
  S.step = -1;
  emitChange();
}

function scheduleStep(step, when) {
  const dur = stepSeconds(), evs = [];
  if (S.mode === 'drums') {
    for (const r of S.rows) {
      const v = r.pattern[step];
      if (!v || r.mute) continue;
      // Hold the gate until just before the row's next hit, up to a beat, so
      // long envelopes (a 500 ms kick decay) are not cut by the release stage.
      let gap = STEPS;
      for (let k = 1; k < STEPS; k++) if (r.pattern[(step + k) % STEPS]) { gap = k; break; }
      const hold = Math.min(dur * 4 * 0.95, dur * gap - 0.005);
      evs.push({ type: 'note', on: true, note: r.note, vel: S.velocities[v] || 0.8, when });
      evs.push({ type: 'note', on: false, note: r.note, when: when + hold });
    }
  } else if (S.mode === 'notes') {
    const n = S.notes[step];
    if (n && n.on) {
      evs.push({ type: 'note', on: true, note: n.note, vel: n.vel, when });
      evs.push({ type: 'note', on: false, note: n.note, when: when + dur * n.gate });
    }
  }
  Audio.sendEvents(evs);
  S.queue.push({ step, when });
}
function tick() {
  const now = Audio.now();
  while (S.nextTime < now + LOOKAHEAD) {
    scheduleStep(S.nextStep, S.nextTime);
    S.nextTime += stepSeconds();
    S.nextStep = (S.nextStep + 1) % STEPS;
  }
}
function frame() {
  if (!S.playing) return;
  const now = Audio.now();
  let cur = null;
  while (S.queue.length && S.queue[0].when <= now) cur = S.queue.shift();
  if (cur && cur.step !== S.step) { S.step = cur.step; for (const fn of S.stepListeners) fn(S.step); }
  requestAnimationFrame(frame);
}
async function start() {
  await Audio.unlock();
  if (S.playing) return;
  S.playing = true;
  S.nextTime = Audio.now() + 0.05; S.nextStep = 0; S.queue = []; S.step = -1;
  Audio.setTransport({ tempo: S.bpm, playing: 1, ppq: 0, when: S.nextTime });
  tick();
  S.timer = setInterval(tick, TICK_MS);
  requestAnimationFrame(frame);
  console.info(`transport: play at ${S.bpm} bpm (${S.mode} pattern, ${STEPS} steps)`);
  emitChange();
}
function stop() {
  if (!S.playing) return;
  S.playing = false;
  clearInterval(S.timer); S.timer = null; S.queue = [];
  Audio.panic();
  Audio.setTransport({ playing: 0 });
  S.step = -1;
  for (const fn of S.stepListeners) fn(-1);
  console.info('transport: stop');
  emitChange();
}
function setBpm(b) {
  S.bpm = Math.max(30, Math.min(300, Math.round(b)));
  if (S.playing) Audio.setTransport({ tempo: S.bpm });
  emitChange();
}
let pending = Promise.resolve();
function audition(note, vel, holdMs) {
  pending = pending.then(async () => {
    if (!Audio.state.unlocked) await Audio.unlock();
    Audio.noteOn(note, vel == null ? 0.9 : vel);
    if (holdMs != null) setTimeout(() => Audio.noteOff(note), holdMs);
  }).catch((e) => console.warn('audition: ' + e.message));
  return pending;
}
function release(note) { pending = pending.then(() => Audio.noteOff(note)); return pending; }

function toggle() { return S.playing ? stop() : start(); }
function onStep(fn) { S.stepListeners.add(fn); return () => S.stepListeners.delete(fn); }
function onChange(fn) { S.changeListeners.add(fn); return () => S.changeListeners.delete(fn); }
function cycleDrum(row, step) { const r = S.rows[row]; if (!r) return; r.pattern[step] = (r.pattern[step] + 1) % 3; emitChange(); }
function clearPattern() { for (const r of S.rows) r.pattern.fill(0); for (const n of S.notes) n.on = false; emitChange(); }

export {
  S, STEPS, GM, noteName, configure, start, stop, setBpm, audition, release,
  toggle, onStep, onChange, cycleDrum, clearPattern,
};
