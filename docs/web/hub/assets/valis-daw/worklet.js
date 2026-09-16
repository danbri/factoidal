/*
 * worklet.js — the AudioWorkletProcessor that runs the engine on the
 * audio rendering thread. Loaded with `audioWorklet.addModule(new
 * URL('./worklet.js', import.meta.url))` (audio.mjs): a same-origin
 * file URL, never a Blob or data URL, so it survives a page whose
 * Content-Security-Policy is `script-src 'self'`. AudioWorklet modules
 * run as real ES modules, so this file imports dsp.mjs directly rather
 * than the original app's approach of stringifying the engine factory
 * into the module source.
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

export const WORKLET_NAME = 'valis-engine';

class ValisProcessor extends AudioWorkletProcessor {
  constructor() {
    super();
    this.engine = null;
    this.acc = 0;
    this.port.onmessage = (e) => this.onMessage(e.data);
  }
  onMessage(m) {
    try {
      switch (m.type) {
        case 'circuit': this.engine = new Engine(m.compiled, sampleRate); this.port.postMessage({ type: 'ready', nodes: this.engine.nodes.length, sr: sampleRate }); break;
        case 'sample': if (this.engine) this.engine.setSample(m.node, m.data, m.sr); break;
        case 'event': if (this.engine) this.engine.pushEvent(m.event); break;
        case 'events': if (this.engine) for (const ev of m.events) this.engine.pushEvent(ev); break;
        case 'param': if (this.engine) this.engine.setParam(m.node, m.ci, m.value); break;
        case 'stop': this.engine = null; break;
      }
    } catch (err) { this.port.postMessage({ type: 'error', message: String(err && err.stack || err) }); }
  }
  process(inputs, outputs) {
    const out = outputs[0]; if (!out || !out.length) return true;
    const Lc = out[0], Rc = out[1] || null, n = Lc.length;
    const inp = inputs[0]; const inL = inp && inp[0] ? inp[0] : null, inR = inp && inp[1] ? inp[1] : null;
    const eng = this.engine;
    if (!eng) { Lc.fill(0); if (Rc) Rc.fill(0); return true; }
    try { eng.process(inL, inR, Lc, Rc, n, currentTime); }
    catch (err) { this.engine = null; this.port.postMessage({ type: 'error', message: String(err && err.stack || err) }); return true; }
    this.acc += n;
    if (this.acc >= 2048) {
      this.acc = 0;
      const peaks = eng.takePeaks();
      this.port.postMessage({ type: 'meters', peaks, readouts: eng.readouts(), host: { gate: eng.host.gate, note: eng.host.note, ppq: eng.host.ppq }, warnings: eng.warnings.splice(0) }, [peaks.buffer]);
    }
    return true;
  }
}

registerProcessor(WORKLET_NAME, ValisProcessor);
