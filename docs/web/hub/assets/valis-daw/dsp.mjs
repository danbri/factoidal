/*
 * dsp.mjs — the engine. A CompiledCircuit (plain JSON from compiler.mjs) is
 * instantiated into element objects and run in execution order. Every
 * element processes 32-sample blocks over Float64Array port buffers; single
 * source audio inputs are aliased straight to the source's output buffer, so
 * routing costs nothing. Feedback loops (multi-node stages) are stepped one
 * sample at a time. Control ports resolve on the same 32-sample grid the
 * ontology describes for control arcs. This module is loaded directly by
 * worklet.js inside the AudioWorkletGlobalScope, so it must not reference
 * `window` or `document`.
 *
 * This is the owner's clean-room JavaScript reimplementation of the
 * Valis synthesizer engine (https://github.com/danja/valis), built from
 * the Valis Turtle vocabulary (third_party/valis/vocabs/valis.ttl) and
 * its documentation, not from the upstream C++ (src/, include/).
 * Licensed with this repository (Apache-2.0). Derivation review:
 * https://github.com/danbri/factoidal/issues/687#issuecomment-5701030083
 */
'use strict';

  const CTRL = 32;
  const TWO_PI = Math.PI * 2;

  function clamp(v, lo, hi) { return v < lo ? lo : v > hi ? hi : v; }
  function db2lin(db) { return Math.pow(10, db / 20); }
  function lin2db(v) { return 20 * Math.log10(v + 1e-12); }
  function midiHz(n) { return 440 * Math.pow(2, (n - 69) / 12); }
  function polyblep(t, dt) {
    if (t < dt) { t /= dt; return t + t - t * t - 1; }
    if (t > 1 - dt) { t = (t - 1) / dt; return t * t + t + t + 1; }
    return 0;
  }
  function onepoleCoef(ms, sr) { return 1 - Math.exp(-1000 / (Math.max(0.01, ms) * sr)); }

  // ------------------------------------------------------------------
  // Base element
  // ------------------------------------------------------------------
  class El {
    constructor(spec, eng) {
      this.spec = spec; this.eng = eng; this.sr = eng.sr; this.idx = spec.idx;
      this.ai = spec.ai.map(() => new Float64Array(CTRL)); this.ai.push(new Float64Array(CTRL));
      this.ao = spec.ao.map(() => new Float64Array(CTRL)); this.ao.push(new Float64Array(CTRL));
      this.ci = new Float64Array(spec.ci.length + 1);
      this.base = new Float64Array(spec.ci.length + 1);
      this.co = new Float64Array(spec.co.length + 1);
      for (let i = 0; i < spec.ci.length; i++) { this.ci[i] = spec.ciBase[i]; this.base[i] = spec.ciBase[i]; }
      for (let i = 0; i < spec.co.length; i++) this.co[i] = spec.coDef[i] || 0;
      this.sum = [];      // ports with several sources: {dst, srcs}
      this.carcs = [];    // control arcs ending here
      this.driven = new Uint8Array(spec.ci.length + 1);
      this.spare = spec.ci.length;
      this.hasAudio = spec.ai.length > 0 || spec.ao.length > 0;
    }
    ciIdx(sym) { const i = this.spec.ci.indexOf(sym); return i < 0 ? this.spare : i; }
    coIdx(sym) { const i = this.spec.co.indexOf(sym); return i < 0 ? this.spec.co.length : i; }
    aiIdx(sym) { const i = this.spec.ai.indexOf(sym); return i < 0 ? this.spec.ai.length : i; }
    aoIdx(sym) { const i = this.spec.ao.indexOf(sym); return i < 0 ? this.spec.ao.length : i; }
    ctl() {}
    run(a, b) {}
  }

  // ------------------------------------------------------------------
  // Sources
  // ------------------------------------------------------------------
  class Oscillator extends El {
    constructor(s, e) { super(s, e); this.kF = this.ciIdx('frequency'); this.kS = this.ciIdx('shape'); this.o = this.aoIdx('out'); this.ph = 0; this.dt = 440 / this.sr; this.shape = 0; this.amp = 1; }
    ctl() { this.dt = clamp(this.ci[this.kF], 0, this.sr * 0.45) / this.sr; this.shape = Math.round(this.ci[this.kS]) | 0; }
    run(a, b) {
      const out = this.ao[this.o], dt = this.dt, amp = this.amp;
      let t = this.ph;
      switch (this.shape) {
        case 1: for (let s = a; s < b; s++) { out[s] = amp * (2 * t - 1 - polyblep(t, dt)); t += dt; if (t >= 1) t -= 1; } break;
        case 2: for (let s = a; s < b; s++) { let t2 = t + 0.5; if (t2 >= 1) t2 -= 1; out[s] = amp * ((t < 0.5 ? 1 : -1) + polyblep(t, dt) - polyblep(t2, dt)); t += dt; if (t >= 1) t -= 1; } break;
        case 3: for (let s = a; s < b; s++) { out[s] = amp * (1 - 4 * Math.abs(t - 0.5)); t += dt; if (t >= 1) t -= 1; } break;
        case 4: for (let s = a; s < b; s++) out[s] = amp * (Math.random() * 2 - 1); break;
        default: for (let s = a; s < b; s++) { out[s] = amp * Math.sin(TWO_PI * t); t += dt; if (t >= 1) t -= 1; }
      }
      this.ph = t;
    }
  }
  class SignalGenerator extends Oscillator {
    constructor(s, e) { super(s, e); this.kA = this.ciIdx('amplitude'); }
    ctl() { super.ctl(); this.amp = clamp(this.ci[this.kA], 0, 1); if (this.shape > 4) this.shape = 4; }
  }
  class Noise extends El {
    constructor(s, e) { super(s, e); this.kC = this.ciIdx('colour'); this.o = this.aoIdx('out'); this.c = 0; this.b = new Float64Array(7); }
    ctl() { this.c = clamp(this.ci[this.kC], 0, 1); }
    run(a, b) {
      const out = this.ao[this.o], c = this.c;
      if (c <= 0) { for (let s = a; s < b; s++) out[s] = Math.random() * 2 - 1; return; }
      const f = this.b;
      for (let s = a; s < b; s++) {
        const w = Math.random() * 2 - 1;
        f[0] = 0.99886 * f[0] + w * 0.0555179; f[1] = 0.99332 * f[1] + w * 0.0750759; f[2] = 0.96900 * f[2] + w * 0.1538520;
        f[3] = 0.86650 * f[3] + w * 0.3104856; f[4] = 0.55000 * f[4] + w * 0.5329522; f[5] = -0.7616 * f[5] - w * 0.0168980;
        const p = (f[0] + f[1] + f[2] + f[3] + f[4] + f[5] + f[6] + w * 0.5362) * 0.11;
        f[6] = w * 0.115926;
        out[s] = w * (1 - c) + p * c;
      }
    }
  }
  class TwinTBridge extends El {
    constructor(s, e) {
      super(s, e); this.kF = this.ciIdx('frequency'); this.kD = this.ciIdx('decay'); this.kT = this.ciIdx('trigger'); this.kV = this.ciIdx('velocity'); this.o = this.aoIdx('out');
      this.y1 = 0; this.y2 = 0; this.a1 = 0; this.a2 = 0; this.exc = 0; this.prevT = 0;
    }
    ctl() {
      const f = clamp(this.ci[this.kF], 10, this.sr * 0.45), d = Math.max(1, this.ci[this.kD]) / 1000;
      const r = Math.exp(-6.91 / (d * this.sr)), w = TWO_PI * f / this.sr;
      this.a1 = 2 * r * Math.cos(w); this.a2 = -r * r;
      const t = this.ci[this.kT];
      let fire;
      if (t < 0) fire = this.eng.host.trig > 0;
      else { fire = t > 0 && this.prevT <= 0; this.prevT = t; }
      if (fire) { const v = this.ci[this.kV]; this.exc = (v < 0 ? this.eng.host.vel : clamp(v, 0, 1)) * Math.sin(w); }
    }
    run(a, b) {
      const out = this.ao[this.o], a1 = this.a1, a2 = this.a2;
      let y1 = this.y1, y2 = this.y2, exc = this.exc;
      for (let s = a; s < b; s++) { const y = a1 * y1 + a2 * y2 + exc; exc = 0; y2 = y1; y1 = y; out[s] = y; }
      this.y1 = y1; this.y2 = y2; this.exc = 0;
    }
  }
  class NoteGate extends El {
    constructor(s, e) { super(s, e); this.kN = this.ciIdx('note'); this.oG = this.coIdx('gate'); this.oV = this.coIdx('velocity'); this.gate = 0; this.vel = 0; e.noteGates.push(this); }
    get note() { return Math.round(this.ci[this.kN]); }
    noteOn(n, v) { if (n === this.note) { this.gate = 1; this.vel = v; } }
    noteOff(n) { if (n === this.note) this.gate = 0; }
    ctl() { this.co[this.oG] = this.gate; this.co[this.oV] = this.gate ? this.vel : 0; }
  }
  class LFO extends El {
    constructor(s, e) { super(s, e); this.kR = this.ciIdx('rate'); this.kS = this.ciIdx('shape'); this.o = this.coIdx('out'); this.ph = 0; this.sh = 0; }
    ctl() {
      const dt = clamp(this.ci[this.kR], 0, 1000) * CTRL / this.sr, shape = Math.round(this.ci[this.kS]) | 0;
      let t = this.ph, v;
      switch (shape) {
        case 1: v = 1 - 4 * Math.abs(t - 0.5); break;
        case 2: v = 2 * t - 1; break;
        case 3: v = t < 0.5 ? 1 : -1; break;
        case 4: v = this.sh; break;
        default: v = Math.sin(TWO_PI * t);
      }
      t += dt; if (t >= 1) { t -= 1; this.sh = Math.random() * 2 - 1; }
      this.ph = t; this.co[this.o] = v;
    }
  }
  class MidiPitch extends El { constructor(s, e) { super(s, e); this.o = this.coIdx('out'); } ctl() { this.co[this.o] = this.eng.host.freq; } }
  class MidiVelocity extends El { constructor(s, e) { super(s, e); this.o = this.coIdx('out'); } ctl() { this.co[this.o] = this.eng.host.vel; } }
  class MidiInterval extends El {
    constructor(s, e) { super(s, e); this.kR = this.ciIdx('root'); this.oS = this.coIdx('semitones'); this.oR = this.coIdx('ratio'); }
    ctl() { const st = this.eng.host.note - this.ci[this.kR]; this.co[this.oS] = st; this.co[this.oR] = Math.pow(2, st / 12); }
  }
  class Transport extends El {
    constructor(s, e) { super(s, e); this.kD = this.ciIdx('division'); this.oPh = this.coIdx('phase'); this.oT = this.coIdx('trigger'); this.oR = this.coIdx('rate'); this.oTe = this.coIdx('tempo'); this.oP = this.coIdx('playing'); this.prev = 0; }
    ctl() {
      const h = this.eng.host, div = Math.max(1 / 64, this.ci[this.kD]);
      const ph = (h.ppq / div) % 1;
      this.co[this.oPh] = ph; this.co[this.oT] = ph < this.prev ? 1 : 0; this.prev = ph;
      this.co[this.oR] = h.tempo / 60 / div; this.co[this.oTe] = h.tempo; this.co[this.oP] = h.playing;
    }
  }
  class Input extends El {
    constructor(s, e) { super(s, e); this.o = this.aoIdx('out'); this.ao[this.o] = e.inBuf; }
  }
  class SampleLoad extends El {
    constructor(s, e) {
      super(s, e); this.kSp = this.ciIdx('speed'); this.kSt = this.ciIdx('start'); this.kL = this.ciIdx('loop'); this.kT = this.ciIdx('trigger'); this.o = this.aoIdx('out');
      this.buf = null; this.rate = 1; this.pos = 0; this.playing = false; this.prevT = 0; this.speed = 1; this.loop = 1; this.start = 0;
      e.samplers.push(this);
    }
    setSample(buf, sr) { this.buf = buf; this.rate = sr / this.sr; this.pos = this.start * buf.length; this.playing = this.loop > 0; }
    ctl() {
      this.speed = this.ci[this.kSp]; this.loop = this.ci[this.kL]; this.start = clamp(this.ci[this.kSt], 0, 1);
      const t = this.ci[this.kT];
      const fire = t < 0 ? this.eng.host.trig > 0 : (t > 0 && this.prevT <= 0);
      if (t >= 0) this.prevT = t;
      if (fire && this.buf) { this.pos = this.start * this.buf.length; this.playing = true; }
      if (this.loop > 0 && this.buf && !this.playing) this.playing = true;
    }
    run(a, b) {
      const out = this.ao[this.o], buf = this.buf;
      if (!buf || !this.playing) { for (let s = a; s < b; s++) out[s] = 0; return; }
      const n = buf.length, step = this.speed * this.rate, loop = this.loop > 0;
      let p = this.pos;
      for (let s = a; s < b; s++) {
        const i = p | 0, f = p - i, x0 = buf[i], x1 = buf[(i + 1) % n];
        out[s] = x0 + (x1 - x0) * f;
        p += step;
        if (p >= n || p < 0) { if (loop) { p = ((p % n) + n) % n; } else { this.playing = false; p = 0; for (let k = s + 1; k < b; k++) out[k] = 0; break; } }
      }
      this.pos = p;
    }
  }

  // ------------------------------------------------------------------
  // Control elements (block rate only)
  // ------------------------------------------------------------------
  class Envelope extends El {
    constructor(s, e) {
      super(s, e); this.kA = this.ciIdx('attack'); this.kD = this.ciIdx('decay'); this.kS = this.ciIdx('sustain'); this.kR = this.ciIdx('release'); this.kG = this.ciIdx('gate'); this.o = this.coIdx('out');
      this.level = 0; this.stage = 0; this.on = false; this.amp = 1; this.blockMs = 1000 * CTRL / this.sr; this.retrig = false;
    }
    ctl() {
      const g = this.ci[this.kG];
      let on, amp;
      if (g < 0) { on = this.eng.host.gate > 0; amp = this.eng.host.vel; if (this.eng.host.trig && on) this.retrig = true; }
      else { on = g > 0; amp = clamp(g, 0, 1); }
      if (on && (!this.on || this.retrig)) { this.stage = 1; this.amp = amp > 0 ? amp : 1; }
      if (!on && this.on) this.stage = 4;
      this.retrig = false;
      this.on = on;
      const a = Math.max(0.05, this.ci[this.kA]), d = Math.max(0.05, this.ci[this.kD]), su = clamp(this.ci[this.kS], 0, 1), r = Math.max(0.05, this.ci[this.kR]);
      const bm = this.blockMs;
      switch (this.stage) {
        case 1: this.level += bm / a; if (this.level >= 1) { this.level = 1; this.stage = 2; } break;
        case 2: { const k = Math.exp(-6.9 * bm / d); this.level = su + (this.level - su) * k; if (this.level - su < 0.001) { this.level = su; this.stage = 3; } break; }
        case 3: this.level = su; break;
        case 4: { const k = Math.exp(-6.9 * bm / r); this.level *= k; if (this.level < 0.0005) { this.level = 0; this.stage = 0; } break; }
        default: this.level = 0;
      }
      this.co[this.o] = this.level * this.amp;
    }
  }
  class Scale extends El {
    constructor(s, e) { super(s, e); this.kI = this.ciIdx('in'); this.kMin = this.ciIdx('min'); this.kMax = this.ciIdx('max'); this.o = this.coIdx('out'); }
    ctl() { const mn = this.ci[this.kMin], mx = this.ci[this.kMax]; this.co[this.o] = mn + clamp(this.ci[this.kI], 0, 1) * (mx - mn); }
  }
  class Choke extends El {
    constructor(s, e) { super(s, e); this.kG = this.ciIdx('gate'); this.kC = this.ciIdx('choke'); this.o = this.coIdx('out'); this.pg = 0; this.pc = 0; this.choked = false; }
    ctl() {
      const g = this.ci[this.kG], c = this.ci[this.kC];
      if (g > 0 && this.pg <= 0) this.choked = false;
      if (c > 0 && this.pc <= 0) this.choked = true;
      this.pg = g; this.pc = c;
      this.co[this.o] = this.choked ? 0 : g;
    }
  }
  class Select extends El {
    constructor(s, e) { super(s, e); this.kA = this.ciIdx('a'); this.kB = this.ciIdx('b'); this.kS = this.ciIdx('select'); this.o = this.coIdx('out'); this.oT = this.coIdx('thru'); }
    ctl() { const on = this.ci[this.kS] > 0.5; this.co[this.o] = on ? this.ci[this.kB] : this.ci[this.kA]; this.co[this.oT] = on ? 1 : 0; }
  }
  class ControlMultiply extends El {
    constructor(s, e) { super(s, e); this.kA = this.ciIdx('a'); this.kB = this.ciIdx('b'); this.o = this.coIdx('out'); }
    ctl() { this.co[this.o] = this.ci[this.kA] * this.ci[this.kB]; }
  }
  class EnvelopeFollower extends El {
    constructor(s, e) { super(s, e); this.kA = this.ciIdx('attack'); this.kR = this.ciIdx('release'); this.kM = this.ciIdx('mode'); this.i = this.aiIdx('in'); this.o = this.coIdx('out'); this.env = 0; this.aA = 0.1; this.aR = 0.001; this.rms = false; }
    ctl() { this.aA = onepoleCoef(this.ci[this.kA], this.sr); this.aR = onepoleCoef(this.ci[this.kR], this.sr); this.rms = this.ci[this.kM] > 0.5; this.co[this.o] = this.rms ? Math.sqrt(this.env) : this.env; }
    run(a, b) {
      const x = this.ai[this.i], aA = this.aA, aR = this.aR, rms = this.rms;
      let env = this.env;
      for (let s = a; s < b; s++) { const d = rms ? x[s] * x[s] : Math.abs(x[s]); env += (d > env ? aA : aR) * (d - env); }
      this.env = env;
    }
  }

  // ------------------------------------------------------------------
  // Gain structure and routing
  // ------------------------------------------------------------------
  class Gain extends El {
    constructor(s, e) { super(s, e); this.kG = this.ciIdx('gain'); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.g = 1; }
    ctl() { this.g = db2lin(this.ci[this.kG]); }
    run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], g = this.g; for (let s = a; s < b; s++) y[s] = x[s] * g; }
  }
  class VCA extends El {
    constructor(s, e) { super(s, e); this.kC = this.ciIdx('cv'); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.g = 1; this.gt = 1; }
    ctl() { this.gt = Math.max(0, this.ci[this.kC]); }
    run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], gt = this.gt; let g = this.g; for (let s = a; s < b; s++) { g += (gt - g) * 0.08; y[s] = x[s] * g; } this.g = g; }
  }
  class Mixer extends El {
    constructor(s, e) { super(s, e); this.iI = this.aiIdx('in'); this.iL = this.aiIdx('left'); this.iR = this.aiIdx('right'); this.oO = this.aoIdx('out'); this.oL = this.aoIdx('left'); this.oR = this.aoIdx('right'); }
    run(a, b) {
      const i = this.ai[this.iI], l = this.ai[this.iL], r = this.ai[this.iR], oo = this.ao[this.oO], ol = this.ao[this.oL], or = this.ao[this.oR];
      for (let s = a; s < b; s++) { const m = i[s]; oo[s] = m + 0.5 * (l[s] + r[s]); ol[s] = m + l[s]; or[s] = m + r[s]; }
    }
  }
  class Pan extends El {
    constructor(s, e) { super(s, e); this.kP = this.ciIdx('pan'); this.i = this.aiIdx('in'); this.oO = this.aoIdx('out'); this.oL = this.aoIdx('left'); this.oR = this.aoIdx('right'); this.gl = 0.707; this.gr = 0.707; }
    ctl() { const th = (clamp(this.ci[this.kP], -1, 1) + 1) * Math.PI / 4; this.gl = Math.cos(th); this.gr = Math.sin(th); }
    run(a, b) { const x = this.ai[this.i], oo = this.ao[this.oO], ol = this.ao[this.oL], or = this.ao[this.oR], gl = this.gl, gr = this.gr; for (let s = a; s < b; s++) { const v = x[s]; oo[s] = v; ol[s] = v * gl; or[s] = v * gr; } }
  }
  class DryWet extends El {
    constructor(s, e) { super(s, e); this.kM = this.ciIdx('mix'); this.iD = this.aiIdx('dry'); this.iW = this.aiIdx('wet'); this.o = this.aoIdx('out'); this.m = 1; }
    ctl() { this.m = clamp(this.ci[this.kM], 0, 1); }
    run(a, b) { const d = this.ai[this.iD], w = this.ai[this.iW], y = this.ao[this.o], m = this.m; for (let s = a; s < b; s++) y[s] = d[s] * (1 - m) + w[s] * m; }
  }
  class Output extends El {
    constructor(s, e) { super(s, e); this.iI = this.aiIdx('in'); this.iL = this.aiIdx('left'); this.iR = this.aiIdx('right'); this.l = new Float64Array(CTRL); this.r = new Float64Array(CTRL); e.outputs.push(this); }
    run(a, b) { const i = this.ai[this.iI], l = this.ai[this.iL], r = this.ai[this.iR], ol = this.l, or = this.r, m = this.ao[0]; for (let s = a; s < b; s++) { ol[s] = i[s] + l[s]; or[s] = i[s] + r[s]; m[s] = 0.5 * (ol[s] + or[s]); } }
  }
  class UnitDelay extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); }
    // Runs before the element that feeds it, so in[s-1] is the previous sample
    // and in[CTRL-1] at s = 0 is still the previous block's last sample.
    run(a, b) { const x = this.ai[this.i], y = this.ao[this.o]; for (let s = a; s < b; s++) y[s] = x[s === 0 ? CTRL - 1 : s - 1]; }
  }
  class Bypass extends El {
    run(a, b) { const x = this.ai[0], y = this.ao[0]; for (let s = a; s < b; s++) y[s] = x[s]; }
  }

  // ------------------------------------------------------------------
  // Filters and resonators
  // ------------------------------------------------------------------
  class OnePole extends El {
    constructor(s, e) { super(s, e); this.kC = this.ciIdx('cutoff'); this.kM = this.ciIdx('mode'); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.a = 0.1; this.lp = 0; this.mode = 0; this.c = 0; this.x1 = 0; this.y1 = 0; }
    ctl() { const fc = clamp(this.ci[this.kC], 1, this.sr * 0.49); this.a = 1 - Math.exp(-TWO_PI * fc / this.sr); this.mode = Math.round(this.ci[this.kM]) | 0; const tn = Math.tan(Math.PI * fc / this.sr); this.c = (tn - 1) / (tn + 1); }
    run(a, b) {
      const x = this.ai[this.i], y = this.ao[this.o], k = this.a, mode = this.mode;
      let lp = this.lp;
      if (mode === 2) { const c = this.c; let x1 = this.x1, y1 = this.y1; for (let s = a; s < b; s++) { const v = c * x[s] + x1 - c * y1; x1 = x[s]; y1 = v; y[s] = v; } this.x1 = x1; this.y1 = y1; return; }
      if (mode === 1) for (let s = a; s < b; s++) { lp += k * (x[s] - lp); y[s] = x[s] - lp; }
      else for (let s = a; s < b; s++) { lp += k * (x[s] - lp); y[s] = lp; }
      this.lp = lp;
    }
  }
  class StateVariable extends El {
    constructor(s, e) { super(s, e); this.kC = this.ciIdx('cutoff'); this.kR = this.ciIdx('resonance'); this.i = this.aiIdx('in'); this.oL = this.aoIdx('lp'); this.oB = this.aoIdx('bp'); this.oH = this.aoIdx('hp'); this.ic1 = 0; this.ic2 = 0; this.k = 1.4; this.a1 = 0; this.a2 = 0; this.a3 = 0; }
    ctl() {
      const fc = clamp(this.ci[this.kC], 5, this.sr * 0.45), q = Math.max(0.05, this.ci[this.kR]);
      const g = Math.tan(Math.PI * fc / this.sr), k = 1 / q;
      this.k = k; this.a1 = 1 / (1 + g * (g + k)); this.a2 = g * this.a1; this.a3 = g * this.a2;
    }
    run(a, b) {
      const x = this.ai[this.i], lp = this.ao[this.oL], bp = this.ao[this.oB], hp = this.ao[this.oH], a1 = this.a1, a2 = this.a2, a3 = this.a3, k = this.k;
      let ic1 = this.ic1, ic2 = this.ic2;
      for (let s = a; s < b; s++) {
        const v0 = x[s], v3 = v0 - ic2, v1 = a1 * ic1 + a2 * v3, v2 = ic2 + a2 * ic1 + a3 * v3;
        ic1 = 2 * v1 - ic1; ic2 = 2 * v2 - ic2;
        lp[s] = v2; bp[s] = v1; hp[s] = v0 - k * v1 - v2;
      }
      this.ic1 = ic1; this.ic2 = ic2;
    }
  }
  class Ladder extends El {
    constructor(s, e) { super(s, e); this.kC = this.ciIdx('cutoff'); this.kR = this.ciIdx('resonance'); this.kD = this.ciIdx('drive'); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.g = 0.1; this.k = 0; this.d = 1; this.s0 = 0; this.s1 = 0; this.s2 = 0; this.s3 = 0; }
    ctl() { const fc = clamp(this.ci[this.kC], 10, this.sr * 0.45); this.g = 1 - Math.exp(-TWO_PI * fc / this.sr); this.k = 4 * clamp(this.ci[this.kR], 0, 1.05); this.d = Math.max(0.01, this.ci[this.kD]); }
    run(a, b) {
      const x = this.ai[this.i], y = this.ao[this.o], g = this.g, k = this.k, d = this.d;
      let s0 = this.s0, s1 = this.s1, s2 = this.s2, s3 = this.s3;
      for (let s = a; s < b; s++) {
        const u = Math.tanh(x[s] * d - k * s3);
        s0 += g * (u - Math.tanh(s0)); s1 += g * (Math.tanh(s0) - Math.tanh(s1)); s2 += g * (Math.tanh(s1) - Math.tanh(s2)); s3 += g * (Math.tanh(s2) - Math.tanh(s3));
        y[s] = s3;
      }
      this.s0 = s0; this.s1 = s1; this.s2 = s2; this.s3 = s3;
    }
  }
  class Delay extends El {
    constructor(s, e) { super(s, e); this.kT = this.ciIdx('time'); this.kF = this.ciIdx('feedback'); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.n = Math.ceil(this.sr * 5) + 2; this.buf = new Float32Array(this.n); this.w = 0; this.d = 1; this.fb = 0; this.dt = 1; }
    ctl() { this.dt = clamp(this.ci[this.kT], 0, 5000) * this.sr / 1000; this.fb = clamp(this.ci[this.kF], 0, 0.99); }
    run(a, b) {
      const x = this.ai[this.i], y = this.ao[this.o], buf = this.buf, n = this.n, fb = this.fb, dt = this.dt;
      let w = this.w, d = this.d;
      for (let s = a; s < b; s++) {
        d += (dt - d) * 0.001;
        let r = w - d; if (r < 0) r += n;
        const i0 = r | 0, f = r - i0, v = buf[i0] * (1 - f) + buf[(i0 + 1) % n] * f;
        buf[w] = x[s] + v * fb; w = (w + 1) % n; y[s] = v;
      }
      this.w = w; this.d = d;
    }
  }
  class CombFilter extends El {
    constructor(s, e) { super(s, e); this.kF = this.ciIdx('frequency'); this.kB = this.ciIdx('feedback'); this.kD = this.ciIdx('damping'); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.n = Math.ceil(this.sr / 10) + 4; this.buf = new Float32Array(this.n); this.w = 0; this.len = 100; this.fb = 0.95; this.a = 0.9; this.lp = 0; }
    ctl() { this.len = clamp(this.sr / Math.max(10, this.ci[this.kF]), 2, this.n - 2); this.fb = clamp(this.ci[this.kB], 0, 0.999); this.a = 0.02 + 0.98 * (1 - clamp(this.ci[this.kD], 0, 1)); }
    disperse(v) { return v; }
    run(a, b) {
      const x = this.ai[this.i], y = this.ao[this.o], buf = this.buf, n = this.n, len = this.len, fb = this.fb, k = this.a;
      let w = this.w, lp = this.lp;
      for (let s = a; s < b; s++) {
        let r = w - len; if (r < 0) r += n;
        const i0 = r | 0, f = r - i0, v = buf[i0] * (1 - f) + buf[(i0 + 1) % n] * f;
        lp += k * (v - lp);
        buf[w] = x[s] + this.disperse(lp) * fb; w = (w + 1) % n; y[s] = v;
      }
      this.w = w; this.lp = lp;
    }
  }
  class StiffString extends CombFilter {
    constructor(s, e) { super(s, e); this.kDi = this.ciIdx('dispersion'); this.c = 0; this.x1 = new Float64Array(4); this.y1 = new Float64Array(4); }
    ctl() { super.ctl(); this.c = -0.6 * clamp(this.ci[this.kDi], 0, 1); }
    disperse(v) { const c = this.c, x1 = this.x1, y1 = this.y1; for (let k = 0; k < 4; k++) { const y = c * v + x1[k] - c * y1[k]; x1[k] = v; y1[k] = y; v = y; } return v; }
  }
  const MODAL = [
    [1, 2.756, 5.404, 8.933, 13.344, 18.648],
    [1, 1.593, 2.136, 2.296, 2.653, 2.917],
    [1, 1.414, 1.581, 2.0, 2.236, 2.550],
    [1, 1.414, 2.0, 2.236, 2.449, 2.828],
  ];
  class ModalBank extends El {
    constructor(s, e) { super(s, e); this.kF = this.ciIdx('frequency'); this.kD = this.ciIdx('decay'); this.kB = this.ciIdx('brightness'); this.kM = this.ciIdx('mode'); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.a1 = new Float64Array(6); this.a2 = new Float64Array(6); this.wgt = new Float64Array(6); this.y1 = new Float64Array(6); this.y2 = new Float64Array(6); }
    ctl() {
      const f = clamp(this.ci[this.kF], 20, 5000), d = Math.max(0.05, this.ci[this.kD]), br = clamp(this.ci[this.kB], 0, 1), ratios = MODAL[clamp(Math.round(this.ci[this.kM]), 0, 3) | 0];
      for (let k = 0; k < 6; k++) {
        const fk = Math.min(f * ratios[k], this.sr * 0.45), w = TWO_PI * fk / this.sr, r = Math.exp(-6.91 * (1 + 0.6 * k) / (d * this.sr));
        this.a1[k] = 2 * r * Math.cos(w); this.a2[k] = -r * r; this.wgt[k] = Math.pow(0.15 + 0.85 * br, k) * Math.sin(w);
      }
    }
    run(a, b) {
      const x = this.ai[this.i], out = this.ao[this.o], a1 = this.a1, a2 = this.a2, wgt = this.wgt, y1 = this.y1, y2 = this.y2;
      for (let s = a; s < b; s++) {
        const v = x[s]; let acc = 0;
        for (let k = 0; k < 6; k++) { const y = a1[k] * y1[k] + a2[k] * y2[k] + v * wgt[k]; y2[k] = y1[k]; y1[k] = y; acc += y; }
        out[s] = acc * 0.5;
      }
    }
  }
  class Reed extends El {
    constructor(s, e) { super(s, e); this.kF = this.ciIdx('frequency'); this.kP = this.ciIdx('pressure'); this.kS = this.ciIdx('stiffness'); this.kD = this.ciIdx('damping'); this.o = this.aoIdx('out'); this.n = Math.ceil(this.sr / 20) + 4; this.buf = new Float32Array(this.n); this.w = 0; this.len = 100; this.p = 0.5; this.slope = -0.44; this.a = 0.7; this.lp = 0; this.dc = 0; }
    ctl() { this.len = clamp(this.sr / (2 * clamp(this.ci[this.kF], 20, 5000)) - 1.5, 2, this.n - 2); this.p = clamp(this.ci[this.kP], 0, 1); this.slope = -0.44 + 0.26 * clamp(this.ci[this.kS], 0, 1); this.a = 0.15 + 0.8 * (1 - clamp(this.ci[this.kD], 0, 1)); }
    run(a, b) {
      const out = this.ao[this.o], buf = this.buf, n = this.n, len = this.len, p = this.p, slope = this.slope, k = this.a;
      let w = this.w, lp = this.lp, dc = this.dc;
      for (let s = a; s < b; s++) {
        let r = w - len; if (r < 0) r += n;
        const i0 = r | 0, f = r - i0, y = buf[i0] * (1 - f) + buf[(i0 + 1) % n] * f;
        lp += k * (-0.95 * y - lp);
        const pd = lp - p, rg = clamp(0.7 + slope * pd, -1, 1);
        buf[w] = p + pd * rg; w = (w + 1) % n;
        dc += (y - dc) * 0.0005;
        out[s] = y - dc;
      }
      this.w = w; this.lp = lp; this.dc = dc;
    }
  }

  // ------------------------------------------------------------------
  // Modulation effects
  // ------------------------------------------------------------------
  class ModDelay extends El {
    constructor(s, e, base, voices) {
      super(s, e); this.kR = this.ciIdx('rate'); this.kD = this.ciIdx('depth'); this.kM = this.ciIdx('mix'); this.kF = this.ciIdx('feedback'); this.i = this.aiIdx('in'); this.o = this.aoIdx('out');
      this.baseS = base * this.sr / 1000; this.voices = voices; this.n = Math.ceil(this.sr * 0.06); this.buf = new Float32Array(this.n); this.w = 0; this.ph = 0; this.dph = 0; this.depth = 0; this.mix = 0.5; this.fb = 0;
    }
    ctl() { this.dph = clamp(this.ci[this.kR], 0, 50) / this.sr; this.depth = Math.max(0, this.ci[this.kD]) * this.sr / 1000; this.mix = clamp(this.ci[this.kM], 0, 1); this.fb = this.kF < this.spare ? clamp(this.ci[this.kF], -0.95, 0.95) : 0; }
    run(a, b) {
      const x = this.ai[this.i], y = this.ao[this.o], buf = this.buf, n = this.n, V = this.voices, base = this.baseS, depth = this.depth, mix = this.mix, fb = this.fb, dph = this.dph;
      let w = this.w, ph = this.ph;
      for (let s = a; s < b; s++) {
        let wet = 0;
        for (let v = 0; v < V; v++) {
          const dl = clamp(base + depth * Math.sin(TWO_PI * (ph + v / V)), 1, n - 2);
          let r = w - dl; if (r < 0) r += n;
          const i0 = r | 0, f = r - i0;
          wet += buf[i0] * (1 - f) + buf[(i0 + 1) % n] * f;
        }
        wet /= V;
        buf[w] = x[s] + wet * fb; w = (w + 1) % n;
        ph += dph; if (ph >= 1) ph -= 1;
        y[s] = x[s] * (1 - mix) + wet * mix;
      }
      this.w = w; this.ph = ph;
    }
  }
  class Chorus extends ModDelay { constructor(s, e) { super(s, e, 15, 3); } }
  class Flanger extends ModDelay { constructor(s, e) { super(s, e, 5, 1); } }
  class Phaser extends El {
    constructor(s, e) { super(s, e); this.kR = this.ciIdx('rate'); this.kD = this.ciIdx('depth'); this.kM = this.ciIdx('mix'); this.kF = this.ciIdx('feedback'); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.ph = 0; this.dph = 0; this.depth = 0.7; this.mix = 0.5; this.fb = 0.5; this.x1 = new Float64Array(4); this.y1 = new Float64Array(4); this.last = 0; this.c = 0; }
    ctl() {
      this.dph = clamp(this.ci[this.kR], 0, 50) * CTRL / this.sr; this.depth = clamp(this.ci[this.kD], 0, 1); this.mix = clamp(this.ci[this.kM], 0, 1); this.fb = clamp(this.ci[this.kF], 0, 0.95);
      const f = 100 + this.depth * 1900 * (0.5 + 0.5 * Math.sin(TWO_PI * this.ph)), t = Math.tan(Math.PI * Math.min(f, this.sr * 0.45) / this.sr);
      this.c = (t - 1) / (t + 1); this.ph += this.dph; if (this.ph >= 1) this.ph -= 1;
    }
    run(a, b) {
      const x = this.ai[this.i], y = this.ao[this.o], c = this.c, x1 = this.x1, y1 = this.y1, mix = this.mix, fb = this.fb;
      let last = this.last;
      for (let s = a; s < b; s++) {
        let v = x[s] + last * fb;
        for (let k = 0; k < 4; k++) { const u = c * v + x1[k] - c * y1[k]; x1[k] = v; y1[k] = u; v = u; }
        last = v; y[s] = x[s] * (1 - mix) + v * mix;
      }
      this.last = last;
    }
  }

  // ------------------------------------------------------------------
  // Transfer functions and nonlinear stages
  // ------------------------------------------------------------------
  class Shaper extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.kG = this.ciIdx('gain'); this.g = 1; }
    ctl() { this.g = this.kG < this.spare ? this.ci[this.kG] : 1; }
  }
  class Tanh extends Shaper { run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], g = this.g; for (let s = a; s < b; s++) y[s] = Math.tanh(g * x[s]); } }
  class SoftSine extends Shaper { run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], g = this.g; for (let s = a; s < b; s++) { const v = g * x[s]; y[s] = v / (Math.abs(v) + 1); } } }
  class SinArcTan extends Shaper { run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], g = this.g; for (let s = a; s < b; s++) { const v = g * x[s]; y[s] = v / Math.sqrt(v * v + 1); } } }
  class Fold extends Shaper { run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], g = this.g; for (let s = a; s < b; s++) { let v = (g * x[s] + 1) % 4; if (v < 0) v += 4; y[s] = v < 2 ? v - 1 : 3 - v; } } }
  class HardClip extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.kT = this.ciIdx('threshold'); this.t = 1; }
    ctl() { this.t = Math.max(0.01, this.ci[this.kT]); }
    run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], t = this.t; for (let s = a; s < b; s++) y[s] = clamp(x[s], -t, t); }
  }
  class AsymClip extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.kD = this.ciIdx('drive'); this.kP = this.ciIdx('posVf'); this.kN = this.ciIdx('negVf'); this.d = 1; this.p = 0.3; this.nv = 0.6; }
    ctl() { this.d = this.ci[this.kD]; this.p = Math.max(0.01, this.ci[this.kP]); this.nv = Math.max(0.01, this.ci[this.kN]); }
    run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], d = this.d, p = this.p, nv = this.nv; for (let s = a; s < b; s++) { const v = x[s] * d; y[s] = v >= 0 ? p * Math.tanh(v / p) : nv * Math.tanh(v / nv); } }
  }
  class Diode extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.kIs = this.ciIdx('saturationCurrent'); this.kN = this.ciIdx('emissionCoefficient'); this.kVt = this.ciIdx('thermalVoltage'); this.nvt = 0.045; this.is = 2.52e-9; }
    ctl() { this.nvt = Math.max(0.005, this.ci[this.kN] * (this.kVt < this.spare ? this.ci[this.kVt] : 0.02585)); this.is = Math.max(1e-15, this.ci[this.kIs]); }
    run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], nvt = this.nvt, k = 1 / (1000 * this.is); for (let s = a; s < b; s++) { const v = x[s]; y[s] = v > 0 ? nvt * Math.log(1 + v * k) : v; } }
  }
  class DiodePair extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.kIs = this.ciIdx('saturationCurrent'); this.kN = this.ciIdx('emissionCoefficient'); this.kR = this.ciIdx('seriesResistance'); this.nvt = 0.045; this.is = 2.52e-9; this.r = 1000; }
    ctl() { this.nvt = Math.max(0.005, this.ci[this.kN] * 0.02585); this.is = Math.max(1e-15, this.ci[this.kIs]); this.r = Math.max(1, this.ci[this.kR]); }
    run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], nvt = this.nvt, k = 1 / (this.r * 2 * this.is); for (let s = a; s < b; s++) y[s] = nvt * Math.asinh(x[s] * k); }
  }
  class Triode extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.kMu = this.ciIdx('mu'); this.kB = this.ciIdx('bias'); this.mu = 1; this.bias = -0.45; this.rest = 0; }
    static f(v) { return v > 0 ? v / (1 + 2 * v) : Math.tanh(v); }
    ctl() { this.mu = Math.max(1, this.ci[this.kMu]) / 100; this.bias = this.ci[this.kB] * 0.3; this.rest = Triode.f(this.bias); }
    run(a, b) { const x = this.ai[this.i], y = this.ao[this.o], mu = this.mu, bias = this.bias, rest = this.rest; for (let s = a; s < b; s++) y[s] = -(Triode.f(x[s] * mu + bias) - rest); }
  }

  // ------------------------------------------------------------------
  // Dynamics
  // ------------------------------------------------------------------
  class Compressor extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.kT = this.ciIdx('threshold'); this.kR = this.ciIdx('ratio'); this.kK = this.ciIdx('knee'); this.kA = this.ciIdx('attack'); this.kRel = this.ciIdx('release'); this.kU = this.ciIdx('upward'); this.gr = 0; this.env = 0; this.aA = 0.01; this.aR = 0.001; this.T = -6; this.R = 4; this.W = 6; this.up = 0; }
    ctl() { this.T = this.ci[this.kT]; this.R = Math.max(1, this.ci[this.kR]); this.W = Math.max(0, this.ci[this.kK]); this.up = clamp(this.ci[this.kU], 0, 1); this.aA = onepoleCoef(this.ci[this.kA], this.sr); this.aR = onepoleCoef(this.ci[this.kRel], this.sr); }
    run(a, b) {
      const x = this.ai[this.i], y = this.ao[this.o], T = this.T, W = this.W, R = this.R, up = this.up, aA = this.aA, aR = this.aR;
      let env = this.env, gr = this.gr;
      for (let s = a; s < b; s++) {
        const v = x[s], ax = Math.abs(v);
        env += (ax > env ? aA : aR) * (ax - env);
        const xdb = lin2db(env);
        let ydb;
        if (2 * (xdb - T) < -W) ydb = xdb;
        else if (2 * Math.abs(xdb - T) <= W) ydb = xdb + (1 / R - 1) * Math.pow(xdb - T + W / 2, 2) / (2 * Math.max(0.001, W));
        else ydb = T + (xdb - T) / R;
        let g = ydb - xdb;
        if (up > 0 && xdb < T - W) g += up * Math.min(24, (T - W - xdb) * (1 - 1 / R));
        gr += (g - gr) * 0.2;
        y[s] = v * db2lin(gr);
      }
      this.env = env; this.gr = gr;
    }
  }
  class Expander extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.kA = this.ciIdx('amount'); this.kT = this.ciIdx('threshold'); this.kR = this.ciIdx('ratio'); this.env = 0; this.gr = 0; this.det = 0; this.ext = false; this.T = -60; this.R = 2; }
    ctl() { this.ext = this.driven[this.kA] > 0; this.det = clamp(this.ci[this.kA], 0, 1); this.T = this.ci[this.kT]; this.R = Math.max(1, this.ci[this.kR]); }
    run(a, b) {
      const x = this.ai[this.i], y = this.ao[this.o], T = this.T, R = this.R, ext = this.ext, det = this.det;
      let env = this.env, gr = this.gr;
      for (let s = a; s < b; s++) {
        const v = x[s];
        let lvl;
        if (ext) lvl = det; else { const ax = Math.abs(v); env += (ax > env ? 0.01 : 0.0005) * (ax - env); lvl = env; }
        const ldb = lin2db(lvl), g = ldb < T ? Math.max(-80, (ldb - T) * (R - 1)) : 0;
        gr += (g - gr) * 0.05;
        y[s] = v * db2lin(gr);
      }
      this.env = env; this.gr = gr;
    }
  }

  // ------------------------------------------------------------------
  // Meters (pass audio through, report on control outputs)
  // ------------------------------------------------------------------
  class Oscilloscope extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.oP = this.coIdx('peak'); this.oR = this.coIdx('rms'); this.oF = this.coIdx('frequency'); this.pk = 0; this.sq = 0; this.n = 0; this.zc = 0; this.prev = 0; this.win = Math.round(this.sr / 20); e.scopes.push(this); }
    run(a, b) {
      const x = this.ai[this.i], y = this.ao[this.o];
      let pk = this.pk, sq = this.sq, zc = this.zc, prev = this.prev;
      for (let s = a; s < b; s++) { const v = x[s], av = v < 0 ? -v : v; y[s] = v; if (av > pk) pk = av; sq += v * v; if (prev <= 0 && v > 0) zc++; prev = v; }
      this.n += b - a; this.pk = pk; this.sq = sq; this.zc = zc; this.prev = prev;
      if (this.n >= this.win) { this.co[this.oP] = pk; this.co[this.oR] = Math.sqrt(sq / this.n); this.co[this.oF] = pk > 0.001 ? zc * this.sr / this.n : 0; this.pk = 0; this.sq = 0; this.n = 0; this.zc = 0; }
    }
  }
  class FreqAnalyzer extends El {
    constructor(s, e) { super(s, e); this.i = this.aiIdx('in'); this.o = this.aoIdx('out'); this.oL = this.coIdx('low'); this.oM = this.coIdx('mid'); this.oH = this.coIdx('high'); this.oC = this.coIdx('centroid'); this.lp1 = 0; this.lp2 = 0; this.eL = 0; this.eM = 0; this.eH = 0; this.a1 = 1 - Math.exp(-TWO_PI * 250 / this.sr); this.a2 = 1 - Math.exp(-TWO_PI * 2500 / this.sr); e.scopes.push(this); }
    run(a, b) {
      const x = this.ai[this.i], y = this.ao[this.o], a1 = this.a1, a2 = this.a2;
      let lp1 = this.lp1, lp2 = this.lp2, eL = this.eL, eM = this.eM, eH = this.eH;
      for (let s = a; s < b; s++) {
        const v = x[s]; y[s] = v; lp1 += a1 * (v - lp1); lp2 += a2 * (v - lp2);
        const lo = lp1, mid = lp2 - lp1, hi = v - lp2;
        eL += (lo * lo - eL) * 0.002; eM += (mid * mid - eM) * 0.002; eH += (hi * hi - eH) * 0.002;
      }
      this.lp1 = lp1; this.lp2 = lp2; this.eL = eL; this.eM = eM; this.eH = eH;
    }
    ctl() { const l = Math.sqrt(this.eL), m = Math.sqrt(this.eM), h = Math.sqrt(this.eH), t = l + m + h; this.co[this.oL] = l; this.co[this.oM] = m; this.co[this.oH] = h; this.co[this.oC] = t > 1e-6 ? (l * 120 + m * 900 + h * 5000) / t : 0; }
  }

  // ------------------------------------------------------------------
  // Granular
  // ------------------------------------------------------------------
  class Granulator extends El {
    constructor(s, e) {
      super(s, e);
      this.i = this.aiIdx('in'); this.oO = this.aoIdx('out'); this.oL = this.aoIdx('left'); this.oR = this.aoIdx('right');
      const K = (k) => this.ciIdx(k);
      this.k = { position: K('position'), size: K('size'), density: K('density'), pitch: K('pitch'), spray: K('spray'), jitter: K('jitter'), pitchJitter: K('pitchJitter'), shape: K('shape'), spread: K('spread'), reverse: K('reverse'), scan: K('scan'), freeze: K('freeze'), trigger: K('trigger') };
      const secs = clamp(Number(s.props && s.props.seconds) || 8, 0.5, 60);
      this.n = Math.ceil(secs * this.sr); this.buf = new Float32Array(this.n); this.w = 0; this.fileLen = 0;
      this.grains = []; for (let g = 0; g < 64; g++) this.grains.push({ on: false, pos: 0, len: 1, ph: 0, rate: 1, gl: 1, gr: 1, rev: false });
      this.countdown = 0; this.prevT = 0; this.scanPos = 0; this.p = { record: true, free: true, size: 5000, density: 20, shape: 0.5, spray: 0, jitter: 0, pitch: 0, pitchJitter: 0, spread: 0.5, reverse: false, scan: 0, position: 0 };
      e.samplers.push(this);
    }
    setSample(data, sr) {
      const ratio = sr / this.sr, len = Math.min(this.n, Math.floor(data.length / ratio));
      for (let i = 0; i < len; i++) { const p = i * ratio, j = p | 0, f = p - j; this.buf[i] = data[j] * (1 - f) + (data[j + 1] || 0) * f; }
      this.fileLen = len; this.w = len % this.n;
    }
    ctl() {
      const c = this.ci, k = this.k, p = this.p;
      p.position = clamp(c[k.position], 0, 1); p.size = clamp(c[k.size], 1, 2000) * this.sr / 1000; p.density = clamp(c[k.density], 0.01, 200);
      p.pitch = c[k.pitch]; p.spray = clamp(c[k.spray], 0, 1); p.jitter = clamp(c[k.jitter], 0, 1); p.pitchJitter = Math.max(0, c[k.pitchJitter]);
      p.shape = clamp(c[k.shape], 0, 1); p.spread = clamp(c[k.spread], 0, 1); p.reverse = c[k.reverse] > 0.5; p.scan = c[k.scan];
      const fz = c[k.freeze]; p.record = fz < 0 ? !this.fileLen : fz < 0.5;
      const t = c[k.trigger];
      if (t < 0) p.free = true;
      else { p.free = false; if (t > 0 && this.prevT <= 0) this.spawn(); this.prevT = t; }
      this.scanPos += p.scan * (CTRL / this.sr) / Math.max(0.1, this.n / this.sr);
      if (this.scanPos > 1 || this.scanPos < 0) this.scanPos -= Math.floor(this.scanPos);
    }
    spawn() {
      const p = this.p; let g = null;
      for (let i = 0; i < 64; i++) if (!this.grains[i].on) { g = this.grains[i]; break; }
      if (!g) return;
      let rel = (p.position + this.scanPos + (Math.random() - 0.5) * p.spray) % 1; if (rel < 0) rel += 1;
      g.pos = this.fileLen ? rel * this.fileLen : (this.w - rel * this.n + this.n) % this.n;
      g.len = Math.max(8, p.size); g.ph = 0; g.on = true;
      g.rate = Math.pow(2, (p.pitch + (Math.random() - 0.5) * 2 * p.pitchJitter) / 12);
      g.rev = p.reverse;
      const pan = (Math.random() - 0.5) * p.spread; g.gl = Math.cos((pan + 0.5) * Math.PI / 2); g.gr = Math.sin((pan + 0.5) * Math.PI / 2);
    }
    run(a, b) {
      const p = this.p, n = this.n, buf = this.buf, x = this.ai[this.i], oo = this.ao[this.oO], ol = this.ao[this.oL], or = this.ao[this.oR], shape = p.shape, grains = this.grains;
      for (let s = a; s < b; s++) {
        if (p.record) { buf[this.w] = x[s]; this.w = (this.w + 1) % n; }
        if (p.free && --this.countdown <= 0) { this.spawn(); this.countdown = this.sr / p.density * (1 + (Math.random() - 0.5) * 2 * p.jitter); }
        let l = 0, r = 0;
        for (let gi = 0; gi < 64; gi++) {
          const g = grains[gi];
          if (!g.on) continue;
          const u = g.ph / g.len;
          if (u >= 1) { g.on = false; continue; }
          let env = 0.5 - 0.5 * Math.cos(TWO_PI * u);
          if (shape < 0.5) { const edge = 0.02 + 0.96 * shape; env = u < edge ? u / edge : u > 1 - edge ? (1 - u) / edge : 1; }
          else if (shape > 0.5) env = Math.pow(env, 1 + (shape - 0.5) * 4);
          const off = g.rev ? g.len - g.ph : g.ph;
          let pos = g.pos + off * g.rate; pos = ((pos % n) + n) % n;
          const i0 = pos | 0, f = pos - i0, v = (buf[i0] * (1 - f) + buf[(i0 + 1) % n] * f) * env;
          l += v * g.gl; r += v * g.gr;
          g.ph += 1;
        }
        ol[s] = l * 0.35; or[s] = r * 0.35; oo[s] = (l + r) * 0.175;
      }
    }
  }

  const REGISTRY = {
    Oscillator, SignalGenerator, Noise, TwinTBridge, NoteGate, LFO, MidiPitch, MidiVelocity, MidiInterval, Transport, Input, SampleLoad,
    Envelope, Scale, Choke, Select, ControlMultiply, EnvelopeFollower,
    Gain, VCA, Mixer, Pan, DryWet, Output, UnitDelay,
    OnePole, StateVariable, Ladder, Delay, CombFilter, StiffString, ModalBank, Reed,
    Chorus, Flanger, Phaser,
    Tanh, SoftSine, SinArcTan, Fold, HardClip, AsymClip, Diode, DiodePair, Triode,
    Compressor, Expander, Oscilloscope, FreqAnalyzer, Granulator,
  };

  // ------------------------------------------------------------------
  // Engine
  // ------------------------------------------------------------------
  class Engine {
    constructor(compiled, sr) {
      this.sr = sr; this.compiled = compiled;
      this.host = { gate: 0, note: 60, vel: 0, freq: 261.63, tempo: 120, playing: 0, ppq: 0, trig: 0 };
      this.held = []; this.noteGates = []; this.outputs = []; this.samplers = []; this.scopes = [];
      this.events = []; this.inBuf = new Float64Array(CTRL); this.time = 0; this.nan = 0; this.warnings = [];
      this.nodes = compiled.nodes.map((spec) => {
        if (spec.unknown) return new Bypass(spec, this);
        const C = REGISTRY[spec.impl] || REGISTRY[spec.type] || Bypass;
        return new C(spec, this);
      });
      // Audio wiring: one source → alias the buffer; several → summed each block.
      const fanin = new Map();
      for (const a of compiled.audioArcs) { const key = a.to + ':' + a.in; (fanin.get(key) || fanin.set(key, []).get(key)).push(a); }
      for (const [key, arcs] of fanin) {
        const d = this.nodes[arcs[0].to], port = arcs[0].in;
        if (arcs.length === 1) d.ai[port] = this.nodes[arcs[0].from].ao[arcs[0].out];
        else d.sum.push({ dst: d.ai[port], srcs: arcs.map((a) => this.nodes[a.from].ao[a.out]) });
      }
      for (const a of compiled.ctlArcs) { const d = this.nodes[a.to]; d.carcs.push({ ci: a.in, src: this.nodes[a.from], co: a.out, mode: a.mode, depth: a.depth == null ? 1 : a.depth, mult: a.mult, range: a.range }); d.driven[a.in] = 1; }
      this.order = compiled.order.map((i) => this.nodes[i]);
      this.stages = (compiled.stages || [{ nodes: compiled.order, sample: false }]).map((st) => ({ sample: st.sample, nodes: st.nodes.map((i) => this.nodes[i]).filter((nd) => nd.hasAudio) })).filter((st) => st.nodes.length);
      this.peaks = new Float32Array(this.nodes.length);
      for (const nd of this.order) { this.resolve(nd); nd.ctl(); }
    }
    resolve(nd) {
      const ci = nd.ci, base = nd.base;
      for (let i = 0; i < base.length; i++) ci[i] = base[i];
      const arcs = nd.carcs;
      for (let k = 0; k < arcs.length; k++) {
        const a = arcs[k], v = a.src.co[a.co];
        if (a.mode === 'replace') ci[a.ci] = v;
        else if (a.mult) ci[a.ci] = ci[a.ci] * (1 + a.depth * v);
        else ci[a.ci] += a.depth * v * a.range;
      }
    }
    setParam(nodeIdx, ciIdx, value) { const nd = this.nodes[nodeIdx]; if (nd && ciIdx < nd.base.length) nd.base[ciIdx] = value; }
    setSample(nodeIdx, data, sr) { const nd = this.nodes[nodeIdx]; if (nd && nd.setSample) nd.setSample(data, sr); }
    pushEvent(ev) { this.events.push(ev); if (this.events.length > 4096) this.events.shift(); }
    noteOn(n, v) {
      n = Math.round(n); v = clamp(v, 0, 1);
      this.held = this.held.filter((x) => x !== n); this.held.push(n);
      this.host.gate = 1; this.host.note = n; this.host.vel = v; this.host.freq = midiHz(n); this.host.trig = 1;
      for (const g of this.noteGates) g.noteOn(n, v);
    }
    noteOff(n) {
      n = Math.round(n);
      this.held = this.held.filter((x) => x !== n);
      if (this.held.length) { const m = this.held[this.held.length - 1]; this.host.note = m; this.host.freq = midiHz(m); }
      else this.host.gate = 0;
      for (const g of this.noteGates) g.noteOff(n);
    }
    allNotesOff() { this.held = []; this.host.gate = 0; for (const g of this.noteGates) g.gate = 0; }
    setTransport(t) { if (t.tempo != null) this.host.tempo = t.tempo; if (t.playing != null) this.host.playing = t.playing ? 1 : 0; if (t.ppq != null) this.host.ppq = t.ppq; }
    applyEvents(until) {
      const evs = this.events;
      if (!evs.length) return;
      const keep = [];
      for (let i = 0; i < evs.length; i++) {
        const e = evs[i];
        if (e.when != null && e.when > until) { keep.push(e); continue; }
        switch (e.type) {
          case 'note': if (e.on) this.noteOn(e.note, e.vel == null ? 1 : e.vel); else this.noteOff(e.note); break;
          case 'transport': this.setTransport(e); break;
          case 'param': this.setParam(e.node, e.ci, e.value); break;
          case 'panic': this.allNotesOff(); break;
          default: break;
        }
      }
      this.events = keep;
    }
    process(inL, inR, outL, outR, frames, now) {
      const order = this.order, N = order.length, stages = this.stages, sr = this.sr, outs = this.outputs, peaks = this.peaks, inBuf = this.inBuf;
      const blockSec = CTRL / sr;
      for (let i = 0; i < frames; i += CTRL) {
        const nb = Math.min(CTRL, frames - i);
        const t = (now != null ? now : this.time) + i / sr;
        this.applyEvents(t + blockSec);
        for (let k = 0; k < N; k++) { const nd = order[k]; this.resolve(nd); nd.ctl(); }
        this.host.trig = 0;
        this.host.ppq += this.host.tempo / 60 * nb / sr;
        if (inL) { if (inR) for (let s = 0; s < nb; s++) inBuf[s] = 0.5 * (inL[i + s] + inR[i + s]); else for (let s = 0; s < nb; s++) inBuf[s] = inL[i + s]; }
        for (let st = 0; st < stages.length; st++) {
          const stage = stages[st], nodes = stage.nodes, M = nodes.length;
          if (!stage.sample) {
            for (let k = 0; k < M; k++) { const nd = nodes[k]; if (nd.sum.length) this.gather(nd, 0, nb); nd.run(0, nb); }
          } else {
            for (let s = 0; s < nb; s++) for (let k = 0; k < M; k++) { const nd = nodes[k]; if (nd.sum.length) this.gather(nd, s, s + 1); nd.run(s, s + 1); }
          }
        }
        for (let s = 0; s < nb; s++) {
          let l = 0, r = 0;
          for (let o = 0; o < outs.length; o++) { l += outs[o].l[s]; r += outs[o].r[s]; }
          if (!(l === l) || !(r === r)) { l = 0; r = 0; this.nan++; }
          outL[i + s] = l; if (outR) outR[i + s] = r;
        }
        for (let k = 0; k < N; k++) {
          const nd = order[k];
          let v;
          if (nd.spec.ao.length) { const buf = nd.ao[0]; v = 0; for (let s = 0; s < nb; s += 4) { const x = buf[s] < 0 ? -buf[s] : buf[s]; if (x > v) v = x; } }
          else v = Math.abs(nd.co[0]);
          if (v > peaks[nd.idx]) peaks[nd.idx] = v;
        }
      }
      this.time += frames / sr;
      if (this.nan === 1) this.warnings.push('non-finite sample at output (reported once)');
    }
    gather(nd, a, b) {
      const sums = nd.sum;
      for (let j = 0; j < sums.length; j++) {
        const dst = sums[j].dst, srcs = sums[j].srcs, n = srcs.length;
        for (let s = a; s < b; s++) { let v = 0; for (let q = 0; q < n; q++) v += srcs[q][s]; dst[s] = v; }
      }
    }
    takePeaks() { const p = Float32Array.from(this.peaks); this.peaks.fill(0); return p; }
    readouts() { return this.scopes.map((s) => ({ idx: s.idx, co: Array.from(s.co).slice(0, s.spec.co.length) })); }
  }

export const IMPLEMENTED = Object.keys(REGISTRY);
export { Engine, CTRL, midiHz };
