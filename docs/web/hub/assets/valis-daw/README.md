# Vendored: the Valis DAW engine (owner's clean-room JavaScript)

Same-origin ES modules for hub post 55
(`docs/web/hub/55-valis-a-drum-machine-in-rdf.md`): the DAW that plays a
circuit described in RDF (see [`third_party/valis/`](../../../../third_party/valis/)
for the vocabulary and example circuits it reads). This is the owner's
clean-room JavaScript reimplementation of the
[Valis](https://github.com/danja/valis) synthesizer engine, built from
the Valis Turtle vocabulary and its documentation -- not a port of
upstream's AGPL-3.0 C++ (`src/`, `include/`). Licensed with this
repository, Apache-2.0. Derivation review, element by element against
the upstream C++:
[danbri/factoidal#687 (comment)](https://github.com/danbri/factoidal/issues/687#issuecomment-5701030083).

## Module map

| File | Runs on | What it does |
|---|---|---|
| `compiler.mjs` | main thread | `compile(model, ont, implemented)`: a parsed circuit (`model`, from RDF: elements/arcs/params) plus the ontology's element classes (`ont.classes`, with each class's ports) becomes a `CompiledCircuit` -- port indices resolved, audio fan-in checked, a topological execution order computed (Kahn's algorithm, `val:UnitDelay` treated as a source so feedback loops can be broken), and Tarjan's algorithm staging the multi-node strongly-connected components to be stepped sample by sample. Output is plain JSON, safe to `postMessage()` into the worklet unchanged. |
| `dsp.mjs` | **both** (imported directly by `worklet.js`, and by `audio.mjs`'s `ScriptProcessorNode` fallback) | The `Engine` class and every DSP element (`Oscillator`, `Ladder`, `Reed`, `Granulator`, ...) that a `CompiledCircuit` can instantiate, keyed by `IMPLEMENTED` (the element names this build has code for -- `compiler.mjs`'s output flags any circuit element outside that set as a pass-through). Pure computation: no `window`, no `document`, so it loads inside the restricted `AudioWorkletGlobalScope`. |
| `worklet.js` | **audio rendering thread only** | `ValisProcessor extends AudioWorkletProcessor`, registered as `"valis-engine"`. Receives `{type:'circuit', compiled}` over its message port, instantiates `dsp.mjs`'s `Engine`, and runs `engine.process()` once per audio quantum. Sends `{type:'ready'|'meters'|'error', ...}` back. |
| `audio.mjs` | main thread | The host: owns the `AudioContext`, loads `worklet.js` as the processor module (falling back to a deprecated `ScriptProcessorNode`, built straight on `dsp.mjs`'s `Engine`, if worklet modules are refused), and exposes `loadCircuit()`/`noteOn()`/`noteOff()`/`setTransport()`/`setParam()`/`onMeters()`/`onError()` etc. as the one channel the rest of the notebook talks to the engine through. |
| `sequencer.mjs` | main thread | The transport: a lookahead scheduler (`Audio.now()` plus a 120 ms lookahead window) that stamps note events with audio-clock times and hands them to `audio.mjs`. Two pattern kinds: drum rows keyed by MIDI note (one row per `val:NoteGate` element the compiled circuit has) and a monophonic note sequence for circuits driven by the host gate. |

## The worklet-URL rule

`audio.mjs`'s `ensureEngineNode()` loads the processor with:

```js
await ctx.audioWorklet.addModule(new URL('./worklet.js', import.meta.url));
```

a same-origin **file** URL. The hub page's Content-Security-Policy is
`script-src 'self'`, which blocks a Blob URL or a `data:` URL passed to
`addModule()` -- the original (non-vendored) app worked around that by
stringifying the whole DSP engine into the worklet module's source
text at runtime. That workaround is gone here: `worklet.js` is a real
file next to `dsp.mjs` and imports it with an ordinary static `import`
statement, which `AudioWorkletGlobalScope` supports as of the
Chromium/Firefox versions this project targets. Do not reintroduce a
Blob/data URL for the worklet module; it will 404 under the strict
page's CSP the same way an external `<script src>` does.

`audio.mjs` and `worklet.js` each define `WORKLET_NAME = 'valis-engine'`
independently rather than importing it from one another -- `worklet.js`
cannot be imported from the main thread (it references
`AudioWorkletProcessor`/`registerProcessor`/`sampleRate`, which only
exist inside the worklet global scope, so evaluating the module outside
it throws). Keep the two string literals in sync by hand if either
changes.

## How the notebook uses them

Hub post 55's audio cell imports `audio.mjs` and `sequencer.mjs` only
when `AudioContext` exists (skipping entirely under Node, where the
cell returns `{skipped: "no AudioContext"}`) and only after the reader
taps Play, so the modules are never fetched on an ordinary page load:

```js
const base = new URL("../valis-daw/", valisBase);
const Audio = await import(new URL("audio.mjs", base));
const Seq = await import(new URL("sequencer.mjs", base));
const compiled = daw.compile(model, elementClasses, implemented);
await Audio.loadCircuit(compiled);
Seq.configure(compiled);
Seq.start();
```

`daw.compile` (the post's library cell, at the end of the post) is
`compiler.mjs`'s `compile` export, imported the same way. `implemented`
is the `Set` a cell builds from `dsp.mjs`'s `IMPLEMENTED` list, so the
compiler can flag any circuit element this build has no DSP code for.
