---
title: "Valis: a drum machine in RDF"
description: "The Valis synthesizer vocabulary and a TR-909 circuit, parsed and queried live by this engine, with the same six npm usability items from issue #679 measured on every page load."
layout: hub.njk
series: docs-hub
series_order: 55
vocab: none
status: published
tests: tests/hub/post55_test.mjs
---

[Valis](https://github.com/danja/valis), by Danny Ayers, describes virtual
analog synthesizer circuits in RDF: an LV2-style port vocabulary for
elements (oscillators, filters, envelopes, resonators) and Turtle documents
that wire elements into a circuit with `val:Arc`/`val:ControlArc`. The
vocabulary and the example circuit below are vendored, byte for byte, into
[`third_party/valis/`](https://github.com/danbri/factoidal/tree/claude/main/third_party/valis)
under MIT (see that directory's `PROVENANCE.md` for the commit and licence
record). The engine that plays them —
[`docs/web/hub/assets/valis-daw/`](https://github.com/danbri/factoidal/tree/claude/main/docs/web/hub/assets/valis-daw) —
is the owner's clean-room JavaScript reimplementation, built from the
Turtle and Valis's documentation, not a port of upstream's C++; the
derivation review is
[danbri/factoidal#687 (comment)](https://github.com/danbri/factoidal/issues/687#issuecomment-5701030083).

Building that engine against `@factoidal/core` produced a report of six
usability gaps in the npm package,
[danbri/factoidal#679](https://github.com/danbri/factoidal/issues/679).
This notebook runs the same parses and queries the DAW runs — the Valis
ontology, the TR-909 circuit, the port and arc SPARQL, an UPDATE and a
Turtle serialization — with timings, and a probe cell that checks each of
the report's items against the live API. As the linked issues land, the
probe's answers change; `tests/hub/post55_expected.json` pins today's
answers and is edited deliberately when one flips.

## Loading the vocabulary and the circuit

`valisBase` points at the vendored files this page serves same-origin.
The Node test overrides it to a `file:` URL so the pinned cells read the
committed files directly.

```observable-js
valisBase = new URL("../assets/valis/", location.href).href
```

```observable-js
ontologyText = (await fetch(valisBase + "vocabs/valis.ttl")).text()
```

```observable-js
circuitText = (await fetch(valisBase + "examples/909.ttl")).text()
```

The ontology declares its own namespace as `http://purl.org/stuff/valis/`;
the circuit has no namespace of its own; the DAW opens it under a
`urn:valis:909` base.

```observable-js
ontology = {
  const t0 = performance.now();
  const ds = await fn.parse(ontologyText, {
    format: "turtle",
    baseIRI: "http://purl.org/stuff/valis/",
  });
  daw.timing.set("ontology parse", performance.now() - t0);
  return ds;
}
```

```observable-js
return ontology.size;
```

```observable-js
circuit = {
  const t0 = performance.now();
  const ds = await fn.parse(circuitText, { format: "turtle", baseIRI: "urn:valis:909" });
  daw.timing.set("circuit parse", performance.now() - t0);
  return ds;
}
```

```observable-js
return circuit.size;
```

## The port query

The DAW reads every element class's ports with one `GROUP_CONCAT` query
(`rdfmodel.js` lines 252-270 of the owner's original client) — one row per
port, with its LV2 port properties (`logarithmic`, `integer`, `toggled`, …)
folded into a single space-separated string so the row stays one binding
per port rather than fanning out per property. A second query collects
each port's named scale points (the Oscillator's `shape` values: sine,
saw, square, triangle) separately, since a `GROUP_CONCAT` over those would
lose their individual labels.

```observable-js
PORT_QUERY = daw.PREFIXES + `
  # Every element class's ports, with LV2 port properties folded into one
  # string per port (GROUP_CONCAT) so a port with several properties
  # still comes back as one row.
  SELECT ?c ?impl ?p ?sym ?name ?dir ?kind ?def ?min ?max ?unit ?usym ?cmt
         (GROUP_CONCAT(STR(?pp); separator=" ") AS ?props)
  WHERE {
    ?c a rdfs:Class ; lv2:port ?p .
    ?p lv2:symbol ?sym ; a ?dir ; a ?kind .
    FILTER(?dir IN (lv2:InputPort, lv2:OutputPort))
    FILTER(?kind IN (lv2:AudioPort, lv2:ControlPort))
    OPTIONAL { ?c val:implementation ?impl }
    OPTIONAL { ?p lv2:name ?name }
    OPTIONAL { ?p lv2:default ?def }
    OPTIONAL { ?p lv2:minimum ?min }
    OPTIONAL { ?p lv2:maximum ?max }
    OPTIONAL { ?p units:unit ?unit . OPTIONAL { ?unit units:symbol ?usym } }
    OPTIONAL { ?p lv2:portProperty ?pp }
    OPTIONAL { ?p rdfs:comment ?cmt }
  }
  GROUP BY ?c ?impl ?p ?sym ?name ?dir ?kind ?def ?min ?max ?unit ?usym ?cmt`
```

```observable-js
SCALE_QUERY = daw.PREFIXES + `
  # Named scale points (e.g. Oscillator's shape: 0 sine, 1 saw, ...).
  SELECT ?p ?v ?l WHERE { ?c lv2:port ?p . ?p lv2:scalePoint ?s . ?s rdf:value ?v ; rdfs:label ?l }`
```

```observable-js
portRows = {
  const t0 = performance.now();
  const rows = await fn.query(ontology, PORT_QUERY);
  daw.timing.set("port query", performance.now() - t0);
  return rows;
}
```

```observable-js
scalePoints = fn.query(ontology, SCALE_QUERY)
```

`daw.foldPorts` is the same row-folding step `rdfmodel.js`'s ontology
loader does after the query returns: group the port rows by class, attach
each port's scale points, and read the class hierarchy and comments
straight off the parsed dataset.

```observable-js
elementClasses = daw.foldPorts(portRows, scalePoints, ontology)
```

```observable-js
return pretty(Object.values(elementClasses.classes)
  .map((c) => ({ class: c.name, implementation: c.impl || "", ports: c.ports.length }))
  .sort((a, b) => a.class.localeCompare(b.class)));
```

## The circuit: elements and arcs

The arc query joins each `val:Arc`/`val:ControlArc`'s blank-node endpoints
in one query (`rdfmodel.js` lines 406-413) rather than walking them with
several `RDF/JS` `match()` calls.

```observable-js
ARC_QUERY = daw.PREFIXES + `
  # Each arc's endpoints: a blank node giving the element and the port name.
  SELECT ?a ?fn ?fp ?tn ?tp ?d WHERE {
    ?a val:from ?f ; val:to ?t .
    ?f val:node ?fn ; val:port ?fp .
    ?t val:node ?tn ; val:port ?tp .
    OPTIONAL { ?a val:depth ?d }
  }`
```

```observable-js
arcRows = {
  const t0 = performance.now();
  const rows = await fn.query(circuit, ARC_QUERY);
  daw.timing.set("arc query", performance.now() - t0);
  return rows;
}
```

`daw.circuitModel` assembles the typed elements and the resolved arcs the
same way `rdfmodel.js`'s circuit loader does, reading `fn`'s Dataset by
iterating its quads rather than through `RDF/JS` `match()`, which the `fn`
Dataset does not implement.

```observable-js
model = daw.circuitModel(circuit, arcRows)
```

```observable-js
{
  // Computing the row array in its own statement, rather than passing
  // "model.elements.map(...)" straight to pretty(), is deliberate: the
  // post's reactive-cell analyzer is regex-based and mis-scans a
  // function call wrapped directly around a chained method call as one
  // long parameter list, hiding "model" as a real dependency. See the
  // daw library cell's arcQueryRows/circuitMdl comment for the same
  // hazard from a different angle.
  const rows = model.elements.map((el) => ({ element: el.local, type: el.type }));
  return pretty(rows);
}
```

```observable-js
{
  const rows = model.arcs.map((a) => ({ from: a.from, to: a.to, depth: a.depth }));
  return pretty(rows);
}
```

## Editing the circuit: UPDATE, then Turtle

The DAW's own editor writes a property change back with one SPARQL UPDATE
per changed value — `DELETE` the old triple if any, `INSERT` the new one,
guarded by an `OPTIONAL` so a property that was never set still gets
inserted — then serializes the whole dataset as Turtle. Here it retunes
the bass-drum oscillator from its 55 Hz thump to 440 Hz (concert pitch).

```observable-js
UPDATE = daw.PREFIXES + `
  DELETE { <urn:valis:909#bdOsc> val:frequency ?o }
  INSERT { <urn:valis:909#bdOsc> val:frequency 440.0 }
  WHERE { OPTIONAL { <urn:valis:909#bdOsc> val:frequency ?o } }`
```

```observable-js
edited = {
  const t0 = performance.now();
  const ds = await fn.update(circuit, UPDATE);
  daw.timing.set("update", performance.now() - t0);
  return ds;
}
```

```observable-js
turtleOut = {
  const t0 = performance.now();
  const text = await fn.serialize(edited, { format: "turtle" });
  daw.timing.set("serialize", performance.now() - t0);
  return text;
}
```

```observable-js
return turtleOut.split("\n").slice(0, 30).join("\n");
```

## What it costs

Milliseconds for each step above, measured with `performance.now()` inside
the cell that does the work and collected in `daw.timing`.

```observable-js
timings = {
  // Reference every timed cell so this one runs after all six have.
  ontology; portRows; circuit; arcRows; edited; turtleOut;
  const timingMap = daw.timing; // an alias -- "...daw.timing" below would read as member
                                 // access on the spread's trailing dot, hiding the daw reference
  return pretty([...timingMap].map(([step, ms]) => ({ step, ms: Math.round(ms * 10) / 10 })));
}
```

## The API items from issue #679

Three of the six usability items the DAW session reported are checkable
from inside a cell: does a broken parse reject rather than answer an empty
dataset ([#344](https://github.com/danbri/factoidal/issues/344)); does a
parsed dataset carry the prefixes it read, and does a Turtle serialization
reuse them instead of inventing `ns1:`
([#681](https://github.com/danbri/factoidal/issues/681)); does a decimal
like `440.0` print bare instead of `"440.0"^^xsd:decimal`
([#681](https://github.com/danbri/factoidal/issues/681)); and does the
typed API expose a parse-once, query-many dataset handle
([#680](https://github.com/danbri/factoidal/issues/680)). Every check is a
try/catch against the real API, not an assumption about what should be
true.

```observable-js
apiItems = {
  const items = {};
  try {
    await fn.parse("this is not turtle");
    items.strictParse = false;
  } catch (err) {
    items.strictParse = true;
  }
  try {
    items.parseReturnsPrefixes = !!(
      ontology && ontology.prefixes && typeof ontology.prefixes === "object" && "val" in ontology.prefixes
    );
  } catch (err) {
    items.parseReturnsPrefixes = false;
  }
  try {
    items.turtleUsesSourcePrefixes = turtleOut.includes("@prefix val:");
  } catch (err) {
    items.turtleUsesSourcePrefixes = false;
  }
  try {
    items.decimalShorthand = turtleOut.includes("440.0") && !turtleOut.includes('"440.0"');
  } catch (err) {
    items.decimalShorthand = false;
  }
  try {
    items.datasetHandle = typeof fn.openDataset === "function";
  } catch (err) {
    items.datasetHandle = false;
  }
  return items;
}
```

```observable-js
return pretty(apiItems);
```

## Play it

Compiles the circuit and plays a 16-step pattern through Web Audio. The
step grid below is read straight from the circuit's `val:NoteGate`
elements — no audio module is loaded until this button is pressed.

```observable-js
{
  if (typeof AudioContext === "undefined" && typeof webkitAudioContext === "undefined") {
    return { skipped: "no AudioContext" };
  }

  // Mirrors sequencer.mjs's configure(): one row per val:NoteGate,
  // keyed by MIDI note, with the same four-bar seed pattern it plays.
  const SEED = {
    36: [0, 4, 8, 12], 35: [0, 4, 8, 12], 38: [4, 12], 40: [4, 12],
    42: [0, 2, 4, 6, 8, 10, 12], 39: [4, 12], 46: [14],
  };
  const gates = model.elements
    .filter((el) => el.type === "NoteGate")
    .map((el) => ({ local: el.local, note: Number(el.props.note) }))
    .sort((a, b) => a.note - b.note);

  const root = html`<div>
    <p><strong>${gates.length} drum rows, 16 steps.</strong></p>
    <div style="display:flex;gap:.6em;align-items:center;margin:.5em 0;flex-wrap:wrap;">
      <button type="button" class="valis-play">Play</button>
      <button type="button" class="valis-stop" disabled>Stop</button>
      <label>Tempo <input type="number" class="valis-bpm" value="120" min="30" max="300" style="width:4em"> bpm</label>
    </div>
    <table class="valis-grid" style="border-collapse:collapse;font-size:.85em"></table>
    <pre class="valis-log" aria-live="polite">Tap Play to compile the circuit and start the engine.</pre>
  </div>`;

  const table = root.querySelector(".valis-grid");
  for (const g of gates) {
    const row = document.createElement("tr");
    const label = document.createElement("td");
    label.textContent = g.local;
    label.style.paddingRight = ".6em";
    row.appendChild(label);
    const hits = new Set(SEED[g.note] || []);
    for (let s = 0; s < 16; s++) {
      const cell = document.createElement("td");
      cell.textContent = hits.has(s) ? "#" : "·";
      cell.style.width = "1.2em";
      cell.style.textAlign = "center";
      row.appendChild(cell);
    }
    table.appendChild(row);
  }

  const playBtn = root.querySelector(".valis-play");
  const stopBtn = root.querySelector(".valis-stop");
  const bpmInput = root.querySelector(".valis-bpm");
  const log = root.querySelector(".valis-log");
  let Seq = null;

  playBtn.addEventListener("click", async () => {
    playBtn.disabled = true;
    log.textContent = "Loading the audio engine...";
    try {
      const base = new URL("../valis-daw/", valisBase);
      const [Audio, SeqMod, Dsp] = await Promise.all([
        import(new URL("audio.mjs", base).href),
        import(new URL("sequencer.mjs", base).href),
        import(new URL("dsp.mjs", base).href),
      ]);
      Seq = SeqMod;
      const implemented = new Set(Dsp.IMPLEMENTED);
      const compiled = await daw.compile(model, elementClasses, implemented);
      await Audio.unlock();
      await Audio.loadCircuit(compiled);
      Seq.configure(compiled);
      Seq.setBpm(Number(bpmInput.value) || 120);
      Seq.start();
      globalThis.__valisAudio = {
        state: Audio.state.ctx ? Audio.state.ctx.state : "closed",
        nodeCount: compiled.nodes.length,
      };
      log.textContent = `Playing: ${compiled.nodes.length} DSP nodes, ${Audio.mode()} mode, context ${Audio.state.ctx.state}.`;
      stopBtn.disabled = false;
    } catch (err) {
      log.textContent = "Play failed: " + err.message;
      playBtn.disabled = false;
    }
  });
  stopBtn.addEventListener("click", () => {
    if (Seq) Seq.stop();
    stopBtn.disabled = true;
    playBtn.disabled = false;
    log.textContent = "Stopped.";
  });
  bpmInput.addEventListener("change", () => {
    if (Seq) Seq.setBpm(Number(bpmInput.value) || 120);
  });
  return root;
}
```

## Library: DAW helpers

The RDF-facing helpers below (`rdfmodel.js`'s namespace map, term
conversion and the port/element/arc folding steps used above) and
`compile` (`compiler.mjs`, imported on first use) live in one cell at the
end of the post, closed by default, so the notebook's actual subject
stays above the fold.

```observable-js closed title="Library: DAW helpers"
daw = ({
  NS: {
    val: "http://purl.org/stuff/valis/",
    lv2: "http://lv2plug.in/ns/lv2core#",
    units: "http://lv2plug.in/ns/extensions/units#",
    rdf: "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
    rdfs: "http://www.w3.org/2000/01/rdf-schema#",
    xsd: "http://www.w3.org/2001/XMLSchema#",
    owl: "http://www.w3.org/2002/07/owl#",
  },
  NUMERIC_LOCAL_NAMES: [
    "decimal", "integer", "double", "float", "int", "long", "short", "byte",
    "nonNegativeInteger", "positiveInteger", "negativeInteger", "nonPositiveInteger",
    "unsignedInt", "unsignedLong", "unsignedShort", "unsignedByte",
  ],
  UNIT_SYMBOLS: {
    hz: "Hz", khz: "kHz", mhz: "MHz", db: "dB", ms: "ms", s: "s", min: "min", pc: "%",
    semitone12TET: "st", cent: "ct", midiNote: "note", bpm: "bpm", coef: "", degree: "°",
    m: "m", cm: "cm", mm: "mm", km: "km", inch: "in", mile: "mi", bar: "bar", beat: "beat",
    frame: "fr", oct: "oct",
  },
  get PREFIXES() {
    return Object.keys(this.NS).map((k) => `PREFIX ${k}: <${this.NS[k]}>`).join("\n") + "\n";
  },
  local(iri) {
    if (!iri) return "";
    const h = iri.lastIndexOf("#");
    if (h >= 0) return iri.slice(h + 1);
    return iri.slice(iri.lastIndexOf("/") + 1);
  },
  termValue(t) {
    if (!t) return null;
    if (t.termType === "Literal") {
      const dt = t.datatype && t.datatype.value;
      const dtLocal = dt ? this.local(dt) : null;
      if (dt && this.NUMERIC_LOCAL_NAMES.includes(dtLocal)) {
        const n = Number(t.value);
        return Number.isNaN(n) ? t.value : n;
      }
      if (dt === this.NS.xsd + "boolean") return t.value === "true" || t.value === "1";
      return t.value;
    }
    return t.value; // NamedNode / BlankNode -> IRI / label
  },
  bnodeOrder(t) {
    const m = /(\d+)$/.exec((t && t.value) || "");
    return m ? Number(m[1]) : 0;
  },
  // The port-row folding step from rdfmodel.js's loadOntology(), factored
  // out to take an already-run query's rows instead of running the query
  // itself. `ontologyDs` supplies the class hierarchy (rdfs:subClassOf)
  // and comments, read by iterating its quads -- fn's Dataset has no
  // RDF/JS match(), unlike the raw @factoidal/core Dataset rdfmodel.js uses.
  foldPorts(rows, scale, ontologyDs) {
    const scaleByPort = {};
    for (const b of scale) {
      const p = b.get("p").value;
      (scaleByPort[p] = scaleByPort[p] || []).push({
        value: Number(this.termValue(b.get("v"))),
        label: this.termValue(b.get("l")),
      });
    }
    const classes = {};
    const seenPort = {};
    for (const b of rows) {
      const c = this.local(b.get("c").value);
      const p = b.get("p");
      const pid = p.value;
      const cls = classes[c] = classes[c] || {
        name: c, iri: b.get("c").value, impl: null, ports: [], parent: null, comment: "",
      };
      if (b.get("impl")) cls.impl = this.termValue(b.get("impl"));
      if (seenPort[c + "|" + pid]) continue; // GROUP BY may duplicate when a port has two OPTIONAL matches
      seenPort[c + "|" + pid] = true;
      const props = (b.get("props") ? this.termValue(b.get("props")) : "") || "";
      const unitIri = b.get("unit") ? b.get("unit").value : null;
      let unit = "";
      if (b.get("usym")) unit = this.termValue(b.get("usym"));
      else if (unitIri && unitIri.startsWith(this.NS.units)) {
        const key = this.local(unitIri);
        unit = this.UNIT_SYMBOLS[key] != null ? this.UNIT_SYMBOLS[key] : key;
      }
      const enumPts = scaleByPort[pid] ? scaleByPort[pid].slice().sort((a, b2) => a.value - b2.value) : null;
      cls.ports.push({
        sym: this.termValue(b.get("sym")),
        name: b.get("name") ? this.termValue(b.get("name")) : this.termValue(b.get("sym")),
        dir: b.get("dir").value.endsWith("InputPort") ? "in" : "out",
        kind: b.get("kind").value.endsWith("AudioPort") ? "audio" : "control",
        def: b.get("def") != null ? Number(this.termValue(b.get("def")))
          : (b.get("kind").value.endsWith("AudioPort") ? null : 0),
        min: b.get("min") != null ? Number(this.termValue(b.get("min"))) : null,
        max: b.get("max") != null ? Number(this.termValue(b.get("max"))) : null,
        unit,
        log: /logarithmic/.test(props),
        integer: /integer/.test(props),
        toggled: /toggled/.test(props),
        enum: enumPts,
        comment: b.get("cmt") ? this.termValue(b.get("cmt")) : "",
        _order: this.bnodeOrder(p),
      });
    }
    for (const c of Object.keys(classes)) {
      classes[c].ports.sort((a, b) => a._order - b._order);
      classes[c].ports.forEach((p) => { delete p._order; });
    }
    const quads = [...ontologyDs];
    for (const q of quads) {
      if (q.predicate.value !== this.NS.rdfs + "subClassOf") continue;
      const c = this.local(q.subject.value);
      if (!classes[c]) {
        classes[c] = { name: c, iri: q.subject.value, impl: null, ports: [], parent: null, comment: "", abstract: true };
      }
      classes[c].parent = this.local(q.object.value);
    }
    for (const q of quads) {
      if (q.predicate.value !== this.NS.rdfs + "comment") continue;
      const c = this.local(q.subject.value);
      if (classes[c]) classes[c].comment = String(this.termValue(q.object)).replace(/\s+/g, " ").trim();
    }
    return { classes, triples: ontologyDs.size };
  },
  // The element/arc/param assembly step from rdfmodel.js's loadCircuit(),
  // taking an already-run arc query's rows and reading the typed subjects
  // by iterating the circuit dataset's quads (same match()-free approach
  // as foldPorts above). Parameter named arcQueryRows, not arcRows: the
  // post's reactive-cell analyzer is regex-based and does not recognise
  // object-method parameter lists as local bindings, so a parameter
  // reusing a cell's name here would read as a real (and circular)
  // dependency on that cell.
  circuitModel(circuitDs, arcQueryRows) {
    const quads = [...circuitDs];
    const rdfType = this.NS.rdf + "type";
    const SKIP = new Set(["Circuit", "Endpoint", "Arc", "ControlArc", "Param"]);
    const typed = new Map();
    for (const q of quads) {
      if (q.predicate.value !== rdfType) continue;
      if (q.object.termType !== "NamedNode" || !q.object.value.startsWith(this.NS.val)) continue;
      const cls = this.local(q.object.value);
      const arr = typed.get(q.subject.value) || [];
      arr.push(cls);
      typed.set(q.subject.value, arr);
    }
    const propsOf = (subj) => {
      const props = {};
      for (const q of quads) {
        if (q.subject.value !== subj) continue;
        const p = q.predicate.value;
        if (p === rdfType) continue;
        if (p.startsWith(this.NS.val)) {
          const k = this.local(p);
          props[k] = q.object.termType === "NamedNode" ? this.local(q.object.value) : this.termValue(q.object);
        }
      }
      return props;
    };
    const elements = [];
    for (const [iri, classesOf] of typed) {
      const cls = classesOf.find((c) => !SKIP.has(c)) || classesOf[0];
      if (SKIP.has(cls)) continue;
      elements.push({ id: iri, local: this.local(iri), type: cls, props: propsOf(iri) });
    }
    elements.sort((a, b) => a.local.localeCompare(b.local));

    const seenArc = new Set();
    const arcs = [];
    for (const b of arcQueryRows) {
      const id = b.get("a").value;
      if (seenArc.has(id)) continue;
      seenArc.add(id);
      arcs.push({
        id, local: this.local(id),
        from: this.local(b.get("fn").value) + "." + String(this.termValue(b.get("fp"))),
        to: this.local(b.get("tn").value) + "." + String(this.termValue(b.get("tp"))),
        depth: b.get("d") != null ? Number(this.termValue(b.get("d"))) : null,
      });
    }
    arcs.sort((a, b) => a.local.localeCompare(b.local));

    const params = [];
    for (const [iri, classesOf] of typed) {
      if (!classesOf.includes("Param")) continue;
      const props = propsOf(iri);
      const targetQuad = quads.find((q) => q.subject.value === iri && q.predicate.value === this.NS.val + "target");
      params.push({
        id: iri, local: this.local(iri),
        slot: Number(props.slot),
        target: targetQuad ? targetQuad.object.value : null,
        property: props.property || null,
      });
    }
    params.sort((a, b) => (a.slot - b.slot) || a.local.localeCompare(b.local));

    return { elements, arcs, params };
  },
  // compiler.mjs is only fetched the first time a cell actually calls
  // this -- normally when the reader presses Play. Parameter named
  // circuitMdl, not model, for the same reason arcQueryRows above is not
  // named arcRows.
  async compile(circuitMdl, ont, implemented) {
    const mod = await import(new URL("../valis-daw/compiler.mjs", valisBase));
    return mod.compile(circuitMdl, ont, implemented);
  },
  timing: new Map(),
})
```
