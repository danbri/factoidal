/*
 * compiler.mjs — CircuitModel -> CompiledCircuit.
 * Validates elements and arcs against the ontology, resolves port indices,
 * checks audio fan-in, and produces a topological execution order that
 * includes control arcs. Feedback cycles must pass through val:UnitDelay.
 * Output is plain JSON so it can cross into an AudioWorklet unchanged.
 *
 * This is the owner's clean-room JavaScript reimplementation of the
 * Valis synthesizer engine (https://github.com/danja/valis), built from
 * the Valis Turtle vocabulary (third_party/valis/vocabs/valis.ttl) and
 * its documentation, not from the upstream C++ (src/, include/).
 * Licensed with this repository (Apache-2.0). Derivation review:
 * https://github.com/danbri/factoidal/issues/687#issuecomment-5701030083
 */
'use strict';

export function compile(model, ont, implemented) {
  const errors = [], warnings = [], info = [];
  const classes = ont.classes;
  const nodes = [];
  const byId = new Map();

  for (const el of model.elements) {
    let cls = classes[el.type];
    if (cls && cls.name === 'NonLinear') cls = classes.Transfer;
    const node = {
      idx: nodes.length, id: el.id, local: el.local, label: el.label, type: el.type,
      impl: cls && cls.impl ? cls.impl : el.type,
      ai: [], ao: [], ci: [], co: [], ciBase: [], ciMeta: [], coDef: [],
      props: {}, x: el.x, y: el.y, unknown: false, implemented: true,
    };
    if (!cls || cls.abstract || !cls.ports.length) {
      errors.push(`element ${el.local}: val:${el.type} is not an element class in the ontology${cls && cls.abstract ? ' (it is abstract)' : ''}`);
      node.unknown = true;
    } else {
      for (const p of cls.ports) {
        if (p.kind === 'audio') (p.dir === 'in' ? node.ai : node.ao).push(p.sym);
        else if (p.dir === 'in') {
          node.ci.push(p.sym);
          let v = el.props[p.sym];
          if (typeof v === 'boolean') v = v ? 1 : 0;
          if (typeof v === 'string') { const n = Number(v); v = Number.isNaN(n) ? undefined : n; }
          if (typeof v !== 'number') v = p.def != null ? p.def : 0;
          node.ciBase.push(v);
          node.ciMeta.push({ min: p.min, max: p.max, log: !!p.log, unit: p.unit || '', enum: p.enum || null, integer: !!p.integer, toggled: !!p.toggled, def: p.def, name: p.name });
        } else { node.co.push(p.sym); node.coDef.push(p.def != null ? p.def : 0); }
      }
      for (const k of Object.keys(el.props)) {
        const v = el.props[k];
        if (node.ci.indexOf(k) >= 0) continue;
        if (k === 'x' || k === 'y') continue;
        node.props[k] = v; // e.g. val:file, val:seconds, val:antialiasing
        if (typeof v === 'number' && !['seconds'].includes(k)) warnings.push(`element ${el.local}: val:${k} is not a control port of val:${el.type}; kept as a plain property`);
      }
    }
    node.implemented = !node.unknown && implemented.has(node.impl);
    nodes.push(node);
    byId.set(el.id, node);
  }

  const audioArcs = [], ctlArcs = [];
  let plainControl = 0;
  const audioIn = new Map(); // "toIdx:portIdx" → count
  const drawArcs = []; // every arc that resolved, for the graph view (includes skipped ones flagged)
  for (const arc of model.arcs) {
    const a = byId.get(arc.from.node), b = byId.get(arc.to.node);
    const name = arc.local;
    if (!a || !b) { errors.push(`arc ${name}: ${!a ? arc.from.node : arc.to.node} is not an element in this circuit`); continue; }
    let fromKind = null, outIdx = a.ao.indexOf(arc.from.port);
    if (outIdx >= 0) fromKind = 'audio'; else { outIdx = a.co.indexOf(arc.from.port); if (outIdx >= 0) fromKind = 'control'; }
    let toKind = null, inIdx = b.ai.indexOf(arc.to.port);
    if (inIdx >= 0) toKind = 'audio'; else { inIdx = b.ci.indexOf(arc.to.port); if (inIdx >= 0) toKind = 'control'; }
    const d = { id: arc.id, local: name, from: a.idx, to: b.idx, fromPort: arc.from.port, toPort: arc.to.port, kind: null, ok: false, depth: arc.depth };
    drawArcs.push(d);
    if (a.unknown || b.unknown) { warnings.push(`arc ${name}: skipped because ${a.unknown ? a.local : b.local} has no known ports`); continue; }
    if (fromKind == null) { errors.push(`arc ${name}: ${a.local} (val:${a.type}) has no output port "${arc.from.port}"`); continue; }
    if (toKind == null) { errors.push(`arc ${name}: ${b.local} (val:${b.type}) has no input port "${arc.to.port}"`); continue; }
    if (fromKind !== toKind) { errors.push(`arc ${name}: ${a.local}.${arc.from.port} is ${fromKind} rate but ${b.local}.${arc.to.port} is ${toKind} rate`); continue; }
    d.kind = fromKind;
    if (fromKind === 'audio') {
      const key = b.idx + ':' + inIdx;
      const n = (audioIn.get(key) || 0) + 1;
      audioIn.set(key, n);
      if (n > 1 && b.type !== 'Mixer') { errors.push(`arc ${name}: second audio arc into ${b.local}.${arc.to.port}; only val:Mixer sums (dropped)`); continue; }
      audioArcs.push({ from: a.idx, out: outIdx, to: b.idx, in: inIdx });
    } else {
      const meta = b.ciMeta[inIdx] || {};
      const range = (typeof meta.min === 'number' && typeof meta.max === 'number') ? (meta.max - meta.min) : 1;
      const mult = meta.unit === 'Hz' || !!meta.log;
      if (arc.kind === 'Arc') plainControl++;
      ctlArcs.push({ from: a.idx, out: outIdx, to: b.idx, in: inIdx, depth: arc.depth, mode: arc.depth == null ? 'replace' : 'mod', mult, range: range || 1 });
    }
    d.ok = true;
  }

  if (plainControl) info.push(`${plainControl} arc(s) typed val:Arc end on control ports and are treated as control arcs`);

  // Execution order: Kahn's algorithm over audio + control arcs, with
  // val:UnitDelay treated as a source (its inbound edges are ignored and it
  // runs first, so its input is always the previous sample).
  const n = nodes.length;
  const indeg = new Array(n).fill(0);
  const succ = Array.from({ length: n }, () => []);
  const allEdges = audioArcs.concat(ctlArcs);
  for (const e of allEdges) {
    if (nodes[e.to].type === 'UnitDelay') continue;
    succ[e.from].push(e.to);
    indeg[e.to]++;
  }
  const order = [];
  const done = new Array(n).fill(false);
  const queue = [];
  for (let i = 0; i < n; i++) if (nodes[i].type === 'UnitDelay') { queue.push(i); }
  for (let i = 0; i < n; i++) if (indeg[i] === 0 && nodes[i].type !== 'UnitDelay') queue.push(i);
  while (queue.length) {
    const i = queue.shift();
    if (done[i]) continue;
    done[i] = true;
    order.push(i);
    for (const j of succ[i]) { if (--indeg[j] === 0) queue.push(j); }
  }
  if (order.length < n) {
    // Something is stuck in a cycle with no UnitDelay. Name one loop, then append the rest in a DFS order.
    const stuck = [];
    for (let i = 0; i < n; i++) if (!done[i]) stuck.push(i);
    const loop = findCycle(stuck, succ);
    if (loop) errors.push('feedback loop with no val:UnitDelay to break it: ' + loop.map((i) => nodes[i].local).join(' -> '));
    else errors.push('unresolved dependency among: ' + stuck.map((i) => nodes[i].local).join(', '));
    for (const i of stuck) if (!done[i]) { done[i] = true; order.push(i); }
    warnings.push('the loop was run in document order with a one-block delay on its back edge; the sound may differ from the original circuit');
  }

  const outputs = nodes.filter((nd) => nd.type === 'Output');
  if (outputs.length === 0) warnings.push('no val:Output element: the circuit will be silent');
  if (outputs.length > 1) warnings.push(`${outputs.length} val:Output elements; all are summed`);
  const unimplemented = [...new Set(nodes.filter((nd) => !nd.unknown && !nd.implemented).map((nd) => nd.type))];
  for (const t of unimplemented) warnings.push(`val:${t} has no DSP implementation in this build; instances pass audio through unchanged and hold their control outputs at the ontology default`);

  // Depth (longest path from a source) for the layered graph view.
  const depth = new Array(n).fill(0);
  for (const i of order) for (const j of succ[i]) depth[j] = Math.max(depth[j], depth[i] + 1);

  // Stages: strongly connected components of the full graph (UnitDelay edges
  // included). A multi-node component is a feedback loop and is stepped
  // sample by sample; everything else runs per 32-sample block. Components
  // are sequenced by a topological sort of the condensation, in which a
  // UnitDelay that is not inside a loop is treated as a source so it runs
  // before the element it delays.
  const fullSucc = Array.from({ length: n }, () => []);
  for (const e of allEdges) fullSucc[e.from].push(e.to);
  const sccs = tarjan(n, fullSucc);
  const comp = new Array(n).fill(0);
  sccs.forEach((m, k) => m.forEach((i) => { comp[i] = k; }));
  const pos = new Map(order.map((i, k) => [i, k]));
  const C = sccs.length;
  const cIn = new Array(C).fill(0);
  const cSucc = Array.from({ length: C }, () => new Set());
  for (const e of allEdges) {
    const a = comp[e.from], b = comp[e.to];
    if (a === b) continue;
    if (nodes[e.to].type === 'UnitDelay' && sccs[b].length === 1) continue;
    if (!cSucc[a].has(b)) { cSucc[a].add(b); cIn[b]++; }
  }
  const cMin = sccs.map((m) => Math.min(...m.map((i) => pos.get(i))));
  const cDelay = sccs.map((m) => m.length === 1 && nodes[m[0]].type === 'UnitDelay');
  const cDone = new Array(C).fill(false);
  const stages = [];
  for (let step = 0; step < C; step++) {
    let best = -1;
    for (let c = 0; c < C; c++) {
      if (cDone[c] || cIn[c] > 0) continue;
      if (best < 0 || (cDelay[c] && !cDelay[best]) || (cDelay[c] === cDelay[best] && cMin[c] < cMin[best])) best = c;
    }
    if (best < 0) { for (let c = 0; c < C; c++) if (!cDone[c]) { best = c; break; } } // should not happen: condensation is acyclic
    cDone[best] = true;
    for (const b of cSucc[best]) cIn[b]--;
    const members = sccs[best].slice().sort((a, b) => pos.get(a) - pos.get(b));
    stages.push({ nodes: members, sample: members.length > 1 });
  }
  const finalOrder = [];
  for (const st of stages) for (const i of st.nodes) finalOrder.push(i);
  const loops = stages.filter((st) => st.sample).length;
  if (loops) info.push(`${loops} feedback loop(s) will be evaluated sample by sample; the rest of the circuit runs in 32-sample blocks`);

  return {
    label: model.label, nodes, audioArcs, ctlArcs, drawArcs, order: finalOrder, depth, stages,
    errors, warnings, info, unimplemented,
    params: model.params,
  };
}

function tarjan(n, succ) {
  let index = 0;
  const idx = new Array(n).fill(-1), low = new Array(n).fill(0), on = new Array(n).fill(false), stack = [], out = [];
  const strong = (v) => {
    idx[v] = low[v] = index++; stack.push(v); on[v] = true;
    for (const w of succ[v]) {
      if (idx[w] < 0) { strong(w); low[v] = Math.min(low[v], low[w]); }
      else if (on[w]) low[v] = Math.min(low[v], idx[w]);
    }
    if (low[v] === idx[v]) {
      const comp = [];
      let w;
      do { w = stack.pop(); on[w] = false; comp.push(w); } while (w !== v);
      out.push(comp);
    }
  };
  for (let v = 0; v < n; v++) if (idx[v] < 0) strong(v);
  return out;
}

function findCycle(stuck, succ) {
  const inStuck = new Set(stuck);
  const state = new Map();
  const stack = [];
  let found = null;
  const dfs = (i) => {
    if (found) return;
    state.set(i, 1); stack.push(i);
    for (const j of succ[i]) {
      if (!inStuck.has(j)) continue;
      if (state.get(j) === 1) { found = stack.slice(stack.indexOf(j)).concat([j]); return; }
      if (!state.has(j)) dfs(j);
      if (found) return;
    }
    state.set(i, 2); stack.pop();
  };
  for (const i of stuck) { if (!state.has(i)) dfs(i); if (found) break; }
  return found;
}
