/*
 * Small, dependency-free RDF/SPARQL result views for Factoidal Hub pages.
 *
 * Public elements:
 *   <factoidal-sparql-results>  SPARQL Results JSON SELECT bindings
 *   <factoidal-sparql-graph>    graph rows / RDFJS-like quads
 *   <factoidal-sparql-boolean>  ASK result
 *   <factoidal-sparql-error>    query error/status message
 *
 * `data` accepts a JSON-encoded SPARQL Results JSON document.  In script,
 * setting `.results = result` is preferable: no JSON attribute escaping and
 * no limit on the payload size. `view=table|cards`, `palette=sage|ocean|plum|sand`,
 * `language-tags=show|hide`, `datatypes=show|hide`, `tags=show|hide`
 * (a backwards-compatible shorthand for both), `transpose`,
 * `card-direction=horizontal|vertical`, and `max-rows` are declarative
 * customisation points.
 */

const XSD_STRING = "http://www.w3.org/2001/XMLSchema#string";
const PALETTES = {
  sage: { ink: "#183b2c", muted: "#50675b", paper: "#f8fcf8", soft: "#e7f2e9", line: "#c7ddcd", accent: "#286846", focus: "#0e6fda" },
  ocean: { ink: "#15394b", muted: "#4b6572", paper: "#f7fbfc", soft: "#e5f1f5", line: "#c4dce5", accent: "#196a85", focus: "#075fd0" },
  plum: { ink: "#41253f", muted: "#70566c", paper: "#fdf9fc", soft: "#f4eaf2", line: "#e1cce0", accent: "#7b3f74", focus: "#075fd0" },
  sand: { ink: "#493719", muted: "#6e604a", paper: "#fdfbf6", soft: "#f6eedc", line: "#e4d6b9", accent: "#88611a", focus: "#075fd0" },
};

const css = `
  :host { display:block; color:var(--fr-ink); font:inherit; }
  *, *::before, *::after { box-sizing:border-box; }
  .shell { --fr-ink:#183b2c; --fr-muted:#50675b; --fr-paper:#f8fcf8; --fr-soft:#e7f2e9; --fr-line:#c7ddcd; --fr-accent:#286846; --fr-focus:#0e6fda; border:1px solid var(--fr-line); background:var(--fr-paper); border-radius:14px; overflow:hidden; }
  .top { padding: .85rem 1rem .75rem; background:var(--fr-soft); border-bottom:1px solid var(--fr-line); }
  .summary { margin:0; color:var(--fr-ink); font-size:.94rem; }
  .toolbar { display:flex; flex-wrap:wrap; align-items:end; gap:.55rem .75rem; padding:.75rem 1rem; border-bottom:1px solid var(--fr-line); }
  label { color:var(--fr-muted); font-size:.78rem; font-weight:650; display:grid; gap:.22rem; }
  select, button { min-height:2.6rem; max-width:100%; border:1px solid var(--fr-line); background:var(--fr-paper); color:var(--fr-ink); border-radius:.5rem; padding:.35rem .55rem; font:inherit; }
  select { min-width:7.2rem; }
  button { cursor:pointer; font-size:.88rem; }
  button[aria-pressed="true"] { background:var(--fr-accent); border-color:var(--fr-accent); color:#fff; }
  button:focus-visible, select:focus-visible, a:focus-visible { outline:3px solid var(--fr-focus); outline-offset:2px; }
  .count { margin-left:auto; color:var(--fr-muted); font-size:.82rem; }
  .table-wrap { max-height:31rem; overflow:auto; }
  table { border-collapse:separate; border-spacing:0; width:100%; min-width:max-content; }
  caption { position:absolute; width:1px; height:1px; padding:0; margin:-1px; overflow:hidden; clip:rect(0,0,0,0); white-space:nowrap; border:0; }
  th, td { border-right:1px solid var(--fr-line); border-bottom:1px solid var(--fr-line); text-align:left; vertical-align:top; padding:.55rem .68rem; }
  th:last-child, td:last-child { border-right:0; }
  tbody tr:last-child td { border-bottom:0; }
  th { position:sticky; top:0; z-index:1; background:var(--fr-soft); color:var(--fr-ink); font-size:.84rem; }
  th button { min-height:auto; border:0; background:transparent; padding:0; color:inherit; font-weight:700; text-align:left; }
  th button:hover { text-decoration:underline; }
  td { background:var(--fr-paper); max-width:27rem; }
  .term { display:flex; align-items:baseline; flex-wrap:wrap; gap:.24rem; min-width:9rem; }
  .term-main { overflow-wrap:anywhere; }
  .term.iri .term-main { color:var(--fr-accent); text-decoration:none; }
  .term.iri .term-main:hover { text-decoration:underline; }
  .kind, .meta { color:var(--fr-muted); font: .76rem/1.25 ui-monospace, SFMono-Regular, Menlo, monospace; }
  .meta { background:var(--fr-soft); border-radius:999px; padding:.1rem .36rem; max-width:100%; overflow:hidden; text-overflow:ellipsis; white-space:nowrap; }
  .missing { color:var(--fr-muted); }
  .cards { display:grid; gap:.75rem; padding:1rem; }
  .cards.horizontal { grid-auto-flow:column; grid-auto-columns:minmax(17rem, 85%); grid-template-columns:unset; overflow-x:auto; scroll-snap-type:x mandatory; }
  .card { border:1px solid var(--fr-line); border-radius:.75rem; padding:.8rem; background:var(--fr-paper); scroll-snap-align:start; }
  .card h3 { font-size:.9rem; margin:0 0 .65rem; color:var(--fr-muted); }
  dl { margin:0; display:grid; gap:.55rem; }
  dt { font-size:.78rem; font-weight:700; color:var(--fr-muted); }
  dd { margin:.08rem 0 0; }
  .empty { padding:1.2rem 1rem; color:var(--fr-muted); }
  .error { border-color:#d68075; background:#fff8f7; color:#6b1d16; padding:.85rem 1rem; border-radius:.65rem; }
  .error strong { display:block; }
  @media (max-width: 520px) { .toolbar { align-items:stretch; } label { flex:1 1 8rem; } select { width:100%; min-width:0; } .count { flex-basis:100%; margin-left:0; } th, td { padding:.5rem; } }
  @media (prefers-color-scheme: dark) { .shell { filter:brightness(.9) saturate(.82); } .error { background:#351b19; color:#ffd8d2; border-color:#9b4b42; } }
`;

function element(name, text) { const e = document.createElement(name); if (text !== undefined) e.textContent = text; return e; }
function classed(name, text, className) { const e = element(name, text); e.className = className; return e; }
function compactIri(value) { const v = String(value || ""); const i = Math.max(v.lastIndexOf("#"), v.lastIndexOf("/")); return i >= 0 && i < v.length - 1 ? v.slice(i + 1) : v; }
function isTerm(v) { return v && typeof v === "object" && typeof v.type === "string" && "value" in v; }
function termKind(t) { return t.type === "uri" ? "IRI" : t.type === "bnode" ? "blank node" : t.type === "literal" || t.type === "typed-literal" ? "literal" : t.type || "value"; }
function termText(t) {
  if (!isTerm(t)) return t === undefined || t === null ? "" : String(t);
  if (t.type === "uri") return compactIri(t.value);
  if (t.type === "bnode") return "_:" + t.value;
  return `“${t.value}”`;
}
function termMeta(t) { if (!isTerm(t)) return ""; return t["xml:lang"] || t.lang || t.language || ((t.datatype && t.datatype !== XSD_STRING) ? compactIri(t.datatype) : ""); }
function normalizeTerm(t) {
  if (isTerm(t)) return t;
  if (t && typeof t === "object" && t.termType) {
    return { type: t.termType === "NamedNode" ? "uri" : t.termType === "BlankNode" ? "bnode" : "literal", value: t.value, datatype: t.datatype?.value, lang: t.language };
  }
  return { type:"literal", value:String(t ?? "") };
}
function rowMetadata(row, kind) {
  return Object.values(row).map(normalizeTerm).map(t => kind === "language"
    ? (t.lang || t.language || t["xml:lang"] || "")
    : (t.datatype && t.datatype !== XSD_STRING ? t.datatype : ""))
    .filter(Boolean).sort()[0] || "";
}

class ResultBase extends HTMLElement {
  constructor() { super(); this.attachShadow({mode:"open"}); this._data = null; }
  connectedCallback() { this.render(); }
  static get observedAttributes() { return ["data", "palette", "view", "tags", "language-tags", "datatypes", "transpose", "card-direction", "max-rows", "message", "label"]; }
  attributeChangedCallback() { if (this.isConnected) this.render(); }
  set results(v) { this._data = v; this.render(); }
  get results() { return this._data; }
  get palette() { return PALETTES[this.getAttribute("palette")] || PALETTES.sage; }
  styles(root) { const s=element("style", css); root.append(s); }
  readData() { if (this._data) return this._data; const raw=this.getAttribute("data"); if (!raw) return null; try { return JSON.parse(raw); } catch { return null; } }
}

export class FactoidalSparqlResults extends ResultBase {
  constructor() { super(); this.state={ view:null, languageTags:null, datatypes:null, lang:"", datatype:"", sort:"", dir:1, transpose:false }; }
  attributeChangedCallback(name, oldValue, newValue) {
    if (oldValue !== newValue) {
      if (name === "view") this.state.view = newValue || "table";
      if (name === "language-tags" || name === "tags") this.state.languageTags = this.getAttribute("language-tags") || this.getAttribute("tags") || "show";
      if (name === "datatypes" || name === "tags") this.state.datatypes = this.getAttribute("datatypes") || this.getAttribute("tags") || "show";
      if (name === "transpose") this.state.transpose = this.hasAttribute("transpose");
    }
    if (this.isConnected) this.render();
  }
  getRows() { const d=this.readData(); return Array.isArray(d) ? d : (d?.results?.bindings || d?.bindings || []); }
  getVars(rows) { const d=this.readData(); return d?.head?.vars || d?.vars || [...new Set(rows.flatMap(r => Object.keys(r)))]; }
  makeTerm(t) {
    const term=normalizeTerm(t), wrap=element("span"); wrap.className="term " + (term.type === "uri" ? "iri" : "");
    const main=term.type === "uri" ? element("a", termText(term)) : element("span", termText(term));
    main.className="term-main"; main.title=String(term.value || "");
    if (term.type === "uri") { main.href=term.value; main.target="_blank"; main.rel="noreferrer"; main.setAttribute("aria-label", `Open IRI ${term.value}`); }
    wrap.append(main);
    const language=term.lang || term.language || term["xml:lang"] || "";
    const datatype=term.datatype && term.datatype !== XSD_STRING ? term.datatype : "";
    if (this.state.languageTags !== "hide" || this.state.datatypes !== "hide") wrap.append(classed("span", termKind(term), "kind"));
    if (language && this.state.languageTags !== "hide") wrap.append(classed("span", "@" + language, "meta"));
    if (datatype && this.state.datatypes !== "hide") wrap.append(classed("span", compactIri(datatype), "meta"));
    return wrap;
  }
  control(labelText, options, current, onChange) { const label=element("label", labelText), select=element("select"); for (const [v,t] of options) { const o=element("option",t); o.value=v; o.selected=v===current; select.append(o); } select.addEventListener("change", () => onChange(select.value)); label.append(select); return label; }
  render() {
    const root=this.shadowRoot; root.replaceChildren(); this.styles(root); const p=this.palette;
    const shell=element("section"); shell.className="shell"; Object.entries(p).forEach(([k,v])=>shell.style.setProperty(`--fr-${k}`,v)); root.append(shell);
    const rawRows=this.getRows(), vars=this.getVars(rawRows);
    this.state.view ||= this.getAttribute("view") || "table";
    this.state.languageTags ||= this.getAttribute("language-tags") || this.getAttribute("tags") || "show";
    this.state.datatypes ||= this.getAttribute("datatypes") || this.getAttribute("tags") || "show";
    this.state.transpose ||= this.hasAttribute("transpose");
    const languageValues=[...new Set(rawRows.flatMap(r=>Object.values(r).map(x=>{const t=normalizeTerm(x); return t.lang || t.language || t["xml:lang"] || "";}).filter(Boolean)))].sort();
    const datatypeValues=[...new Set(rawRows.flatMap(r=>Object.values(r).map(x=>{const t=normalizeTerm(x); return t.datatype && t.datatype !== XSD_STRING ? t.datatype : "";}).filter(Boolean)))].sort();
    let rows=rawRows.filter(r => (!this.state.lang || Object.values(r).some(x => {const t=normalizeTerm(x); return (t.lang||t.language||t["xml:lang"]||"")===this.state.lang;})) && (!this.state.datatype || Object.values(r).some(x => normalizeTerm(x).datatype===this.state.datatype)));
    if (this.state.sort) rows=rows.slice().sort((a,b)=>this.sortText(a).localeCompare(this.sortText(b), undefined, {numeric:true, sensitivity:"base"})*this.state.dir);
    const max=Number(this.getAttribute("max-rows")); if (Number.isFinite(max) && max>0) rows=rows.slice(0,max);
    const top=element("div"); top.className="top"; top.append(classed("p", `${rawRows.length.toLocaleString()} result ${rawRows.length===1?"row":"rows"}${rows.length!==rawRows.length ? ` · ${rows.length.toLocaleString()} shown` : ""}`, "summary")); shell.append(top);
    if (!rawRows.length) { shell.append(classed("div", "This query returned no solution bindings.", "empty")); return; }
    const toolbar=element("div"); toolbar.className="toolbar";
    toolbar.append(this.control("View", [["table","Table"],["cards","Record cards"]], this.state.view, v=>{this.state.view=v; this.render();}));
    toolbar.append(this.control("Language", [["","All languages"], ...languageValues.map(x=>[x,"@"+x])], this.state.lang, v=>{this.state.lang=v; this.render();}));
    toolbar.append(this.control("Datatype", [["","All datatypes"], ...datatypeValues.map(x=>[x,compactIri(x)])], this.state.datatype, v=>{this.state.datatype=v; this.render();}));
    toolbar.append(this.control("Sort", [["","Document order"], ...vars.map(v=>["var:"+v,"?"+v]), ["language","Language tag"], ["datatype","Datatype"]], this.state.sort, v=>{this.state.sort=v;this.state.dir=1;this.render();}));
    const languageTags=element("button", this.state.languageTags === "hide" ? "Show language tags" : "Hide language tags"); languageTags.type="button"; languageTags.setAttribute("aria-pressed", String(this.state.languageTags !== "hide")); languageTags.addEventListener("click",()=>{this.state.languageTags=this.state.languageTags === "hide" ? "show":"hide";this.render();}); toolbar.append(languageTags);
    const datatypes=element("button", this.state.datatypes === "hide" ? "Show datatypes" : "Hide datatypes"); datatypes.type="button"; datatypes.setAttribute("aria-pressed", String(this.state.datatypes !== "hide")); datatypes.addEventListener("click",()=>{this.state.datatypes=this.state.datatypes === "hide" ? "show":"hide";this.render();}); toolbar.append(datatypes);
    if (this.state.view === "table") { const flip=element("button", this.state.transpose ? "Rows as records" : "Columns as records"); flip.type="button"; flip.setAttribute("aria-pressed",String(this.state.transpose)); flip.addEventListener("click",()=>{this.state.transpose=!this.state.transpose;this.render();}); toolbar.append(flip); }
    if (this.state.view === "cards") toolbar.append(this.control("Cards", [["vertical","Vertical"],["horizontal","Swipeable row"]], this.getAttribute("card-direction") || "vertical", v=>{this.setAttribute("card-direction",v); this.render();}));
    toolbar.append(classed("span", `${vars.length} variables`, "count")); shell.append(toolbar);
    shell.append(this.state.view === "cards" ? this.cards(rows,vars) : this.table(rows,vars));
  }
  sortText(row) {
    if (this.state.sort === "language") return rowMetadata(row, "language");
    if (this.state.sort === "datatype") return rowMetadata(row, "datatype");
    if (this.state.sort.startsWith("var:")) return String(normalizeTerm(row[this.state.sort.slice(4)]).value);
    return "";
  }
  chooseSort(sort) { if(this.state.sort===sort)this.state.dir*=-1;else{this.state.sort=sort;this.state.dir=1;}this.render(); }
  header(name) { const sort="var:"+name, th=element("th"), b=element("button", name + (this.state.sort===sort ? (this.state.dir>0?" ▲":" ▼") : "")); th.scope="col"; b.type="button"; b.title="Sort by this variable"; b.addEventListener("click",()=>this.chooseSort(sort)); th.append(b); return th; }
  table(rows, vars) {
    const wrap=element("div"); wrap.className="table-wrap"; const table=element("table"); table.append(element("caption", "SPARQL SELECT results"));
    const head=element("thead"), hr=element("tr"); if (this.state.transpose) { hr.append(element("th","Variable")); rows.forEach((_,i)=>hr.append(element("th",`Result ${i+1}`))); } else vars.forEach(v=>hr.append(this.header(v))); head.append(hr); table.append(head);
    const body=element("tbody");
    if (this.state.transpose) vars.forEach(v=>{const tr=element("tr"); const name=element("th",v);name.scope="row";tr.append(name); rows.forEach(r=>{const td=element("td"); if(r[v]===undefined) td.append(classed("span", "—", "missing")); else td.append(this.makeTerm(r[v])); tr.append(td);}); body.append(tr);});
    else rows.forEach(r=>{const tr=element("tr"); vars.forEach(v=>{const td=element("td"); if(r[v]===undefined) td.append(classed("span", "—", "missing")); else td.append(this.makeTerm(r[v])); tr.append(td);}); body.append(tr);});
    table.append(body); wrap.append(table); return wrap;
  }
  cards(rows, vars) { const cards=element("div"); cards.className="cards " + (this.getAttribute("card-direction") || "vertical"); rows.forEach((r,i)=>{const card=element("article");card.className="card";card.append(element("h3",`Result ${i+1}`));const dl=element("dl");vars.forEach(v=>{const group=element("div");group.append(element("dt",v));const dd=element("dd");dd.append(r[v]===undefined?element("span","—"):this.makeTerm(r[v]));group.append(dd);dl.append(group);});card.append(dl);cards.append(card);});return cards; }
}

export class FactoidalSparqlGraph extends ResultBase {
  get graph() { return this._data; } set graph(v) { this._data=v; this.render(); }
  render() { const root=this.shadowRoot;root.replaceChildren();this.styles(root);const p=this.palette,shell=element("section");shell.className="shell";Object.entries(p).forEach(([k,v])=>shell.style.setProperty(`--fr-${k}`,v));root.append(shell);const d=this.readData();const rows=Array.isArray(d)?d:(d?.triples||d?.quads||[]);shell.append(classed("div",`${rows.length.toLocaleString()} RDF ${rows.length===1?"statement":"statements"}`, "top"));if(!rows.length){shell.append(classed("div","This graph is empty.", "empty"));return;}const results=document.createElement("factoidal-sparql-results");for(const name of ["palette","view","tags","language-tags","datatypes","transpose","card-direction","max-rows"]) if(this.hasAttribute(name)) results.setAttribute(name,this.getAttribute(name) || "");results.results={head:{vars:["subject","predicate","object","graph"]},results:{bindings:rows.map(q=>({subject:normalizeTerm(q.subject||q.s),predicate:normalizeTerm(q.predicate||q.p),object:normalizeTerm(q.object||q.o),graph:normalizeTerm(q.graph||q.g||{type:"uri",value:"default graph"})}))}};shell.append(results); }
}

export class FactoidalSparqlBoolean extends ResultBase {
  render() { const root=this.shadowRoot;root.replaceChildren();this.styles(root);const p=this.palette,shell=element("section");shell.className="shell";Object.entries(p).forEach(([k,v])=>shell.style.setProperty(`--fr-${k}`,v));const data=this.readData();const value=typeof data === "boolean" ? data : !!(data?.boolean ?? data?.value);const h=element("div");h.className="top";h.append(classed("p", value?"Yes — this ASK query matches.":"No — this ASK query does not match.", "summary"));shell.append(h);const e=element("div", value?"TRUE":"FALSE");e.className="empty";e.style.fontSize="1.7rem";e.style.fontWeight="750";shell.append(e);root.append(shell); }
}

export class FactoidalSparqlError extends ResultBase {
  render() { const root=this.shadowRoot;root.replaceChildren();this.styles(root);const text=this.getAttribute("message") || (this.readData()?.message) || "The query could not be completed.";const box=element("div");box.className="error";box.setAttribute("role","alert");box.append(element("strong","Query problem"),element("span",text));root.append(box); }
}

if (!customElements.get("factoidal-sparql-results")) customElements.define("factoidal-sparql-results", FactoidalSparqlResults);
if (!customElements.get("factoidal-sparql-graph")) customElements.define("factoidal-sparql-graph", FactoidalSparqlGraph);
if (!customElements.get("factoidal-sparql-boolean")) customElements.define("factoidal-sparql-boolean", FactoidalSparqlBoolean);
if (!customElements.get("factoidal-sparql-error")) customElements.define("factoidal-sparql-error", FactoidalSparqlError);
