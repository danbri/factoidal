const root = location.pathname.startsWith("/factoidal/") ? "/factoidal/" : "/";
const pkgUrl = root + "npm/factoidal/browser.js";
const haclBase = root + "npm/factoidal/hacl-wasm/";
const HACL_MODULES = [
  "WasmSupport", "FStar", "LowStar_Endianness",
  "Hacl_Hash_Base", "Hacl_Hash_SHA2",
  "Hacl_IntTypes_Intrinsics", "Hacl_Bignum_Base", "Hacl_Bignum",
  "Hacl_Bignum25519_51", "Hacl_Curve25519_51",
  "Hacl_Ed25519_PrecompTable", "Hacl_Ed25519"
];
const SECRET_KEY =
  "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60";
const THEOREM =
  "urn:factoidal:theorem:fstar:RDF.Entailment.RDFS.RhoDFClosure:rho_df_closure_sound";
const DEFAULT_RDFS_TTL = `PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX ex: <https://example.org/fxev-demo#>

ex:Engineer rdfs:subClassOf ex:Employee .
ex:Employee rdfs:subClassOf ex:Agent .
ex:audits rdfs:domain ex:Auditor .
ex:audits rdfs:range ex:EvidencePackage .
ex:audits rdfs:subPropertyOf ex:reviews .
ex:grace ex:audits ex:rdfs-run-001 .
ex:ada rdf:type ex:Engineer .`;
const DEFAULT_VC_DOC =
  '<https://example.org/credential/1> <https://example.org/claim> "Factoidal evidence demo" .\n';
const DEFAULT_VC_CONFIG =
  '_:pc <http://www.w3.org/ns/data-integrity#cryptosuite> "eddsa-rdfc-2022" .\n';

const $ = (id) => document.getElementById(id);
const status = {
  package: $("fxev-package-status"),
  wasm: $("fxev-wasm-status"),
  crypto: $("fxev-crypto-status")
};
const buttons = [...document.querySelectorAll("[data-fxev-run]")];

let factoidalPromise = null;
let haclPromise = null;

function seedDefaults() {
  if ($("fxev-rdfs-input") && !$("fxev-rdfs-input").value.trim()) {
    $("fxev-rdfs-input").value = DEFAULT_RDFS_TTL;
  }
  if ($("fxev-vc-doc") && !$("fxev-vc-doc").value.trim()) {
    $("fxev-vc-doc").value = DEFAULT_VC_DOC;
  }
  if ($("fxev-vc-config") && !$("fxev-vc-config").value.trim()) {
    $("fxev-vc-config").value = DEFAULT_VC_CONFIG;
  }
}

function setBusy(busy) {
  buttons.forEach((button) => { button.disabled = busy; });
}

function setText(node, text) {
  node.textContent = text;
}

function shortHex(hex) {
  return hex && hex.length > 18 ? hex.slice(0, 18) + "..." : String(hex || "");
}

function unwrap(value, key) {
  if (value && typeof value === "object" && key in value) return value[key];
  return value;
}

function escapeLiteral(value) {
  return String(value)
    .replace(/\\/g, "\\\\")
    .replace(/"/g, '\\"')
    .replace(/\n/g, "\\n");
}

function ntLines(text) {
  return String(text || "").split(/\r?\n/).map((line) => line.trim()).filter(Boolean);
}

async function loadFactoidal() {
  if (!factoidalPromise) {
    status.package.textContent = "package: loading";
    factoidalPromise = import(pkgUrl).then((mod) => {
      status.package.textContent = "@factoidal/core browser module loaded";
      return mod;
    });
  }
  return factoidalPromise;
}

function loadClassicScript(url) {
  return new Promise((resolve, reject) => {
    const script = document.createElement("script");
    script.src = url;
    script.onload = resolve;
    script.onerror = () => reject(new Error("failed to load " + url));
    document.head.appendChild(script);
  });
}

async function loadPatchedClassicScript(url, patch) {
  const response = await fetch(url);
  if (!response.ok) throw new Error("script fetch failed: " + response.status + " " + url);
  const source = patch(await response.text());
  const blobUrl = URL.createObjectURL(new Blob([source], { type: "text/javascript" }));
  try {
    await loadClassicScript(blobUrl);
  } finally {
    URL.revokeObjectURL(blobUrl);
  }
}

async function loadPatchedHaclLoader() {
  await loadPatchedClassicScript(haclBase + "loader.js", (source) =>
    source.replace('if (typeof process !== "undefined") {', 'if (false) {')
  );
}

async function loadPatchedHaclApi() {
  await loadPatchedClassicScript(haclBase + "api.js", (source) =>
    source
      .replace('fetch("api.json")', 'fetch("' + haclBase + 'api.json")')
      .replace('fetch("layouts.json")', 'fetch("' + haclBase + 'layouts.json")')
      .replace(/\bfetch\(m\)/g, 'fetch("' + haclBase + '" + m)')
  );
}

async function initHacl() {
  if (!haclPromise) {
    status.crypto.textContent = "crypto: loading HACL* WASM";
    haclPromise = (async () => {
      if (!globalThis.HaclWasm) {
        await loadPatchedHaclLoader();
        await loadClassicScript(haclBase + "shell.js");
        await loadPatchedHaclApi();
      }
      const hacl = await globalThis.HaclWasm.getInitializedHaclModule(HACL_MODULES);
      globalThis.__factoidalHacl = hacl;
      status.crypto.textContent = "crypto: HACL* WASM ready";
      return hacl;
    })();
  }
  return haclPromise;
}

async function factoidalSha256(factoidal, text) {
  await initHacl();
  return unwrap(await factoidal.vcSha256Hex(text), "sha256");
}

async function runRdfs() {
  const factoidal = await loadFactoidal();
  const input = $("fxev-rdfs-input").value;
  const started = performance.now();
  const fragment = await factoidal.coreRdfsCheck(input, { format: "turtle" });
  const closed = await factoidal.coreRdfsClosure(input, { format: "turtle" });
  const elapsed = Math.round(performance.now() - started);
  const closedLines = ntLines(closed.ntriples);
  const derivedQuery = [
    "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>",
    "PREFIX ex: <https://example.org/fxev-demo#>",
    "SELECT ?s ?p ?o WHERE {",
    "  VALUES (?s ?p ?o) {",
    "    (ex:ada rdf:type ex:Agent)",
    "    (ex:grace rdf:type ex:Auditor)",
    "    (ex:grace ex:reviews ex:rdfs-run-001)",
    "    (ex:rdfs-run-001 rdf:type ex:EvidencePackage)",
    "  }",
    "}"
  ].join("\n");

  let queryEngine = "wasm";
  let derived = null;
  try {
    status.wasm.textContent = "query engine: trying WASM";
    derived = await factoidal.queryDataset(
      [{ content: closed.ntriples, dataFormat: "ntriples" }],
      derivedQuery,
      { engine: "wasm", output: "json", wasmUrl: root + "npm/factoidal/factoidal.wasm.js" }
    );
    status.wasm.textContent = "query engine: WASM";
  } catch (_err) {
    queryEngine = "js fallback";
    status.wasm.textContent = "query engine: JS fallback";
    derived = await factoidal.query(closed.ntriples, derivedQuery, {
      dataFormat: "ntriples",
      output: "json"
    });
  }

  const inputHash = await factoidalSha256(factoidal, input);
  const outputHash = await factoidalSha256(factoidal, closed.ntriples);
  const rows = (derived && derived.results && derived.results.bindings) || [];
  const evidence = [
    "@prefix fxev: <https://factoidal.dev/ns/evidence#> .",
    "@prefix prov: <http://www.w3.org/ns/prov#> .",
    "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .",
    "",
    "<#live-rdfs-run> a fxev:EvidencePackage, fxev:VerifiedRun ;",
    "  fxev:policyProfile fxev:RegulatedRdfsSoundnessProfile ;",
    "  fxev:claim <#live-rdfs-byte-identity>, <#live-rdfs-soundness>, <#live-rdfs-software-gate>, <#live-rdfs-nonclaim> ;",
    '  prov:generatedAtTime "' + new Date().toISOString() + '"^^xsd:dateTime .',
    "",
    "<#live-rdfs-byte-identity> a fxev:ByteIdentityClaim ;",
    "  fxev:claimKind fxev:ByteIdentity ;",
    "  fxev:sourceArtifact <sha256:" + inputHash + "> ;",
    "  fxev:resultArtifact <sha256:" + outputHash + "> ;",
    '  fxev:algorithm "Factoidal Turtle parser plus N-Triples closure output" .',
    "",
    "<#live-rdfs-soundness> a fxev:SemanticClaim ;",
    "  fxev:claimKind fxev:Semantic ;",
    '  fxev:regime "core-RDFS / rho-df" ;',
    '  fxev:fragment "' + (fragment.fragment ? "accepted" : "rejected") + ' by coreRdfsCheck" ;',
    "  fxev:theorem <" + THEOREM + "> ;",
    "  fxev:theoremStatus fxev:CarriedHypothesis ;",
    "  fxev:proofProfile fxev:SoundnessNotCompleteness .",
    "",
    "<#live-rdfs-software-gate> a fxev:SoftwareClaim ;",
    "  fxev:claimKind fxev:SoftwareCorrectness ;",
    '  fxev:implementation "@factoidal/core browser module" ;',
    '  fxev:verifiedBy "coreRdfsClosure plus ' + queryEngine + ' SPARQL check" ;',
    '  fxev:testReport "derived rows=' + rows.length + '; closure triples=' + closedLines.length + '; elapsedMs=' + elapsed + '" .',
    "",
    "<#live-rdfs-nonclaim> a fxev:Refusal ;",
    '  fxev:refusesClaim "complete RDFS entailment for unrestricted RDF graphs" ;',
    '  fxev:reason "This live sketch records core-RDFS closure evidence only." .',
    "",
    "# Derived facts found by the live query:",
    rows.map((row) =>
      "# " + [row.s.value, row.p.value, row.o.value].join(" ")
    ).join("\n")
  ].join("\n");

  setText($("fxev-rdfs-output"), evidence);
}

async function runVc() {
  const factoidal = await loadFactoidal();
  await initHacl();
  const doc = $("fxev-vc-doc").value;
  const cfg = $("fxev-vc-config").value;
  const publicKey = unwrap(await factoidal.vcEd25519SecretToPublic(SECRET_KEY), "publicKeyHex");
  const proofValue = unwrap(
    await factoidal.vcEddsaCreateFromCanonical(SECRET_KEY, doc, cfg),
    "proofValue"
  );
  const verified = unwrap(
    await factoidal.vcEddsaVerifyFromCanonical(publicKey, doc, cfg, proofValue),
    "verified"
  );
  const tamperVerified = unwrap(
    await factoidal.vcEddsaVerifyFromCanonical(
      publicKey,
      doc.replace("Factoidal evidence demo", "Factoidal evidence tamper"),
      cfg,
      proofValue
    ),
    "verified"
  );
  const docHash = await factoidalSha256(factoidal, doc);
  const cfgHash = await factoidalSha256(factoidal, cfg);
  const evidence = [
    "@prefix fxev: <https://factoidal.dev/ns/evidence#> .",
    "@prefix prov: <http://www.w3.org/ns/prov#> .",
    "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .",
    "",
    "<#live-vc-run> a fxev:EvidencePackage, fxev:VerifiedRun ;",
    "  fxev:policyProfile fxev:RegulatedCredentialProfile ;",
    "  fxev:claim <#live-vc-document-identity>, <#live-vc-proof-verification>, <#live-vc-semantic-nonclaim> ;",
    '  prov:generatedAtTime "' + new Date().toISOString() + '"^^xsd:dateTime .',
    "",
    "<#live-vc-document-identity> a fxev:ByteIdentityClaim ;",
    "  fxev:claimKind fxev:ByteIdentity ;",
    "  fxev:canonicalArtifact <sha256:" + docHash + "> ;",
    "  fxev:digest " + JSON.stringify(docHash) + " ;",
    '  fxev:algorithm "caller-supplied canonical document N-Quads" .',
    "",
    "<#live-vc-proof-verification> a fxev:CryptographicClaim ;",
    "  fxev:claimKind fxev:Cryptographic ;",
    '  fxev:algorithm "eddsa-rdfc-2022 over canonical document and proof config" ;',
    "  fxev:digest " + JSON.stringify("sha256(document)=" + shortHex(docHash) + "; sha256(config)=" + shortHex(cfgHash)) + " ;",
    '  fxev:verificationMethod "did:key/demo-ed25519-public-key-' + publicKey.slice(0, 12) + '" ;',
    '  fxev:verifiedBy "@factoidal/core vcEddsaVerifyFromCanonical over HACL* WebAssembly" ;',
    "  fxev:theoremStatus fxev:Measured ;",
    '  fxev:proofProfile "verified=' + verified + '; tamperCheck=' + tamperVerified + '" ;',
    '  fxev:resultArtifact "' + escapeLiteral(proofValue) + '" .',
    "",
    "<#live-vc-semantic-nonclaim> a fxev:Refusal ;",
    '  fxev:refusesClaim "the credential subject assertion is true" ;',
    '  fxev:reason "The live check verifies Data Integrity crypto over canonical inputs; it does not validate real-world truth or authorization." .'
  ].join("\n");

  setText($("fxev-vc-output"), evidence);
}

async function run(which) {
  setBusy(true);
  try {
    if (which === "rdfs" || which === "all") await runRdfs();
    if (which === "vc" || which === "all") await runVc();
  } catch (err) {
    const target = which === "vc" ? $("fxev-vc-output") : $("fxev-rdfs-output");
    setText(target, "Live run failed:\n" + (err && err.stack ? err.stack : String(err)));
  } finally {
    setBusy(false);
  }
}

buttons.forEach((button) => {
  button.addEventListener("click", () => run(button.dataset.fxevRun));
});

seedDefaults();
