---
title: "AI beside a local knowledge graph"
description: "A small, optional browser-AI experiment: check availability, ask a question about the life-sciences Shardborough, and inspect a proposed read-only SPARQL query."
layout: hub.njk
series: docs-hub
series_order: 49
vocab: sparql
status: experimental
tests: tests/hub/post49_test.mjs
---

This is deliberately a small experiment, not an autonomous agent. First check
whether this browser has local AI. Then ask a question about the life-sciences
Shardborough. If available, the model proposes a read-only SPARQL query; it
does not receive the Turtle files, execute the query, or send data to a cloud
service. The [Shardborough notebook](../50-shardborough-life-sciences/) owns
the inspectable graph manifest and user-run query.

```observable-js
localAiForKg = {
  const profile = {
    graphs: ["urn:kgx:chromosome (9,227 triples)", "urn:kgx:sequence_variant (6,455 triples)", "urn:kgx:disease (27,421 triples)"],
    prefixes: { wdt: "http://www.wikidata.org/prop/direct/", wd: "http://www.wikidata.org/entity/" },
    knownFacts: ["?chrom wdt:P31 wd:Q37748", "?variant wdt:P1057 ?chrom"],
  };
  // Prompt API language/modality contract. `expectedInputs`/`expectedOutputs`
  // are current Chrome names; the two *Languages aliases keep this notebook
  // usable on the immediately preceding Chromium contract, whose diagnostic
  // says “No output language was specified”. Web-IDL ignores unknown fields.
  const languageOptions = {
    expectedInputs: [{ type: "text", languages: ["en"] }],
    expectedOutputs: [{ type: "text", languages: ["en"] }],
    expectedInputLanguages: ["en"],
    expectedOutputLanguages: ["en"],
  };
  const root = html`<div><p><strong>1. Check local AI.</strong> <button class="check">Check availability</button> <span class="status" aria-live="polite">Not checked.</span></p><p><strong>2. Ask about the local graph.</strong><br><textarea rows="3">Find sequence variants and their chromosome entities.</textarea></p><p><button class="ask">Propose read-only SPARQL</button> <button class="release" disabled>Release local AI</button></p><p class="result-status" aria-live="polite"></p><pre aria-live="polite">No request made.</pre></div>`;
  const check = root.querySelector(".check"), ask = root.querySelector(".ask"), release = root.querySelector(".release"), status = root.querySelector(".status"), resultStatus = root.querySelector(".result-status"), question = root.querySelector("textarea"), out = root.querySelector("pre");
  let session = null, creating = null;
  async function availability() {
    if (!globalThis.LanguageModel?.availability || !globalThis.LanguageModel?.create) return "unavailable (this browser exposes no LanguageModel API)";
    return await LanguageModel.availability(languageOptions);
  }
  async function getSession() {
    if (session) return session;
    if (creating) return creating;
    creating = (async () => {
      const a = await availability();
      if (String(a).startsWith("unavailable")) throw new Error(a);
      status.textContent = a === "available"
        ? "Chrome reports the model available; creating one local session…"
        : `Chrome reports “${a}”; preparing its local model…`;
      const created = await LanguageModel.create({
        ...languageOptions,
        monitor(monitor) {
          monitor.addEventListener("downloadprogress", event => {
            status.textContent = `Downloading Chrome's local AI model: ${Math.round(event.loaded * 100)}%`;
          });
        },
        initialPrompts: [{ role: "system", content: "Propose one read-only SPARQL SELECT query. Never propose UPDATE. Explain briefly." }],
      });
      session = created;
      release.disabled = false;
      status.textContent = "Local AI session ready. It will stay ready for another proposal until released.";
      return created;
    })();
    try { return await creating; } finally { creating = null; }
  }
  check.addEventListener("click", async () => {
    status.textContent = "Checking…";
    try {
      const a = await availability();
      status.textContent = String(a).startsWith("unavailable")
        ? `Chrome reports “${a}”.`
        : a === "available"
        ? "Chrome reports “available”. Generate a proposal when ready."
        : `Chrome reports “${a}”. Generating a proposal will prepare the model after this click.`;
    } catch (e) { status.textContent = `failed: ${e.message}`; }
  });
  ask.addEventListener("click", async () => {
    ask.disabled = true; resultStatus.textContent = ""; out.textContent = "Preparing local AI…";
    try {
      const localSession = await getSession();
      status.textContent = "Local AI is ready. Proposing a query…";
      out.textContent = "Generating a read-only SPARQL proposal…";
      const prompt = `Local dataset profile: ${JSON.stringify(profile)}\nQuestion: ${question.value}`;
      const proposal = await localSession.prompt(prompt);
      resultStatus.textContent = "Proposal below — it has not run a query.";
      out.textContent = String(proposal).trim() || "(The local model returned no proposal.)";
      status.textContent = "Local AI proposal ready. It has not run a query.";
    } catch (e) {
      status.textContent = "Local AI was not ready.";
      out.textContent = `No local AI proposal: ${e.message}`;
    } finally {
      ask.disabled = false;
    }
  });
  release.addEventListener("click", () => {
    session?.destroy?.();
    session = null;
    release.disabled = true;
    status.textContent = "Local AI session released. Chrome may unload the model when no session remains.";
  });
  return root;
}
```

Chrome may download or prepare its managed model after the reader presses a
button; the page does not preload weights. If Chrome says **Pending Assets** in
`chrome://on-device-internals`, it still needs enough free disk space for the
browser-managed model before a session can become available. A later, separate opt-in Gemma
notebook can name and download an exact local model/adaptor artifact. It should
not be hidden as a fallback inside this small browser-capability experiment.
