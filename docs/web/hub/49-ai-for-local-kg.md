---
title: "AI beside a local knowledge graph"
description: "A small, optional browser-AI experiment: check availability, ask a question about the life-sciences Shardborough, and inspect a proposed read-only SPARQL query."
layout: hub.njk
series: docs-hub
series_order: 49
vocab: sparql
status: experimental
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
  const root = html`<div><p><strong>1. Check local AI.</strong> <button class="check">Check availability</button> <span class="status" aria-live="polite">Not checked.</span></p><p><strong>2. Ask about the local graph.</strong><br><textarea rows="3">Find sequence variants and their chromosome entities.</textarea></p><p><button class="ask">Propose read-only SPARQL</button></p><pre aria-live="polite">No request made.</pre></div>`;
  const check = root.querySelector(".check"), ask = root.querySelector(".ask"), status = root.querySelector(".status"), question = root.querySelector("textarea"), out = root.querySelector("pre");
  async function availability() {
    if (!globalThis.LanguageModel?.availability || !globalThis.LanguageModel?.create) return "unavailable (this browser exposes no LanguageModel API)";
    return await LanguageModel.availability(languageOptions);
  }
  check.addEventListener("click", async () => { status.textContent = "Checking…"; try { status.textContent = await availability(); } catch (e) { status.textContent = `failed: ${e.message}`; } });
  ask.addEventListener("click", async () => {
    ask.disabled = true; out.textContent = "Preparing local AI…";
    let clock = null, giveUp = null;
    try {
      const a = await availability(); if (a === "unavailable") throw new Error(a);
      status.textContent = a === "available" ? "Chrome reports the model available; creating a local session…" : "Preparing Chrome's local AI model…";
      const controller = new AbortController();
      let seconds = 0;
      clock = setInterval(() => {
        seconds += 5;
        status.textContent = `Creating local AI session… ${seconds}s (Chrome reported ${a})`;
      }, 5000);
      giveUp = setTimeout(() => controller.abort(), 60000);
      const session = await LanguageModel.create({
        ...languageOptions,
        signal: controller.signal,
        monitor(monitor) {
          monitor.addEventListener("downloadprogress", event => {
            status.textContent = `Downloading Chrome's local AI model: ${Math.round(event.loaded * 100)}%`;
          });
        },
        initialPrompts: [{ role: "system", content: "Propose one read-only SPARQL SELECT query. Never propose UPDATE. Explain briefly." }],
      });
      status.textContent = "Local AI is ready. Proposing a query…";
      const prompt = `Local dataset profile: ${JSON.stringify(profile)}\nQuestion: ${question.value}`;
      const proposal = await session.prompt(prompt);
      out.textContent = JSON.stringify({ provider: "Chrome LanguageModel", availability: a, expectedInputs: ["text/en"], expectedOutputs: ["text/en"], graphProfile: profile, question: question.value, proposal, execution: "not run; copy it to Shardborough only after review" }, null, 2);
      status.textContent = "Local AI proposal ready. It has not run a query.";
      session.destroy?.();
    } catch (e) {
      const timedOut = e?.name === "AbortError";
      status.textContent = timedOut ? "Chrome did not create a local session within one minute." : "Local AI was not ready.";
      out.textContent = timedOut
        ? "Chrome reported the model available, but session creation timed out. Open chrome://on-device-internals, check Model Status and free-space requirements, then retry."
        : `No local AI proposal: ${e.message}`;
    } finally {
      if (clock) clearInterval(clock);
      if (giveUp) clearTimeout(giveUp);
      ask.disabled = false;
    }
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
