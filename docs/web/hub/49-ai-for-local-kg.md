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
  const options = { outputLanguage: "en" };
  const root = html`<div><p><strong>1. Check local AI.</strong> <button class="check">Check availability</button> <span class="status">Not checked.</span></p><p><strong>2. Ask about the local graph.</strong><br><textarea rows="3">Find sequence variants and their chromosome entities.</textarea></p><p><button class="ask">Propose read-only SPARQL</button></p><pre aria-live="polite">No request made.</pre></div>`;
  const check = root.querySelector(".check"), ask = root.querySelector(".ask"), status = root.querySelector(".status"), question = root.querySelector("textarea"), out = root.querySelector("pre");
  async function availability() {
    if (!globalThis.LanguageModel?.availability || !globalThis.LanguageModel?.create) return "unavailable (this browser exposes no LanguageModel API)";
    return await LanguageModel.availability(options);
  }
  check.addEventListener("click", async () => { status.textContent = "Checking…"; try { status.textContent = await availability(); } catch (e) { status.textContent = `failed: ${e.message}`; } });
  ask.addEventListener("click", async () => {
    ask.disabled = true; out.textContent = "Preparing local AI…";
    try {
      const a = await availability(); if (a === "unavailable") throw new Error(a);
      const session = await LanguageModel.create({ ...options, initialPrompts: [{ role: "system", content: "Propose one read-only SPARQL SELECT query. Never propose UPDATE. Explain briefly." }] });
      const prompt = `Local dataset profile: ${JSON.stringify(profile)}\nQuestion: ${question.value}`;
      const proposal = await session.prompt(prompt);
      out.textContent = JSON.stringify({ provider: "Chrome LanguageModel", availability: a, outputLanguage: "en", graphProfile: profile, question: question.value, proposal, execution: "not run; copy it to Shardborough only after review" }, null, 2);
      session.destroy?.();
    } catch (e) { out.textContent = `No local AI proposal: ${e.message}`; } finally { ask.disabled = false; }
  });
  return root;
}
```

Chrome may download or prepare its managed model after the reader presses a
button; the page does not preload weights. A later, separate opt-in Gemma
notebook can name and download an exact local model/adaptor artifact. It should
not be hidden as a fallback inside this small browser-capability experiment.
