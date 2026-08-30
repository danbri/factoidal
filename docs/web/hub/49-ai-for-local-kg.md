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
Shardborough. If available, the model proposes a read-only SPARQL query. It
does not receive Turtle files or send data to a cloud service. You may then
review and explicitly run that proposal in this notebook against the same
three browser-local named graphs. The [Shardborough notebook](../50-shardborough-life-sciences/)
continues to own the inspectable graph manifest and its fixed user-run query.

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
  const files = [
    { graph: "urn:kgx:chromosome", file: "chromosome.ttl" },
    { graph: "urn:kgx:sequence_variant", file: "sequence_variant.ttl" },
    { graph: "urn:kgx:disease", file: "disease.ttl" },
  ];
  const root = html`<div><p><strong>1. Check local AI.</strong> <button class="check">Check availability</button> <span class="status" aria-live="polite">Not checked.</span></p><p><strong>2. Ask about the local graph.</strong><br><textarea rows="3">Find sequence variants and their chromosome entities.</textarea></p><p><button class="ask">Propose read-only SPARQL</button> <button class="release" disabled>Release local AI</button></p><p class="result-status" aria-live="polite"></p><pre class="proposal" aria-live="polite">No request made.</pre><details class="runner" hidden><summary><strong>3. Review and run this proposal locally</strong></summary><p>Edit the query if needed. Running fetches the committed named-graph files and evaluates only in this browser.</p><textarea class="candidate" rows="12" spellcheck="false"></textarea><p><button class="run">Run reviewed query locally</button> <span class="run-status" aria-live="polite"></span></p><pre class="run-output" aria-live="polite"></pre></details></div>`;
  const check = root.querySelector(".check"), ask = root.querySelector(".ask"), release = root.querySelector(".release"), status = root.querySelector(".status"), resultStatus = root.querySelector(".result-status"), question = root.querySelector("textarea"), out = root.querySelector(".proposal"), runner = root.querySelector(".runner"), candidate = root.querySelector(".candidate"), run = root.querySelector(".run"), runStatus = root.querySelector(".run-status"), runOutput = root.querySelector(".run-output");
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
        initialPrompts: [{ role: "system", content: "Propose one read-only SPARQL SELECT query. Never propose UPDATE. This dataset has named graphs only: put every triple pattern inside an explicit GRAPH <...> block, using only graph URIs in the supplied profile. Use the supplied prefixes and facts, include LIMIT 20, then explain briefly." }],
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
  function proposalQuery(text) {
    return new RegExp("`{3}(?:sparql)?\\s*([\\s\\S]*?)`{3}", "i").exec(text)?.[1]?.trim() || "";
  }
  function isSafeReadOnly(query) {
    const upper = query.toUpperCase();
    return /\b(SELECT|ASK|CONSTRUCT|DESCRIBE)\b/.test(upper)
      && !/\b(INSERT|DELETE|LOAD|CLEAR|CREATE|DROP|COPY|MOVE|ADD|WITH|USING|SERVICE)\b/.test(upper);
  }
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
      const query = proposalQuery(String(proposal));
      if (query) {
        candidate.value = query;
        runner.hidden = false;
        runStatus.textContent = "Review the extracted query, then choose whether to run it.";
      } else {
        runner.hidden = true;
        runStatus.textContent = "No fenced SPARQL query was found in this proposal.";
      }
      status.textContent = "Local AI proposal ready. It has not run a query.";
    } catch (e) {
      status.textContent = "Local AI was not ready.";
      out.textContent = `No local AI proposal: ${e.message}`;
    } finally {
      ask.disabled = false;
    }
  });
  run.addEventListener("click", async () => {
    const query = candidate.value.trim();
    if (!isSafeReadOnly(query)) {
      runStatus.textContent = "Only a reviewed read-only SELECT, ASK, CONSTRUCT, or DESCRIBE query without SERVICE may run here.";
      return;
    }
    run.disabled = true;
    runStatus.textContent = "Fetching the three named graphs and running the reviewed query locally…";
    runOutput.textContent = "";
    try {
      const data = await Promise.all(files.map(async entry => {
        const response = await fetch(new URL("../../../fstar-extracted/lifesci/" + entry.file, location.href));
        if (!response.ok) throw new Error(`${entry.file}: HTTP ${response.status}`);
        return { graph: entry.graph, content: await response.text(), dataFormat: "turtle" };
      }));
      const started = performance.now();
      const result = await Factoidal.queryDataset(data, query, { output: "json" });
      const elapsedMs = Math.round(performance.now() - started);
      runOutput.textContent = JSON.stringify({ elapsedMs, result }, null, 2);
      runStatus.textContent = "Finished locally. No query was sent to a server.";
    } catch (e) {
      runStatus.textContent = "The local query did not complete.";
      runOutput.textContent = e.message;
    } finally {
      run.disabled = false;
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
