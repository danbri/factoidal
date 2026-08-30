---
title: "Could browser AI load skills for a local knowledge graph?"
description: "A capability-gated experiment: declarative SPARQL skills, an in-browser AI prompt when Chrome offers one, and a reproducible evidence bundle without sending the local graph away."
layout: hub.njk
series: docs-hub
series_order: 49
vocab: sparql
status: experimental
---

What if an assistant could load a small, explicit skill bundle before helping
with a browser-local knowledge graph? The key is that the skill is data, not
ambient authority: it describes the graph and SPARQL conventions, while the
reader remains in control of any query execution.

```observable-js
kgSkill = ({
  id: "factoidal.local-kg.sparql.v0",
  goal: "Propose a read-only SPARQL SELECT query for the local dataset.",
  constraints: ["Never transmit graph data", "Never issue UPDATE", "Return one query and a short explanation"],
  graphHints: ["RDF terms retain their full IRI identity", "Prefer bounded SELECT queries with LIMIT"],
  version: "0.1",
})
```

```observable-js
aiSkillRunner = {
  const root = html`<div>
    <p><strong>Local-KG AI skill experiment.</strong> Nothing is sent to a service by this notebook.</p>
    <label>Question about a local RDF graph<br><textarea rows="3">Find people and their names.</textarea></label>
    <p><button type="button">Create reproducible request bundle</button> <button type="button" class="ask">Ask browser AI if available</button></p>
    <pre aria-live="polite">Waiting for a question.</pre>
  </div>`;
  const question = root.querySelector("textarea");
  const bundle = root.querySelector("button");
  const ask = root.querySelector(".ask");
  const output = root.querySelector("pre");
  const request = () => ({ skill: kgSkill, question: question.value, provider: "browser LanguageModel", seed: null, note: "Chrome built-in AI does not currently provide a portable seeded-reproducibility contract." });
  bundle.addEventListener("click", () => output.textContent = JSON.stringify(request(), null, 2));
  ask.addEventListener("click", async () => {
    if (!globalThis.LanguageModel?.availability || !globalThis.LanguageModel?.create) {
      output.textContent = "Browser AI is unavailable here. The request bundle above remains reproducible and can be used with a future local provider."; return;
    }
    ask.disabled = true;
    try {
      const availability = await LanguageModel.availability();
      if (availability === "unavailable") throw new Error("LanguageModel reports unavailable");
      const session = await LanguageModel.create({ initialPrompts: [{ role: "system", content: JSON.stringify(kgSkill) }] });
      const result = await session.prompt(`Question: ${question.value}\nPropose only a read-only SPARQL SELECT query and explanation.`);
      output.textContent = JSON.stringify({ request: request(), availability, result }, null, 2);
      session.destroy?.();
    } catch (error) { output.textContent = `Browser AI did not run: ${error.message}`; }
    finally { ask.disabled = false; }
  });
  return root;
}
```

This is deliberately not an agent with arbitrary Web or filesystem access. A
future local KG runner can show the proposed query, its plan and its result as
separate user-confirmed steps. The request bundle records the skill version,
question, provider and any future sampling parameters; a hosted model seed is
useful metadata, but not a universal reproducibility guarantee.
