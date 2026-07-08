---
title: "Validating data: JSON Schema and XForms recalculation"
description: "A draft-07 JSON Schema accepting one instance and rejecting another, and an XForms bind's calculate MIP deriving one leaf from two others on a live recalculation pass — two verified F* engines for checking and deriving data, running in your browser."
layout: hub.njk
series: docs-hub
series_order: 29
vocab: none
status: published
tests: tests/hub/post29_test.mjs
---

Two more engines that check or derive data rather than query it:
**JSON Schema** draft-07 structural validation
([`JSONSchema.Validate.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/JSONSchema.Validate.fst))
and **XForms** bind recalculation
([`XForms.Bind.fst`](https://github.com/danbri/factoidal/blob/claude/main/formal/fstar/XForms.Bind.fst)),
the "spreadsheet half" of XForms — an instance document plus a bind sheet
of `calculate`/`constraint`/`type` expressions, recomputed in dependency
order. Both run live below.

## JSON Schema: accept, then reject

One schema, `required: ["name"]`:

```observable-js
abi = await Factoidal.loadNpmEntry()
```

```observable-js
personSchema = JSON.stringify({
  type: "object",
  required: ["name"],
  properties: { name: { type: "string" } },
})
```

```observable-js
schemaAccept = {
  const raw = JSON.parse(abi.jsonSchemaValidate(personSchema, JSON.stringify({ name: "Alice" })));
  if (!raw.ok) throw new Error(raw.error);
  return raw;
}
```

`{ valid: true, result: "pass", errors: [] }` — `{name: "Alice"}` has the
one required property, of the right type. Drop it:

```observable-js
schemaReject = {
  const raw = JSON.parse(abi.jsonSchemaValidate(personSchema, JSON.stringify({})));
  if (!raw.ok) throw new Error(raw.error);
  return raw;
}
```

`{ valid: false, result: "fail", errors: [...] }` — the empty object is
missing `name`, so `JSONSchema_Validate.validate` returns `VFail` rather
than `VPass`. A schema keyword this validator doesn't yet implement
returns a third, distinct outcome, `"unsupported"` — never silently
folded into `pass`.

## XForms: a calculate MIP deriving a leaf

An instance with two inputs and one derived leaf, and a single bind
naming `sum`'s `calculate` expression:

```observable-js
xformsInstance = "<data><a>2</a><b>3</b><sum>0</sum></data>"
```

```observable-js
xformsResult = {
  const binds = JSON.stringify([{ target: "sum", calculate: "../a + ../b" }]);
  const raw = JSON.parse(abi.xformsRecalc(xformsInstance, binds));
  if (!raw.ok) throw new Error(raw.error);
  return raw;
}
```

The recalculated instance carries `<sum>5</sum>` — `../a + ../b`
evaluated with the `sum` leaf itself as the XPath context node, so `../`
steps back up to its siblings. `XForms_Bind.recalculate` topologically
sorts binds by which instance nodes their `calculate` expressions read
before running any of them, so a `calculate` graph with a cycle is
rejected as a document error rather than looped forever — there's no
bind here that depends on `sum` itself, but a `binds` list that did would
fail the same way `jsonSchemaValidate` fails an instance: cleanly, with
a reason, not a hang.

Every live cell above is pinned in
[`tests/hub/post29_test.mjs`](https://github.com/danbri/factoidal/blob/claude/main/tests/hub/post29_test.mjs).
