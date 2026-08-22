/-
L4Factoidal.JSONLD.Theorems — proved properties of the JSON-LD port.

Every theorem here is proved outright: no `sorry`, no user `axiom`, no
`native_decide`, no `partial`. `Tests.lean`'s companion audit lines and
the `#print axioms` block at the end of this file show the trusted base
is exactly Lean's own (`propext`, `Classical.choice`, `Quot.sound`).

Scope is deliberately the CHEAP end of the ladder: identities and
invariants of §5.2.2 IRI Expansion, §4.2 Create Term Definition, and the
blank-node issuer, plus the one property the `jsonld-context-cache`
skill singles out as a rule with teeth — that an unresolvable remote
context yields an ERROR, never an empty context. Nothing here claims
conformance; that is what the toRdf probe measures.
-/
import L4Factoidal.JSONLD.ToRdf
import L4Factoidal.RDF.CanonicalTheorems

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-! ## §5.2.2 IRI Expansion -/

/-- **A keyword expands to itself.** JSON-LD 1.1 API §5.2.2 step 2: "If
value is a keyword … return value as is". Holds in both `vocab` modes
and under both the expansion-time and context-processing entry points,
because the keyword test precedes every term and prefix lookup. -/
theorem expandIri_keyword (ac : ActiveContext) (v : String) (vocab inCtx : Bool)
    (hne : (slen v == 0) = false) (hkw : actualKeyword v = true) :
    expandIriGen ac v vocab inCtx = some v := by
  unfold expandIriGen
  simp [hne, hkw]

/-- **A term defined as a keyword alias expands to that keyword.**
JSON-LD 1.1 API §5.2.2 step 4 ("if active context has a term definition
for value, return the associated IRI mapping") composed with §4.2's
storage of an aliased keyword as the term's IRI mapping. Vocab-relative
only, which is exactly the spec's condition. -/
theorem expandIri_keyword_alias (ac : ActiveContext) (t kw : String) (inCtx : Bool)
    (td : TermDef)
    (hne : (slen t == 0) = false) (hkw : actualKeyword t = false)
    (hfind : findTerm ac.terms t = some td) (hiri : td.iri = kw) :
    expandIriGen ac t true inCtx = some kw := by
  unfold expandIriGen
  simp [hne, hkw, hfind, hiri]

/-- **An absolute IRI with an authority component is the identity.**
JSON-LD 1.1 API §5.2.2's compact-IRI step returns `value` unchanged once
the prefix is not a term ("if … the prefix is not a term in the active
context, return value as is"); the `//` after the scheme colon is what
makes it an ordinary absolute IRI rather than a compact one. Stated with
the guards the algorithm itself checks, in the order it checks them. -/
theorem expandIri_absolute_authority (ac : ActiveContext) (v : String)
    (vocab inCtx : Bool) (c : Nat)
    (hne : (slen v == 0) = false)
    (hkw : actualKeyword v = false)
    (hterm : (if vocab then findTerm ac.terms v else none) = none)
    (hform : keywordForm v = false)
    (hc : findColon v = some c) (hc0 : (c == 0) = false)
    (hpre : (substr v 0 c == "_") = false)
    (hsch : (v.toList.take c).all isSchemeChar = true)
    (hs1 : charAtD v (c + 1) = '/') (hs2 : charAtD v (c + 2) = '/') :
    expandIriGen ac v vocab inCtx = some v := by
  have hsub : (substr v 0 c).toList = v.toList.take c := by
    simp [substr]
  unfold expandIriGen
  simp only [hne, hkw, hform, hc, hc0, hpre, hs1, hs2]
  simp [hterm, hsub, hsch]

/-- **With no `@vocab` and no `@base`, nothing relative resolves.** The
fallback of §5.2.2 (steps 5 and 6) has nothing to concatenate onto or
resolve against. -/
theorem expandFallback_none (ac : ActiveContext) (value : String) (vocab : Bool)
    (hv : ac.vocab = none) (hb : ac.base = none) :
    expandFallback ac value vocab = none := by
  unfold expandFallback
  cases vocab <;> simp [hv, hb]

/-! ## §4.2 Create Term Definition -/

/-- **Definition compatibility is reflexive.** A term redefined by an
IDENTICAL definition is always the same definition, which is what makes
§4.2's protected-term rule admit a repeated declaration. -/
theorem termDefsCompatible_refl (a : TermDef) : termDefsCompatible a a = true := by
  simp [termDefsCompatible]

/-- **A protected term redefined identically keeps its OLD definition.**
JSON-LD 1.1 API §4.2: "Set definition to previous definition to retain
the value of protected". This is what stops a later, still-compatible
redefinition that omits `@protected` from silently unprotecting the
term. -/
theorem resolveRedefine_protected_identical (ac : ActiveContext) (key : String)
    (existing : TermDef) (hfind : findTerm ac.terms key = some existing)
    (hprot : existing.protected_ = true) :
    resolveRedefine ac key existing false = .ok existing := by
  simp [resolveRedefine, hfind, hprot, termDefsCompatible_refl]

/-- **A protected term redefined DIFFERENTLY is the named error.** Same
step of §4.2, the failing branch — and the error carries its code, which
the F* source's bare `option` cannot. -/
theorem resolveRedefine_protected_incompatible (ac : ActiveContext) (key : String)
    (existing newTd : TermDef) (hfind : findTerm ac.terms key = some existing)
    (hprot : existing.protected_ = true)
    (hincompat : termDefsCompatible existing newTd = false) :
    resolveRedefine ac key newTd false = .error .protectedTermRedefinition := by
  simp [resolveRedefine, hfind, hprot, hincompat]

/-- **An undefined term is defined by the new definition.** The ordinary
"later wins" rule of §4.2, with nothing to protect. -/
theorem resolveRedefine_fresh (ac : ActiveContext) (key : String) (newTd : TermDef)
    (over : Bool) (hfind : findTerm ac.terms key = none) :
    resolveRedefine ac key newTd over = .ok newTd := by
  simp [resolveRedefine, hfind]

/-- **`override protected` always admits the new definition.** The right
of a property-scoped context (§5.1) to replace a protected term. -/
theorem resolveRedefine_override (ac : ActiveContext) (key : String) (newTd : TermDef) :
    ∃ r, resolveRedefine ac key newTd true = .ok r := by
  unfold resolveRedefine
  cases h : findTerm ac.terms key with
  | none => exact ⟨newTd, rfl⟩
  | some existing => simp

/-- **Removing a term makes it unfindable.** The `defined[term] = false`
guard of §4.2 is implemented by stripping the entry before expanding the
term's own `@id`; this is what makes that strip effective. -/
theorem findTerm_removeTerm (terms : List (String × TermDef)) (name : String) :
    findTerm (removeTerm terms name) name = none := by
  unfold findTerm removeTerm
  cases h : (terms.filter (fun kv => kv.1 != name)).find? (fun kv => kv.1 == name) with
  | none => rfl
  | some kv =>
      exfalso
      -- The entry `find?` returned satisfies BOTH the `find?` predicate
      -- (its key IS `name`) and the `filter` predicate it survived (its
      -- key is NOT `name`).
      have hmem := List.find?_some h
      have hin := List.mem_of_find?_eq_some h
      rw [List.mem_filter] at hin
      have hne := hin.2
      simp only [beq_iff_eq] at hmem
      simp only [bne_iff_ne, ne_eq, hmem, not_true_eq_false] at hne

/-! ## The active context's pop chain

The F* source spells the pop target as a self-referential
`ac_previous : option active_context` field; this port uses an explicit
stack (Lean structures are not recursive). These three theorems are what
make the two representations agree. -/

/-- **A context with no pop target pops to itself** — the F* `None`
case of `match ac.ac_previous with Some prev -> prev | None -> ac`. -/
theorem pop_no_prev (ac : ActiveContext) (h : ac.prev = []) : ac.pop = ac := by
  unfold ActiveContext.pop
  rw [h]

/-- **Popping after `setPrev` lands exactly on the target.** The F*
`Some prev` case: `{ ac with ac_previous = Some target }` then popping
yields `target`. -/
theorem pop_setPrev (ac target : ActiveContext) : (ac.setPrev target).pop = target := by
  unfold ActiveContext.setPrev ActiveContext.pop
  rfl

/-- **`clearPrev` removes the pop target**, so the result pops to
itself — the F* `{ ac with ac_previous = None }`. -/
theorem pop_clearPrev (ac : ActiveContext) : ac.clearPrev.pop = ac.clearPrev := by
  unfold ActiveContext.clearPrev ActiveContext.pop
  rfl

/-! ## The blank-node issuer — §8.2 "generate blank node identifier" -/

/-- **The issuer's counter strictly increases.** -/
theorem freshBnode_counter (ctr : Nat) : (freshBnode ctr).2 = ctr + 1 := rfl

/-- **The issuer is injective.** Two different counter values never
produce the same blank node identifier, so the labels §8.2 mints for
distinct nodes are distinct. Reuses `RDF.Canonical.mkLabel_inj` — this
port builds its labels with the very function RDFC-1.0 canonicalization
already proved injective, rather than a parallel one. -/
theorem freshBnode_injective {m n : Nat} (h : (freshBnode m).1 = (freshBnode n).1) : m = n :=
  L4Factoidal.RDF.Canonical.mkLabel_inj h

/-- Contrapositive, in the form a reader wants: distinct counters give
distinct labels. -/
theorem freshBnode_distinct {m n : Nat} (h : m ≠ n) : (freshBnode m).1 ≠ (freshBnode n).1 :=
  fun heq => h (freshBnode_injective heq)

/-! ## The banned empty-context fallback

`skills/jsonld-context-cache/SKILL.md` states the rule; this is the
rule as a theorem. A silently-empty context expands a document with
every term unmapped — a wrong answer that looks like a right one — so
the failure has to be a failure. -/

/-- **A loader that resolves nothing yields the spec's error, never an
empty context.** JSON-LD 1.1 API §4.1's `loading remote context failed`. -/
theorem fetchRemoteContext_none (url : String) :
    fetchRemoteContext Loader.none url = .error .loadingRemoteContextFailed := by
  unfold fetchRemoteContext Loader.none
  rfl

/-- **And so does the whole context-processing algorithm**, for a
context given as a string reference, whatever the fuel and however the
IRI resolves. Nothing downstream can turn the failure into an empty
active context. -/
theorem contextProcess_string_none_loader (ac : ActiveContext) (s : String)
    (over : Bool) (fuel rfuel : Nat) (visited : List String) :
    ∃ e, contextProcess Loader.none ac (.string s) over fuel rfuel visited = .error e := by
  unfold contextProcess
  cases fuel with
  | zero => exact ⟨.contextOverflow, rfl⟩
  | succ f =>
      simp only
      by_cases hr : rfuel == 0
      · exact ⟨.contextOverflow, by simp [hr]⟩
      · cases hres : resolveContextIri ac s with
        | none => exact ⟨.loadingRemoteContextFailed, by simp [hr]⟩
        | some resolved =>
            by_cases hv : resolved ∈ visited
            · exact ⟨.recursiveContextInclusion, by simp [hr, hv]⟩
            · exact ⟨.loadingRemoteContextFailed, by
                simp [hr, hv, fetchRemoteContext, Loader.none]⟩

/-! ## Small structural facts used by the expansion side -/

/-- **`asArray` is the identity on arrays** — expanded form's
array-wrapping is idempotent. -/
theorem asArray_array (items : List Json) : asArray (.array items) = items := rfl

/-- **A `@list` container may not be combined.** JSON-LD 1.1 API §4.2's
`@container` validation, in the shape `containerKindOfFlags` decides
it. -/
theorem containerKindOfFlags_list_alone :
    containerKindOfFlags false false false false false true = some ContainerKind.list := rfl

theorem containerKindOfFlags_list_combined (g i ix lg ty : Bool)
    (h : (g || i || ix || lg || ty) = true) :
    containerKindOfFlags g i ix lg ty true = none := by
  unfold containerKindOfFlags
  simp [h]

/-- **`@import` merging keeps the CONTAINING context's entry on a key
collision.** JSON-LD 1.1 API §4.1: "merging context into import context,
replacing common entries with those from context". -/
theorem mergeImport_local_suffix (imported local_ : List (String × Json)) :
    ∃ pre, mergeImport imported local_ = pre ++ local_ :=
  ⟨imported.filter (fun kv => !local_.any (fun lv => lv.1 == kv.1)), rfl⟩

/-- **Sorting type names preserves how many there are**, so
`applyTypeScopedContexts` visits every named type exactly once. -/
theorem sortStrings_length : ∀ xs : List String, (sortStrings xs).length = xs.length
  | [] => rfl
  | x :: rest => by
      have hins : ∀ (y : String) (ys : List String),
          (insertSorted y ys).length = ys.length + 1 := by
        intro y ys
        induction ys with
        | nil => rfl
        | cons z zs ih =>
            unfold insertSorted
            by_cases h : strLt y z
            · simp [h]
            · simp [h, ih]
      rw [sortStrings, hins, sortStrings_length rest]
      simp

/-! ## Axiom audit

The trusted base must be exactly Lean's own three. Anything else
appearing below is a regression. -/

#print axioms expandIri_keyword
#print axioms expandIri_keyword_alias
#print axioms expandIri_absolute_authority
#print axioms resolveRedefine_protected_identical
#print axioms findTerm_removeTerm
#print axioms pop_setPrev
#print axioms freshBnode_injective
#print axioms fetchRemoteContext_none
#print axioms contextProcess_string_none_loader
#print axioms sortStrings_length

end L4Factoidal.JSONLD
