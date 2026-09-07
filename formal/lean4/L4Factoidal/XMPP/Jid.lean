/-!
RFC 7622 XMPP Address Format (JID): structural and length well-formedness.

Deliberately does NOT implement PRECIS enforcement (RFC 8264 `IdentifierClass`
for localpart, RFC 8265 `UsernameCaseMapped`/`OpaqueString` profiles) —
that's Unicode normalization, case folding, and disallowed-category checks,
a separate and much larger piece of work. Treat that gap as a stated,
tracked boundary, not a silent omission: see DESIGN.md.
-/

namespace L4Factoidal.XMPP

/-- RFC 7622 §3.1: each JID part (localpart, domainpart, resourcepart) is
at most 1023 octets. -/
def maxPartBytes : Nat := 1023

structure Jid where
  localpart : Option String
  domainpart : String
  resourcepart : Option String
  deriving Repr, DecidableEq

namespace Jid

/-- RFC 7622 bounds are stated in octets, not Unicode codepoints. -/
def byteLength (s : String) : Nat :=
  s.utf8ByteSize

/-- Structural + length well-formedness per RFC 7622 §3.1. Does not check
PRECIS validity of the codepoints themselves (see module header). -/
def isWellFormed (j : Jid) : Bool :=
  let localOk := match j.localpart with
    | none => true
    | some lp => byteLength lp ≥ 1 && byteLength lp ≤ maxPartBytes
  let domainOk := byteLength j.domainpart ≥ 1 && byteLength j.domainpart ≤ maxPartBytes
  let resourceOk := match j.resourcepart with
    | none => true
    | some rp => byteLength rp ≥ 1 && byteLength rp ≤ maxPartBytes
  localOk && domainOk && resourceOk

/-- Structural split only — `[ localpart "@" ] domainpart [ "/" resourcepart ]`,
splitting on the FIRST "/" (resourceparts may themselves contain "/" and
"@") then the FIRST "@" in what remains. No emptiness checks: those are
`parse`'s job. Factored out so `parse` has exactly one guard chain and one
constructor call, which is what makes `parse_some_domain_nonempty` and
`parse_some_localpart_nonempty` below tractable to prove — a nested
match-inside-if-inside-match with several constructor call sites (the
first-draft shape of this function) makes `split`/`cases` produce
unmanageable dependent-elimination goals. -/
def splitParts (s : String) : Option String × String × Option String :=
  let (beforeSlash, resourcepart) :=
    match s.splitOn "/" with
    | [] => (s, none)
    | [single] => (single, none)
    | first :: rest => (first, some (String.intercalate "/" rest))
  let (localpart, domainpart) :=
    match beforeSlash.splitOn "@" with
    | [] => (none, beforeSlash)
    | [single] => (none, single)
    | first :: rest => (some first, String.intercalate "@" rest)
  (localpart, domainpart, resourcepart)

/-- Parse a JID string per the RFC 7622 grammar. Returns `none` on
structural failure: an empty domainpart, or an "@"/"/" with nothing on the
required (non-empty) side of it. -/
def parse (s : String) : Option Jid :=
  let (localpart, domainpart, resourcepart) := splitParts s
  if domainpart.isEmpty then none
  else if localpart.elim false String.isEmpty then none
  else if resourcepart.elim false String.isEmpty then none
  else some ⟨localpart, domainpart, resourcepart⟩

/-- Adversarial-input safety: no matter what string is fed to `parse`, it
never returns a JID with an empty domainpart. A caller that trusts a
`some j` result to have a usable routing domain doesn't need to re-check
it — the type alone doesn't guarantee this (`Jid.domainpart : String`
admits `""`), but this theorem closes that gap for every value `parse`
can actually produce. -/
theorem parse_some_domain_nonempty (s : String) (j : Jid) :
    parse s = some j → j.domainpart.isEmpty = false := by
  unfold parse
  split
  split <;> (try split) <;> (try split) <;> intro h <;>
    (try injection h with h) <;> (try subst h) <;> simp_all

/-- Companion to `parse_some_domain_nonempty`: a present localpart is
never the empty string either — an attacker can't smuggle an empty-but-
present localpart past `parse` by, say, sending `"@example.com"`. -/
theorem parse_some_localpart_nonempty (s : String) (j : Jid) (lp : String) :
    parse s = some j → j.localpart = some lp → lp.isEmpty = false := by
  unfold parse
  split
  split <;> (try split) <;> (try split) <;> intro h hj <;>
    (try injection h with h) <;> (try subst h) <;> simp_all

/-- Companion to `parse_some_domain_nonempty`: same guarantee for a
present resourcepart. -/
theorem parse_some_resourcepart_nonempty (s : String) (j : Jid) (rp : String) :
    parse s = some j → j.resourcepart = some rp → rp.isEmpty = false := by
  unfold parse
  split
  split <;> (try split) <;> (try split) <;> intro h hj <;>
    (try injection h with h) <;> (try subst h) <;> simp_all

/-- Render a JID back to string form. -/
def render (j : Jid) : String :=
  let withLocal := match j.localpart with
    | some lp => lp ++ "@" ++ j.domainpart
    | none => j.domainpart
  match j.resourcepart with
    | some rp => withLocal ++ "/" ++ rp
    | none => withLocal

instance : ToString Jid := ⟨render⟩

end Jid

end L4Factoidal.XMPP
