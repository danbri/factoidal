/-
L4Factoidal.SPARQL.ProtocolTheorems — structural theorems about the
protocol-shaped modules.

  * `percentDecode_percentEncode_ascii` — percent-decoding inverts
    percent-encoding on every ASCII string, which covers the RFC 3986
    §2.2 reserved set (`:/?#[]@!$&'()*+,;=`), the §2.3 unreserved set
    and `%` itself. (Non-ASCII characters round-trip too — pinned by
    `#guard`s in `ProtocolTests.lean` — but their proof would go
    through `String.utf8EncodeChar`, which this stage does not open.)
  * `decodeRequest_get_no_query` — a GET whose query string carries
    no `query=` parameter is a 400-class verdict (Protocol §2.1.1:
    the `query` parameter is required; §2.2.2: `update=` via GET is
    rejected too, so no other parameter can rescue it).
  * `decodeTarget_malformed_graph` — an indirect graph identification
    (GSP §4.1) whose `graph=` value is not an IRI is a 400.

Axiom audit at the end: propext / Classical.choice / Quot.sound only.
No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.Protocol
import L4Factoidal.SPARQL.GraphStore

namespace L4Factoidal.SPARQL.ProtocolTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL.Protocol
open L4Factoidal.SPARQL.GraphStore

/-! ## Hex digits -/

theorem hexValue_hexDigitUpper : ∀ n, n < 16 → hexValue (hexDigitUpper n) = n := by decide

theorem isHexDigit_hexDigitUpper : ∀ n, n < 16 → isHexDigit (hexDigitUpper n) = true := by decide

/-- `%XX` for a byte value decodes back to that byte. -/
theorem pctUnits_percentEncodeByte (p : Bool) (b : Nat) (hb : b < 256) (rest : List Char) :
    pctUnits p (percentEncodeByte b ++ rest) = .byte b :: pctUnits p rest := by
  have h1 := hexValue_hexDigitUpper (b / 16) (by omega)
  have h2 := hexValue_hexDigitUpper (b % 16) (by omega)
  have h3 := isHexDigit_hexDigitUpper (b / 16) (by omega)
  have h4 := isHexDigit_hexDigitUpper (b % 16) (by omega)
  simp [percentEncodeByte, pctUnits, h1, h2, h3, h4]
  omega

/-- A character other than `%` (and, under URL decoding, `+` is not
special) is its own unit. -/
theorem pctUnits_cons_nonpct (c : Char) (hc : c ≠ '%') (rest : List Char) :
    pctUnits false (c :: rest) = .ch c :: pctUnits false rest := by
  have hc' : (c == '%') = false := beq_eq_false_iff_ne.mpr hc
  conv => lhs; unfold pctUnits
  simp [hc']

theorem utf8Assemble_ch (c : Char) (rest : List PctUnit) :
    utf8Assemble (.ch c :: rest) = c :: utf8Assemble rest := by
  rw [utf8Assemble]

theorem utf8Assemble_ascii (b : Nat) (hb : b < 128) (rest : List PctUnit) :
    utf8Assemble (.byte b :: rest) = Char.ofNat b :: utf8Assemble rest := by
  conv => lhs; unfold utf8Assemble
  simp [hb]

theorem isUnreserved_ne_pct (c : Char) (hu : isUnreserved c = true) : c ≠ '%' := by
  intro heq
  subst heq
  simp [isUnreserved] at hu

/-- Percent-decoding inverts percent-encoding on ASCII input. -/
theorem percentDecode_percentEncode_ascii :
    ∀ cs : List Char, (∀ c ∈ cs, c.toNat < 128) →
      percentDecodeChars false (percentEncodeChars cs) = cs
  | [], _ => by simp [percentDecodeChars, percentEncodeChars, pctUnits, utf8Assemble]
  | c :: cs, h => by
    have hc : c.toNat < 128 := h c (by simp)
    have ih := percentDecode_percentEncode_ascii cs (fun d hd => h d (by simp [hd]))
    unfold percentDecodeChars at ih ⊢
    have hsplit : percentEncodeChars (c :: cs) = percentEncodeChar c ++ percentEncodeChars cs := by
      simp [percentEncodeChars]
    rw [hsplit]
    by_cases hu : isUnreserved c = true
    · have hne := isUnreserved_ne_pct c hu
      rw [show percentEncodeChar c = [c] by simp [percentEncodeChar, hu], List.singleton_append,
          pctUnits_cons_nonpct c hne, utf8Assemble_ch, ih]
    · rw [show percentEncodeChar c = percentEncodeByte c.toNat by simp [percentEncodeChar, hu, hc],
          pctUnits_percentEncodeByte false c.toNat (by omega), utf8Assemble_ascii c.toNat hc, ih,
          Char.ofNat_toNat]

/-- The string-level corollary. -/
theorem urlDecode_percentEncode_ascii (s : String) (h : ∀ c ∈ s.toList, c.toNat < 128) :
    urlDecode (percentEncode s) = s := by
  unfold urlDecode percentEncode
  rw [String.toList_ofList, percentDecode_percentEncode_ascii s.toList h, String.ofList_toList]

/-! ## A GET without `query=` is a 400-class verdict -/

theorem collectValues_nil_of_absent (key : String) (kvs : List (String × String))
    (h : ∀ kv ∈ kvs, kv.1 ≠ key) : collectValues key kvs = [] := by
  unfold collectValues
  rw [List.filterMap_eq_nil_iff]
  intro kv hkv
  simp [h kv hkv]

theorem buildFromKvs_get_no_query (isUpdatePath : Bool) (kvs : List (String × String))
    (h : ∀ kv ∈ kvs, kv.1 ≠ "query") : (buildFromKvs true isUpdatePath kvs).isBad = true := by
  have hq : collectValues "query" kvs = [] := collectValues_nil_of_absent _ _ h
  unfold buildFromKvs
  simp only [hq, firstValue, List.length_nil, List.head?_nil]
  split
  · omega
  · split
    · rfl
    · cases (collectValues "update" kvs).head? with
      | none => cases isUpdatePath <;> rfl
      | some u => rfl

/-- Protocol §2.1.1: `query` is a required parameter of the query
operation; a GET request without it is rejected. -/
theorem decodeRequest_get_no_query (path qs contentType body : String)
    (h : ∀ kv ∈ parseQueryString (effectiveQs path qs).2, kv.1 ≠ "query") :
    (decodeRequest "GET" path qs contentType body).isBad = true := by
  have hm : asciiLower "GET" = "get" := by decide
  unfold decodeRequest
  simp only [hm, beq_self_eq_true, if_true]
  exact buildFromKvs_get_no_query _ _ h

/-! ## GSP: a malformed `graph=` is a 400 -/

/-- GSP §4.1: an indirect identification whose `graph` value is not
an IRI (empty, or without a scheme colon) is a Bad Request. -/
theorem decodeTarget_malformed_graph (path qs g : String)
    (hkv : parseQueryString qs = [("graph", g)]) (hg : isIri g = false) :
    decodeTarget path qs = .error 400 := by
  simp [decodeTarget, hkv, firstValue, collectValues, hg]

/-! ## Axiom audit -/

#print axioms percentDecode_percentEncode_ascii
#print axioms urlDecode_percentEncode_ascii
#print axioms decodeRequest_get_no_query
#print axioms decodeTarget_malformed_graph

end L4Factoidal.SPARQL.ProtocolTheorems
