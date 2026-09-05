/-
L4Factoidal.Storage.PagedTermDictionaryV2Theorems — the PTD2 round trip.

    encode? terms = some bytes → decode? bytes = some terms

on the subset `encode?` admits, with no further hypothesis.

There is no proof here either. PTD2 is
`L4Factoidal.Storage.PagedTermDictionaryCore` at
`PagedTermDictionaryV2.v2Format`, and the round trip is
`PTD.decode?_encode?` at that format. PTD1 is the same generic theorem at
`PagedTermDictionary.v1Format`. The page layout is proved once.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.PagedTermDictionaryV2
import L4Factoidal.Storage.PagedTermDictionaryCoreTheorems

namespace L4Factoidal.Storage.PagedTermDictionaryV2

open L4Factoidal.Storage.TermWireV2

/-- `decode?` admits exactly the artifacts `decodeSpec?` admits and
returns the same term array. -/
theorem decode?_eq_spec (bytes : ByteArray) : decode? bytes = decodeSpec? bytes :=
  PTD.decode?_eq_spec v2Format bytes

/-- The PTD2 codec round trip for the list specification. -/
theorem decodeSpec?_encode? (terms : Array WireTerm)
    (bytes : ByteArray) (h : encode? terms = some bytes) :
    decodeSpec? bytes = some terms := PTD.decodeSpec?_encode? v2Format terms bytes h

/-- The PTD2 codec round trip: whatever `encode?` accepts, `decode?`
returns unchanged, as the same `Array WireTerm` in the same order. -/
theorem decode?_encode? (terms : Array WireTerm)
    (bytes : ByteArray) (h : encode? terms = some bytes) :
    decode? bytes = some terms := PTD.decode?_encode? v2Format terms bytes h

/-- The fixed prefix decodes to the header the encoder wrote. -/
theorem decodePrefix_ok (t p c : Nat) (ht : t < UInt32.size) (hp0 : 0 < p)
    (hp : p < UInt32.size) (hc : c < UInt32.size) (hcc : c = (t + p - 1) / p) :
    decodePrefix (byteArrayOfList (writeU32LE magic ++ [version] ++
        writeU32LE (UInt32.ofNat t) ++ writeU32LE (UInt32.ofNat p) ++
        writeU32LE (UInt32.ofNat c)))
      = some { termCount := t, pageTerms := p, pageCount := c } :=
  PTD.decodePrefix_ok v2Format t p c ht hp0 hp hc hcc

#print axioms decodePrefix_ok
#print axioms decode?_eq_spec
#print axioms decodeSpec?_encode?
#print axioms decode?_encode?

end L4Factoidal.Storage.PagedTermDictionaryV2
