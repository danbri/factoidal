import L4Factoidal.Storage.SubjectRowIndexWire

namespace L4Factoidal.Storage.SubjectRowIndexWire

open L4Factoidal.Storage.IndexedBlock

private def rows : Array IdTriple :=
  #[{ s := 7, p := 2, o := 10 }, { s := 9, p := 2, o := 11 },
    { s := 7, p := 2, o := 12 }]

#guard pairsOfRows rows == [(7, 0), (7, 2), (9, 1)]
#guard (encode? rows).bind decode == some (3, [(7, 0), (7, 2), (9, 1)])
#guard (encode? rows).map (fun bytes => (decode bytes).map (fun value => offsetsFor value.2 7)) == some (some [0, 2])
#guard (encode? rows).map (fun bytes => (decode (bytes.extract 0 (bytes.size - 1))).isNone) == some true

end L4Factoidal.Storage.SubjectRowIndexWire
