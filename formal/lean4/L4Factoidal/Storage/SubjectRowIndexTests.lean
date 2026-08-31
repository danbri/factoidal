import L4Factoidal.Storage.SubjectRowIndex

namespace L4Factoidal.Storage.SubjectRowIndex

open L4Factoidal.Storage.IndexedBlock

private def sampleRows : Array IdTriple :=
  #[{ s := 7, p := 2, o := 10 }, { s := 9, p := 2, o := 11 },
    { s := 7, p := 2, o := 12 }]

#guard (lookup (build sampleRows) 7) == [0, 2]
#guard (lookup (build sampleRows) 9) == [1]
#guard (lookup (build sampleRows) 8) == []
#guard (rowsForSubject sampleRows (build sampleRows) 7) ==
  [{ s := 7, p := 2, o := 10 }, { s := 7, p := 2, o := 12 }]

end L4Factoidal.Storage.SubjectRowIndex
