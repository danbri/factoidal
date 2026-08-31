/- Build-time checks for the parsed Update -> durable-delta admission seam. -/
import L4Factoidal.SPARQL.UpdateDelta
import L4Factoidal.SPARQL.UpdateParser

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF
open L4Factoidal.Storage

private def unchangedBnode (b : BNodeId) : BNodeId := b

private def insertRequest :=
  parseSparqlUpdate "INSERT DATA { <http://example.org/s> <http://example.org/p> \"v\" . }"

private def deleteRequest :=
  parseSparqlUpdate "DELETE DATA { GRAPH <http://example.org/g> { <http://example.org/s> <http://example.org/p> \"v\" . } }"

#guard match insertRequest with
  | .ok request => match deltaBatchForUpdate? 4 2 unchangedBnode request with
    | some batch => batch.seq == 4 && batch.epoch == 2 && batch.ops.length == 1 &&
      (parseDeltaBatch (serializeDeltaBatch batch)).map (fun p => p.1) == some batch
    | none => false
  | .error _ => false

#guard match deleteRequest with
  | .ok request => match deltaEntriesForUpdate? unchangedBnode request with
    | some [.remove _ (some "http://example.org/g")] => true
    | _ => false
  | .error _ => false

/- WHERE-dependent update forms remain explicit non-admissions at this disk
   boundary; none may turn into a partial or silently omitted delta. -/
#guard match parseSparqlUpdate "DELETE { ?s <http://example.org/p> ?o } WHERE { ?s <http://example.org/p> ?o }" with
  | .ok request => (deltaEntriesForUpdate? unchangedBnode request).isNone
  | .error _ => false

end L4Factoidal.SPARQL
