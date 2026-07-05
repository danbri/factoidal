open Prims
(* Issue #275: rule-#11 ASSUME-IO realisation -- one shared dispatch
   shape for every consumer binary (precedent:
   57_service_client_bind.sh's service_endpoint_table/_register).
   Default (nothing registered) is an honest None: a consumer that
   never calls jsonld_loader_register gets the same "no remote
   loading" behavior it had before this patch existed. *)
let jsonld_loader_ref
  : (Prims.string -> Prims.string FStar_Pervasives_Native.option) ref =
  ref (fun (uu___ : Prims.string) -> FStar_Pervasives_Native.None)
let jsonld_loader_register
    (f : Prims.string -> Prims.string FStar_Pervasives_Native.option) : unit =
  jsonld_loader_ref := f
let jsonld_load_document (iri : Prims.string) :
  Prims.string FStar_Pervasives_Native.option=
  (!jsonld_loader_ref) iri
