(* fstar_hacl_crypto.ml — realises the VC.DataIntegrity crypto assume-vals
   via the vendored HACL* extracted C (third_party/hacl/, Ed25519 + SHA-256).

   Crypto sourcing policy: skills/crypto-policy/SKILL.md — never hand-roll a
   digest/curve/signature primitive; HACL* is the sanctioned source.  This
   module is an iron-rule-#11(c) ASSUME-CRYPTO realisation: pure host-call-outs
   to the vendored HACL* C (declared `external`, implemented in
   experimental_ocaml_glue/hacl_stubs.c).  No cryptographic logic lives here;
   the hex marshalling is in the C stub.  Same role fstar_pure_hashes.ml plays
   for the SPARQL/RDFC hash assume-vals.  On NATIVE the `external caml_hacl_*`
   below bind to the vendored HACL* C.  Under js_of_ocaml/Node the SAME
   primitives are realised by ocaml-output/hacl_stubs.js over HACL*'s OWN
   official WebAssembly build (third_party/hacl-wasm/, loaded by
   npm/factoidal/hacl-init.js), so VC crypto works off-native too
   (GitHub #286; wasm_of_ocaml target tracked there).

   Boundary: hex strings, lowercase, no 0x prefix.  An empty-string return
   from a keyed operation signals a malformed-length input, never a verdict. *)

external caml_hacl_sha256 : string -> string
  = "caml_hacl_sha256"
external caml_hacl_ed25519_secret_to_public : string -> string
  = "caml_hacl_ed25519_secret_to_public"
external caml_hacl_ed25519_sign : string -> string -> string
  = "caml_hacl_ed25519_sign"
external caml_hacl_ed25519_verify : string -> string -> string -> bool
  = "caml_hacl_ed25519_verify"

(* SHA-256 of the UTF-8 bytes of [s]; returns a 64-char lowercase hex digest.
   Same contract as Fstar_pure_hashes.sha256, but HACL*-backed. *)
let sha256_hex (s : string) : string = caml_hacl_sha256 s

let ed25519_secret_to_public (sk_hex : string) : string =
  caml_hacl_ed25519_secret_to_public sk_hex

let ed25519_sign (sk_hex : string) (msg_hex : string) : string =
  caml_hacl_ed25519_sign sk_hex msg_hex

let ed25519_verify (pk_hex : string) (msg_hex : string) (sig_hex : string) : bool =
  caml_hacl_ed25519_verify pk_hex msg_hex sig_hex
