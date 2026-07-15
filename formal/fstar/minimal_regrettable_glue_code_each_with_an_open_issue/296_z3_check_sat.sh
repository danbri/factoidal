#!/bin/bash
# Issue #296: realise Tableau.CountingOracle.z3_check_sat (rule-#11
# ASSUME-HOST host-engine call-out -- satisfiability is z3's semantics,
# exactly as regex_match's semantics are the host regex engine's).
# https://github.com/danbri/factoidal/issues/296
#
# RETIRED IN PRACTICE (2026-07-15): the verified F* class-size reasoner
# Tableau.CountingOracle.class_size_unsat (a Farkas-certificate validator
# with a build-checked soundness Lemma) is now consulted ONE RUNG BEFORE
# this oracle in owl_runner's InconsistencyTest dispatch. It decides the
# two counting fixtures the oracle ever flipped (dl-910, one=two) inside
# the verified boundary, so they are now plain VERIFIED passes and z3 is
# never reached for them (confirmed under FACTOIDAL_OWL_Z3_RLIMIT=0).
# dl-909 the oracle never flipped (its class-size system is genuinely
# `sat`) and still does not. This realisation is KEPT -- not deleted --
# as the fallback for any future counting fixture the verified reasoner
# does not yet decide, but for the shipped corpus the oracle is
# unreachable. See docs/designissues/2026-07-15-owl2-wave-c-finite-model-
# refutation.md and third_party/z3-native/PROVENANCE.md.
#
# PHASE 1 realisation (Z33kr, docs/designissues/2026-07-14-z3-entailment-
# backend.md, Phase 1 / section 3): spawn the pinned native z3 binary,
# feed the F*-built SMT-LIB 2 string on stdin, parse the first
# sat/unsat/unknown line from stdout to Z3_Sat/Z3_Unsat/Z3_Unknown. This
# is the sanctioned ASSUME-HOST (host decision) + ASSUME-IO (process
# spawn) form -- NO semantics beyond spawn/feed/parse. All the semantic
# content (the counting-fragment encoding) lives in the verified
# Tot F* function encode_counting_smt.
#
# The `rlimit` argument is z3's DETERMINISTIC instruction-count budget
# (parity-relevant, not wall-clock): when > 0 it is prepended as
# `(set-option :rlimit N)` to the SMT-LIB stream (the spelling z3 4.13.3
# accepts on stdin). A value of 0 means "no rlimit option" (unbounded);
# the runner uses 0 to reproduce the pre-oracle behaviour transparently.
#
# SAFETY CONTRACT (mirrors the throw-on-uninit HACL* wasm precedent):
# ANY spawn failure, nonzero/abnormal exit, unparseable output, or absent
# binary yields Z3_Unknown -- NEVER a fabricated Z3_Unsat/Z3_Sat. A
# fabricated Unsat is a soundness hole exactly as a fabricated
# verify=true is. From Z3_Unknown the runner falls back to the verified
# tableau/RL verdict, so the pure-verified score can never regress.
#
# Trust boundary: ASSUME-HOST + ASSUME-IO (skills/ocaml-boundary).

set -euo pipefail

OUTDIR="$1"

# Backward compatibility: if $1 is a .ml file, use its directory
if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

if [[ ! -d "$OUTDIR" ]]; then
  echo "Error: $OUTDIR is not a directory" >&2
  exit 1
fi

FILE="$OUTDIR/Tableau_CountingOracle.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  WARN: $FILE not found; skipping 296_z3_check_sat patch."
  echo "         (F* extract may not have produced Tableau.CountingOracle yet.)"
  exit 0
fi

# Idempotency: marker is the Phase-1 acknowledgement comment injected
# into the replacement body.
if grep -q 'Issue #296: Phase-1 native z3 spawn' "$FILE"; then
  echo "  [296_z3_check_sat] already applied; skipping."
  exit 0
fi

echo "  Patching $FILE (z3_check_sat -> native z3 spawn, Phase 1)..."

python3 - "$FILE" <<'PYEOF'
import sys, re

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

payload = 'Not yet implemented: Tableau.CountingOracle.z3_check_sat'
already_patched = 'Issue #296: Phase-1 native z3 spawn' in content

if payload not in content and not already_patched:
    sys.stderr.write(
        "  ERROR: 296_z3_check_sat: did not find the z3_check_sat failwith "
        "stub in " + path + "; extraction shape changed?\n"
    )
    sys.exit(1)

# Replacement definition. We rewrite the WHOLE binding (from `let
# z3_check_sat` up to and including the failwith payload string) with a
# canonical definition using our own parameter names, so the patch is
# independent of the extraction-mangled binder names (uu___ / uu___0).
replacement = r'''let z3_check_sat smtlib rlimit =
  (* Issue #296: Phase-1 native z3 spawn (ASSUME-HOST + ASSUME-IO).
     Realisation ONLY -- satisfiability is z3's semantics; the counting
     encoding is the verified F* Tot function encode_counting_smt. Any
     failure => Z3_Unknown, NEVER a fabricated verdict. See
     minimal_regrettable_glue_code_each_with_an_open_issue/296_z3_check_sat.sh *)
  (try Sys.set_signal Sys.sigpipe Sys.Signal_ignore with _ -> ());
  (try
     let z3bin = (try Sys.getenv "FACTOIDAL_Z3_BIN" with Not_found -> "z3") in
     (* NB: the extracted module opens Prims, so a bare `>` / `*` are the
        Z.t operators. Use Z.gt / Z.zero explicitly and keep rl as a
        Stdlib int only for Printf's %d. *)
     let rl = (try Z.to_int rlimit with _ -> 0) in
     let use_rlimit = (try Z.gt rlimit Z.zero with _ -> false) in
     let smt =
       (if use_rlimit then Printf.sprintf "(set-option :rlimit %d)\n" rl else "")
       ^ smtlib in
     (* child stdout -> parent reads r_out; parent writes w_in -> child stdin *)
     (* cloexec on BOTH pipes: create_process dup2s r_in/w_out onto the
        child's fd0/fd1 (clearing cloexec on those dups), then exec closes
        every remaining cloexec fd -- so the child does NOT inherit the
        parent's write-end of its stdin (w_in). Without this the child
        keeps w_in open, its stdin never reaches EOF, z3 blocks forever,
        and the read below deadlocks (the wall-clock cap then reports it
        as Unknown). *)
     let (r_out, w_out) = Unix.pipe ~cloexec:true () in
     let (r_in, w_in) = Unix.pipe ~cloexec:true () in
     let pid =
       Unix.create_process z3bin [| z3bin; "-in"; "-smt2" |] r_in w_out Unix.stderr in
     Unix.close r_in; Unix.close w_out;
     let oc = Unix.out_channel_of_descr w_in in
     (try output_string oc smt; flush oc with _ -> ());
     (try close_out oc with _ -> ());
     let ic = Unix.in_channel_of_descr r_out in
     let rec read_lines acc =
       match (try Some (input_line ic) with End_of_file -> None) with
       | Some l -> read_lines (l :: acc)
       | None -> List.rev acc in
     let lines = read_lines [] in
     (try close_in ic with _ -> ());
     (try ignore (Unix.waitpid [] pid) with _ -> ());
     let rec first = function
       | [] -> Z3_Unknown
       | l :: tl ->
         (match String.trim l with
          | "unsat" -> Z3_Unsat
          | "sat" -> Z3_Sat
          | "unknown" -> Z3_Unknown
          | _ -> first tl) in
     first lines
   with _ -> Z3_Unknown)'''

# Match the whole binding head + failwith body (DOTALL for the '.*?').
pat = re.compile(
    r'let\s+z3_check_sat\b.*?failwith[ \t\n]*"' + re.escape(payload) + r'"',
    re.DOTALL,
)
new_content, n = pat.subn(lambda m: replacement, content)

if n == 0 and not already_patched:
    sys.stderr.write(
        "  ERROR: 296_z3_check_sat: failwith payload present but the "
        "binding regex did not match in " + path + "\n"
    )
    sys.exit(1)

with open(path, "w") as f:
    f.write(new_content)
PYEOF

echo "  [296_z3_check_sat] applied: z3_check_sat -> native z3 spawn (Phase 1)."
