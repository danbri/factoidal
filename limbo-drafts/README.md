# limbo-drafts — provably unreachable, deliberately not deleted

Owner decision 2026-08-17 (issue [#456](https://github.com/danbri/factoidal/issues/456), verbatim: "Mv them to a tld
limbo-drafts/"): these modules are **unreachable from every shipping
entry point**, established by the verified liveness chain — but the
graph cannot distinguish *abandoned* from *not yet wired*, and several
of these look like roadmap scaffolding. So they are parked here, out of
the build, in plain sight, instead of deleted.

## The evidence standard each file met before landing here

- Unreachable at the OCaml layer: `ocamldep -modules` source scan,
  BFS from all consumer entry points (native binaries AND the js/npm
  entry), computed by the extracted `Dep.Reachability.reachable` and
  re-checked against its `closed_set_catches_all` theorem's decidable
  premises at runtime (`bin/depcheck` refuses otherwise).
- No F\*-side referrer: `fstar.exe --dep graph` (name resolution, not
  grep), excluding self and stdlib.
- Post-move, the OCaml compiler is the exhaustive backstop: a single
  surviving real reference is a hard build failure. The tree compiles
  and all gates pass without everything in this directory.

Full tooling: `tools/module-liveness.py` (v3, source-only);
`formal/fstar/Dep.Reachability.fst` (the theorem). History: issues
[#448](https://github.com/danbri/factoidal/issues/448), [#456](https://github.com/danbri/factoidal/issues/456); the graph-vs-intent distinction is [#456](https://github.com/danbri/factoidal/issues/456)'s whole subject.

## Contents, by cluster, with the open intent question

| files | cluster | question |
|---|---|---|
| `SPARQL.Plan.Explain.fst`, `SPARQL.Plan.Loader.fst`, `SPARQL.Plan.Estimate.fst` | query-planner scaffolding | named in the 2026-05-07 query-planning recovery roadmap — future wiring, or superseded by `SPARQL.Plan.AccessPath`/`Streamable`? (`Plan.Pruning` stayed in-tree: type-used by the live AccessPath.) |
| `SPARQL.Service.Wrap.fst`, `service_wrap_http.ml`, `sparql_service_wrap_unit.ml` | SERVICE wrapping | half-landed feature ([#57](https://github.com/danbri/factoidal/issues/57) family)? `service_wrap_hook.ml` is live and stayed in-tree. |
| `Parser.Ballyhoo.fst` | original Ballyhoo container parser | superseded by the HDT/COTTAS variants, which do not import it |
| `RDF.CottasInMem.fst`, `cottas_inmem_encoder_runtime.sh` | in-memory COTTAS store | superseded: `--data-cottas-mem` loads via `Parquet_Footer.register_memory_buffer` (verified) |
| `Util.Log.fst`, `util_log_runtime.sh` | logging infra | never wired; nothing imports it |
| `SPARQL.HTTP.Timing.fst` | Server-Timing surface | presumably for the perf observability roadmap; never wired |

## Restoring a module

1. `git mv` its files back (`.fst` → `formal/fstar/`, glue `.sh` →
   `formal/fstar/experimental_ocaml_glue/`, hand-written `.ml` →
   `formal/fstar/ocaml-output/`, unit test → `tests/unit/`).
2. Re-add its name to the module lists: `build-ocaml.sh` (extract
   loop, `COMMON_MODULES`, js `FSTAR_MODULES`), the two debug build
   scripts, `tests/unit/run-all.sh`'s copy, and any `tests/local/*.sh`
   link list that exercises it (hazard #3: the list lives in many
   places — grep, don't guess).
3. `./build-ocaml.sh extract compile`, then run the gates.
4. Delete its row from this README, and say so in the commit.

## The bar for deleting from here

A cluster leaves limbo for deletion only on an explicit owner call on
its intent question ([#456](https://github.com/danbri/factoidal/issues/456)) — at which point its row moves to the
theorem registry's deletion record like the four modules deleted
before it (`Parser.BallyhooHDTQ`, `RDF.CottasStore.OnDiskRuntime`,
`Parser.BallyhooBloom`, `RDF.Store.HDTTermCacheRegistry`).
