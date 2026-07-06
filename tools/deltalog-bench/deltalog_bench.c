/* deltalog_bench.c -- consumer-side micro-benchmark driver for the
 * KaRaMeL-extracted C build of RDF.Store.Columnar.DeltaLog
 * (formal/fstar/c-output/deltalog/Factoidal_DeltaLog.{c,h}).
 *
 * Per CLAUDE.md rule #11 this is a consumer tool, not part of the
 * verified library: it contains NO byte-layout logic of its own,
 * only calls into the F*-extracted serialize_delta_batch /
 * parse_delta_batch functions the same way
 * formal/fstar/c-output/deltalog/demo/delta_log_demo.c does (that
 * file is the correctness proof; this one is its timing sibling).
 *
 * Builds a delta_batch of N synthetic DE_Add entries
 * (http://example.org/sI knows http://example.org/oI, no graph),
 * then times:
 *   - serialize_delta_batch(batch)            -> bytes
 *   - parse_delta_batch(bytes)                -> Some (batch', rest)
 * with clock_gettime(CLOCK_MONOTONIC). Prints one JSON line to stdout.
 *
 * Compiles unmodified for both native (gcc/clang) and wasm32-wasi
 * (clang --target=wasm32-wasi --sysroot=/usr, using the apt packages
 * wasi-libc + libclang-rt-18-dev-wasm32) -- see
 * tools/bench-runtimes.sh for both build recipes and
 * docs/web/perf/index.md for what that answers about a hypothetical
 * KaRaMeL C -> wasm full-engine build.
 *
 * Usage: deltalog_bench N
 *   prints: {"n":N,"bytes":B,"serialize_s":F,"parse_s":F,"parse_ok":true|false}
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "Factoidal_DeltaLog.h"
#include "krmlinit.h"

typedef struct Prims_list__RDF_Store_Columnar_DeltaLog_delta_entry_s entry_list;
typedef struct Prims_list__FStar_Char_char_s byte_list;

static double now_seconds(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

static RDF_Store_Columnar_DeltaLog_delta_entry mk_entry(size_t i) {
  char *s = (char *)malloc(48);
  char *o = (char *)malloc(48);
  snprintf(s, 48, "http://example.org/s%zu", i);
  snprintf(o, 48, "http://example.org/o%zu", i);

  RDF_Term_subject subj;
  subj.tag = RDF_Term_S_IRI;
  subj.case_S_IRI = (Prims_string)s;

  RDF_Term_rdf_term obj;
  obj.tag = RDF_Term_T_IRI;
  obj.case_T_IRI = (Prims_string)o;

  RDF_Triple_triple tr;
  tr.s = subj;
  tr.p = (Prims_string)"http://xmlns.com/foaf/0.1/knows";
  tr.o = obj;

  FStar_Pervasives_Native_option__Prims_string g;
  g.tag = FStar_Pervasives_Native_None;

  RDF_Store_Columnar_DeltaLog_delta_entry e;
  e.tag = RDF_Store_Columnar_DeltaLog_DE_Add;
  e.case_DE_Add.quad = tr;
  e.case_DE_Add.graph = g;
  return e;
}

int main(int argc, char **argv) {
  krmlinit_globals();

  if (argc < 2) {
    fprintf(stderr, "usage: %s N\n", argv[0]);
    return 2;
  }
  size_t n = (size_t)strtoull(argv[1], NULL, 10);

  /* Build the list back-to-front so no `append`/reverse of a
   * growing list is needed here (this driver's own cost, not the
   * measured operation's). */
  entry_list *acc = (entry_list *)malloc(sizeof(entry_list));
  acc->tag = Prims_Nil;
  for (size_t i = n; i > 0; i--) {
    entry_list *node = (entry_list *)malloc(sizeof(entry_list));
    node->tag = Prims_Cons;
    node->hd = mk_entry(i - 1);
    node->tl = acc;
    acc = node;
  }

  RDF_Store_Columnar_DeltaLog_delta_batch batch;
  batch.db_seq = 1;
  batch.db_epoch = 0;
  batch.db_ops = acc;

  double t0 = now_seconds();
  byte_list *bytes =
      (byte_list *)RDF_Store_Columnar_DeltaLog_serialize_delta_batch(batch);
  double t1 = now_seconds();

  size_t nbytes = 0;
  for (byte_list *p = bytes; p->tag == Prims_Cons; p = p->tl) nbytes++;

  double t2 = now_seconds();
  FStar_Pervasives_Native_option___RDF_Store_Columnar_DeltaLog_delta_batch___Prims_list__FStar_Char_char_
      parsed = RDF_Store_Columnar_DeltaLog_parse_delta_batch(
          (Prims_list__FStar_Char_char *)bytes);
  double t3 = now_seconds();

  int ok = parsed.tag == FStar_Pervasives_Native_Some;

  printf(
      "{\"n\":%zu,\"bytes\":%zu,\"serialize_s\":%.6f,\"parse_s\":%.6f,"
      "\"parse_ok\":%s}\n",
      n, nbytes, t1 - t0, t3 - t2, ok ? "true" : "false");

  return ok ? 0 : 1;
}
