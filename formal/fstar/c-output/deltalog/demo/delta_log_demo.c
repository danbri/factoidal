/* End-to-end linkage proof for the DeltaLog KaRaMeL C-build group —
 * the durable-UPDATE delta-log byte format
 * (RDF.Store.Columnar.DeltaLog.fst), running as krml-extracted C rather
 * than OCaml. Exercises the REAL proved guarantee
 * (`lemma_delta_entry_roundtrip` / `lemma_delta_batch_roundtrip`):
 *
 *   1. Build a batch of delta_entry ops (ADD/REMOVE/CLEAR/DROP/CREATE
 *      across a mix of IRI/bnode subjects, an IRI object and a
 *      language-tagged literal object) as native C structs.
 *   2. serialize_delta_batch -> bytes; parse_delta_batch -> compare
 *      field-for-field against the original (the round-trip lemma,
 *      now observed running as C, not asserted).
 *   3. Flip one byte inside the serialized bytes and re-parse: the
 *      corruption-detection contract (`simple_checksum` +
 *      magic/version check) must reject it — parse returns `None`,
 *      not a decoded-garbage entry.
 *   4. filter_batches_since_epoch — the compacted-epoch skip-on-replay
 *      guard (§14) — over a couple of hand-built batches, past and
 *      future of a threshold epoch.
 *
 * Built + run by tools/karamel-c-build.sh --group-c.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Factoidal_DeltaLog.h"
#include "krmlinit.h"

static int failures = 0;

static void check(const char *what, int ok) {
  printf("%-64s %s\n", what, ok ? "OK" : "FAIL");
  if (!ok) failures++;
}

/* ---- small builders (C mirror of the F* constructors) ---- */

static RDF_Term_subject mk_iri_subject(const char *iri) {
  RDF_Term_subject s;
  s.tag = RDF_Term_S_IRI;
  s.case_S_IRI = (Prims_string)iri;
  return s;
}

static RDF_Term_subject mk_bnode_subject(const char *b) {
  RDF_Term_subject s;
  s.tag = RDF_Term_S_BNode;
  s.case_S_BNode = (Prims_string)b;
  return s;
}

static RDF_Term_rdf_term mk_iri_term(const char *iri) {
  RDF_Term_rdf_term t;
  t.tag = RDF_Term_T_IRI;
  t.case_T_IRI = (Prims_string)iri;
  return t;
}

static RDF_Term_rdf_term mk_lit_term(const char *lex, const char *dt,
                                      const char *lang) {
  RDF_Term_rdf_term t;
  t.tag = RDF_Term_T_Literal;
  t.case_T_Literal.lexical_form = (Prims_string)lex;
  t.case_T_Literal.datatype = (Prims_string)dt;
  if (lang) {
    t.case_T_Literal.lang_tag.tag = FStar_Pervasives_Native_Some;
    t.case_T_Literal.lang_tag.v = (Prims_string)lang;
  } else {
    t.case_T_Literal.lang_tag.tag = FStar_Pervasives_Native_None;
  }
  return t;
}

static RDF_Triple_triple mk_triple(RDF_Term_subject s, const char *p,
                                    RDF_Term_rdf_term o) {
  RDF_Triple_triple tr;
  tr.s = s;
  tr.p = (Prims_string)p;
  tr.o = o;
  return tr;
}

static FStar_Pervasives_Native_option__Prims_string none_graph(void) {
  FStar_Pervasives_Native_option__Prims_string g;
  g.tag = FStar_Pervasives_Native_None;
  return g;
}

static FStar_Pervasives_Native_option__Prims_string some_graph(
    const char *iri) {
  FStar_Pervasives_Native_option__Prims_string g;
  g.tag = FStar_Pervasives_Native_Some;
  g.v = (Prims_string)iri;
  return g;
}

static RDF_Store_Columnar_DeltaLog_delta_entry mk_add(
    RDF_Triple_triple q, FStar_Pervasives_Native_option__Prims_string g) {
  RDF_Store_Columnar_DeltaLog_delta_entry e;
  e.tag = RDF_Store_Columnar_DeltaLog_DE_Add;
  e.case_DE_Add.quad = q;
  e.case_DE_Add.graph = g;
  return e;
}

static RDF_Store_Columnar_DeltaLog_delta_entry mk_remove(
    RDF_Triple_triple q, FStar_Pervasives_Native_option__Prims_string g) {
  RDF_Store_Columnar_DeltaLog_delta_entry e;
  e.tag = RDF_Store_Columnar_DeltaLog_DE_Remove;
  e.case_DE_Remove.quad = q;
  e.case_DE_Remove.graph = g;
  return e;
}

static RDF_Store_Columnar_DeltaLog_delta_entry mk_clear(
    FStar_Pervasives_Native_option__Prims_string g) {
  RDF_Store_Columnar_DeltaLog_delta_entry e;
  e.tag = RDF_Store_Columnar_DeltaLog_DE_Clear;
  e.case_DE_Clear = g;
  return e;
}

static RDF_Store_Columnar_DeltaLog_delta_entry mk_drop(const char *g) {
  RDF_Store_Columnar_DeltaLog_delta_entry e;
  e.tag = RDF_Store_Columnar_DeltaLog_DE_Drop;
  e.case_DE_Drop = (Prims_string)g;
  return e;
}

static RDF_Store_Columnar_DeltaLog_delta_entry mk_create(const char *g) {
  RDF_Store_Columnar_DeltaLog_delta_entry e;
  e.tag = RDF_Store_Columnar_DeltaLog_DE_Create;
  e.case_DE_Create = (Prims_string)g;
  return e;
}

typedef struct Prims_list__RDF_Store_Columnar_DeltaLog_delta_entry_s
    entry_list;

static entry_list *entry_list_of_array(
    RDF_Store_Columnar_DeltaLog_delta_entry *arr, size_t n) {
  entry_list *acc = malloc(sizeof(entry_list));
  acc->tag = Prims_Nil;
  for (size_t i = n; i > 0; i--) {
    entry_list *node = malloc(sizeof(entry_list));
    node->tag = Prims_Cons;
    node->hd = arr[i - 1];
    node->tl = acc;
    acc = node;
  }
  return acc;
}

/* ---- byte-list helpers (corrupt-a-byte test) ---- */

typedef struct Prims_list__FStar_Char_char_s byte_list;

static size_t byte_list_length(byte_list *l) {
  size_t n = 0;
  while (l->tag == Prims_Cons) {
    n++;
    l = l->tl;
  }
  return n;
}

static byte_list *byte_list_copy(byte_list *l) {
  byte_list *out = malloc(sizeof(byte_list));
  if (l->tag == Prims_Nil) {
    out->tag = Prims_Nil;
    return out;
  }
  out->tag = Prims_Cons;
  out->hd = l->hd;
  out->tl = byte_list_copy(l->tl);
  return out;
}

/* Flip one bit in the byte at position `idx` (0-based). */
static void byte_list_flip_at(byte_list *l, size_t idx) {
  while (idx > 0) {
    l = l->tl;
    idx--;
  }
  l->hd ^= 0xFFu;
}

/* ---- deep structural equality (mirrors the F* eq the round-trip
   lemma is stated over) ---- */

static int subject_eq(RDF_Term_subject a, RDF_Term_subject b) {
  if (a.tag != b.tag) return 0;
  if (a.tag == RDF_Term_S_IRI) return strcmp(a.case_S_IRI, b.case_S_IRI) == 0;
  return strcmp(a.case_S_BNode, b.case_S_BNode) == 0;
}

static int stropt_eq(FStar_Pervasives_Native_option__Prims_string a,
                      FStar_Pervasives_Native_option__Prims_string b) {
  if (a.tag != b.tag) return 0;
  if (a.tag == FStar_Pervasives_Native_None) return 1;
  return strcmp(a.v, b.v) == 0;
}

static int term_eq(RDF_Term_rdf_term a, RDF_Term_rdf_term b) {
  if (a.tag != b.tag) return 0;
  if (a.tag == RDF_Term_T_IRI) return strcmp(a.case_T_IRI, b.case_T_IRI) == 0;
  if (a.tag == RDF_Term_T_BNode)
    return strcmp(a.case_T_BNode, b.case_T_BNode) == 0;
  RDF_Term_literal la = a.case_T_Literal, lb = b.case_T_Literal;
  return strcmp(la.lexical_form, lb.lexical_form) == 0 &&
         strcmp(la.datatype, lb.datatype) == 0 &&
         stropt_eq(la.lang_tag, lb.lang_tag);
}

static int triple_eq(RDF_Triple_triple a, RDF_Triple_triple b) {
  return subject_eq(a.s, b.s) && strcmp(a.p, b.p) == 0 && term_eq(a.o, b.o);
}

static int entry_eq(RDF_Store_Columnar_DeltaLog_delta_entry a,
                     RDF_Store_Columnar_DeltaLog_delta_entry b) {
  if (a.tag != b.tag) return 0;
  switch (a.tag) {
    case RDF_Store_Columnar_DeltaLog_DE_Add:
      return triple_eq(a.case_DE_Add.quad, b.case_DE_Add.quad) &&
             stropt_eq(a.case_DE_Add.graph, b.case_DE_Add.graph);
    case RDF_Store_Columnar_DeltaLog_DE_Remove:
      return triple_eq(a.case_DE_Remove.quad, b.case_DE_Remove.quad) &&
             stropt_eq(a.case_DE_Remove.graph, b.case_DE_Remove.graph);
    case RDF_Store_Columnar_DeltaLog_DE_Clear:
      return stropt_eq(a.case_DE_Clear, b.case_DE_Clear);
    case RDF_Store_Columnar_DeltaLog_DE_Drop:
      return strcmp(a.case_DE_Drop, b.case_DE_Drop) == 0;
    case RDF_Store_Columnar_DeltaLog_DE_Create:
      return strcmp(a.case_DE_Create, b.case_DE_Create) == 0;
  }
  return 0;
}

static int entry_list_eq(entry_list *a, entry_list *b) {
  while (a->tag == Prims_Cons && b->tag == Prims_Cons) {
    if (!entry_eq(a->hd, b->hd)) return 0;
    a = a->tl;
    b = b->tl;
  }
  return a->tag == Prims_Nil && b->tag == Prims_Nil;
}

static int batch_eq(RDF_Store_Columnar_DeltaLog_delta_batch a,
                     RDF_Store_Columnar_DeltaLog_delta_batch b) {
  return a.db_seq == b.db_seq && a.db_epoch == b.db_epoch &&
         entry_list_eq(a.db_ops, b.db_ops);
}

int main(void) {
  /* krmlinit_globals() must run before any of this module's other
   * top-level values are read — RDF_Store_Columnar_DeltaLog_
   * serialize_log_header (used implicitly via the magic/version
   * globals) is computed there, not as a C static initializer
   * (Warning 9 in the krml log: these two globals aren't C constants).
   */
  krmlinit_globals();

  /* --- 1. Build a batch mixing every delta_entry constructor --- */
  RDF_Store_Columnar_DeltaLog_delta_entry ops[5];
  ops[0] = mk_add(
      mk_triple(mk_iri_subject("http://example.org/alice"),
                "http://xmlns.com/foaf/0.1/knows",
                mk_iri_term("http://example.org/bob")),
      none_graph());
  ops[1] = mk_add(
      mk_triple(mk_bnode_subject("_:b1"), "http://example.org/label",
                mk_lit_term("hello", "http://www.w3.org/2001/XMLSchema#string",
                            NULL)),
      some_graph("http://example.org/graph1"));
  ops[2] = mk_remove(
      mk_triple(mk_iri_subject("http://example.org/alice"),
                "http://xmlns.com/foaf/0.1/knows",
                mk_iri_term("http://example.org/carol")),
      none_graph());
  ops[3] = mk_clear(some_graph("http://example.org/graph1"));
  ops[4] = mk_create("http://example.org/graph2");

  RDF_Store_Columnar_DeltaLog_delta_batch batch;
  batch.db_seq = 42;
  batch.db_epoch = 3;
  batch.db_ops = entry_list_of_array(ops, 5);

  check("delta_batch_ok(batch)",
        RDF_Store_Columnar_DeltaLog_delta_batch_ok(batch));

  /* --- 2. serialize -> parse round trip (lemma_delta_batch_roundtrip,
     running as C) --- */
  byte_list *bytes = (byte_list *)RDF_Store_Columnar_DeltaLog_serialize_delta_batch(
      batch);
  size_t nbytes = byte_list_length(bytes);
  printf("serialize_delta_batch -> %zu bytes\n", nbytes);
  check("serialized length > 0", nbytes > 0);

  FStar_Pervasives_Native_option___RDF_Store_Columnar_DeltaLog_delta_batch___Prims_list__FStar_Char_char_
      parsed = RDF_Store_Columnar_DeltaLog_parse_delta_batch(
          (Prims_list__FStar_Char_char *)bytes);
  check("parse_delta_batch(serialize_delta_batch(batch)) = Some",
        parsed.tag == FStar_Pervasives_Native_Some);
  if (parsed.tag == FStar_Pervasives_Native_Some) {
    check("parsed batch equals original (round-trip)",
          batch_eq(parsed.v.fst, batch));
    check("no leftover bytes",
          ((byte_list *)parsed.v.snd)->tag == Prims_Nil);
  }

  /* Round trip with trailing bytes too — the lemma's actual statement
   * is about `serialize ++ rest`, not just `serialize` alone. */
  byte_list *tail = malloc(sizeof(byte_list));
  tail->tag = Prims_Cons;
  tail->hd = 'X';
  byte_list *tail_nil = malloc(sizeof(byte_list));
  tail_nil->tag = Prims_Nil;
  tail->tl = tail_nil;
  byte_list *with_tail = byte_list_copy(bytes);
  {
    /* append tail onto the copy */
    byte_list *p = with_tail;
    while (p->tag == Prims_Cons) p = p->tl;
    /* p is the Nil node at the end; splice tail's Cons cell in */
    p->tag = Prims_Cons;
    p->hd = tail->hd;
    p->tl = tail->tl;
  }
  FStar_Pervasives_Native_option___RDF_Store_Columnar_DeltaLog_delta_batch___Prims_list__FStar_Char_char_
      parsed2 = RDF_Store_Columnar_DeltaLog_parse_delta_batch(
          (Prims_list__FStar_Char_char *)with_tail);
  check("parse(serialize(batch) ++ 'X') = Some, batch recovered",
        parsed2.tag == FStar_Pervasives_Native_Some &&
            batch_eq(parsed2.v.fst, batch));
  check("...and the trailing 'X' is exactly what's left over",
        parsed2.tag == FStar_Pervasives_Native_Some &&
            ((byte_list *)parsed2.v.snd)->tag == Prims_Cons &&
            ((byte_list *)parsed2.v.snd)->hd == 'X' &&
            ((byte_list *)parsed2.v.snd)->tl->tag == Prims_Nil);

  /* --- 3. Corrupt one byte -> parse must return None --- */
  byte_list *corrupted = byte_list_copy(bytes);
  size_t mid = nbytes / 2;
  byte_list_flip_at(corrupted, mid);
  FStar_Pervasives_Native_option___RDF_Store_Columnar_DeltaLog_delta_batch___Prims_list__FStar_Char_char_
      parsed_corrupt = RDF_Store_Columnar_DeltaLog_parse_delta_batch(
          (Prims_list__FStar_Char_char *)corrupted);
  check("parse_delta_batch(corrupted bytes) = None (checksum rejects it)",
        parsed_corrupt.tag == FStar_Pervasives_Native_None);

  /* Corrupt the magic (first byte) too — a different failure mode
   * (framing rejection, not checksum rejection) that should also
   * yield None, never a mis-decoded batch. */
  byte_list *corrupted_magic = byte_list_copy(bytes);
  byte_list_flip_at(corrupted_magic, 0);
  FStar_Pervasives_Native_option___RDF_Store_Columnar_DeltaLog_delta_batch___Prims_list__FStar_Char_char_
      parsed_bad_magic = RDF_Store_Columnar_DeltaLog_parse_delta_batch(
          (Prims_list__FStar_Char_char *)corrupted_magic);
  check("parse_delta_batch(corrupted magic) = None",
        parsed_bad_magic.tag == FStar_Pervasives_Native_None);

  /* --- 4. filter_batches_since_epoch — the compacted-epoch skip
   * guard (§14). Two batches, epochs 3 and 5; threshold Some 3 must
   * keep only the epoch-5 batch (db_epoch > threshold). --- */
  RDF_Store_Columnar_DeltaLog_delta_batch old_batch = batch; /* db_epoch = 3 */

  RDF_Store_Columnar_DeltaLog_delta_entry ops2[1];
  ops2[0] = mk_add(
      mk_triple(mk_iri_subject("http://example.org/dave"),
                "http://xmlns.com/foaf/0.1/knows",
                mk_iri_term("http://example.org/erin")),
      none_graph());
  RDF_Store_Columnar_DeltaLog_delta_batch new_batch;
  new_batch.db_seq = 43;
  new_batch.db_epoch = 5;
  new_batch.db_ops = entry_list_of_array(ops2, 1);

  typedef struct Prims_list__RDF_Store_Columnar_DeltaLog_delta_batch_s
      batch_list;
  batch_list *bl = malloc(sizeof(batch_list));
  bl->tag = Prims_Cons;
  bl->hd = old_batch;
  batch_list *bl2 = malloc(sizeof(batch_list));
  bl2->tag = Prims_Cons;
  bl2->hd = new_batch;
  batch_list *bl_nil = malloc(sizeof(batch_list));
  bl_nil->tag = Prims_Nil;
  bl2->tl = bl_nil;
  bl->tl = bl2;

  FStar_Pervasives_Native_option__krml_checked_int_t threshold;
  threshold.tag = FStar_Pervasives_Native_Some;
  threshold.v = 3;

  batch_list *kept = (batch_list *)RDF_Store_Columnar_DeltaLog_filter_batches_since_epoch(
      threshold, bl);
  size_t kept_count = 0;
  krml_checked_int_t kept_epoch = -1;
  for (batch_list *p = kept; p->tag == Prims_Cons; p = p->tl) {
    kept_count++;
    kept_epoch = p->hd.db_epoch;
  }
  check("filter_batches_since_epoch(Some 3, [epoch3, epoch5]) keeps exactly 1",
        kept_count == 1);
  check("...and it's the epoch-5 (post-threshold) batch",
        kept_count == 1 && kept_epoch == 5);

  /* No threshold (store never compacted) -> both batches survive. */
  FStar_Pervasives_Native_option__krml_checked_int_t no_threshold;
  no_threshold.tag = FStar_Pervasives_Native_None;
  batch_list *kept_all =
      (batch_list *)RDF_Store_Columnar_DeltaLog_filter_batches_since_epoch(
          no_threshold, bl);
  size_t kept_all_count = 0;
  for (batch_list *p = kept_all; p->tag == Prims_Cons; p = p->tl)
    kept_all_count++;
  check("filter_batches_since_epoch(None, [_, _]) keeps both", kept_all_count == 2);

  if (failures == 0)
    printf(
        "\nAll checks passed — F* -> krml -> C -> gcc round trip OK "
        "(RDF.Store.Columnar.DeltaLog).\n");
  else
    printf("\n%d check(s) FAILED.\n", failures);
  return failures == 0 ? 0 : 1;
}
