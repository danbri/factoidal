/* End-to-end linkage proof for the KaRaMeL C-build pilot.
 *
 * Calls the F*-verified, krml-extracted RDF.Format /
 * SPARQL.HTTP.StaticFiles / SPARQL.JSON.Escape functions from plain C
 * and checks the answers against the values the F* spec (and the OCaml
 * extraction) gives. Exit code 0 = all checks passed.
 *
 * Built + run by tools/karamel-c-build.sh.
 */

#include <stdio.h>
#include <string.h>

#include "Factoidal_Pilot.h"

static int failures = 0;

static void check_str(const char *what, const char *got, const char *want) {
  int ok = strcmp(got, want) == 0;
  printf("%-50s %s (got \"%s\")\n", what, ok ? "OK" : "FAIL", got);
  if (!ok) {
    printf("  expected \"%s\"\n", want);
    failures++;
  }
}

static void check_fmt(const char *what,
                      FStar_Pervasives_Native_option__RDF_Format_rdf_format got,
                      int want_some, RDF_Format_rdf_format want) {
  int ok = want_some ? (got.tag == FStar_Pervasives_Native_Some && got.v == want)
                     : (got.tag == FStar_Pervasives_Native_None);
  printf("%-50s %s\n", what, ok ? "OK" : "FAIL");
  if (!ok) failures++;
}

int main(void) {
  /* RDF.Format — the module refactored to if/else chains for krml. */
  check_fmt("format_of_extension(\".ttl\")",
            RDF_Format_format_of_extension(".ttl"), 1, RDF_Format_Turtle);
  check_fmt("format_of_extension(\".TTL\") (case-insensitive)",
            RDF_Format_format_of_extension(".TTL"), 1, RDF_Format_Turtle);
  check_fmt("format_of_extension(\".nq\")",
            RDF_Format_format_of_extension(".nq"), 1, RDF_Format_NQuads);
  check_fmt("format_of_extension(\".bogus\") -> None",
            RDF_Format_format_of_extension(".bogus"), 0, 0);
  check_fmt("format_of_string(\"application/ld+json\")",
            RDF_Format_format_of_string("application/ld+json"), 1,
            RDF_Format_JSONLD);

  check_str("format_name(Turtle)", RDF_Format_format_name(RDF_Format_Turtle),
            "Turtle");
  check_str("format_name(RDFXML)", RDF_Format_format_name(RDF_Format_RDFXML),
            "RDF/XML");

  printf("%-50s %s\n", "detect_format_or_default(\".xyz\") -> Turtle",
         RDF_Format_detect_format_or_default(".xyz") == RDF_Format_Turtle
             ? "OK"
             : (failures++, "FAIL"));

  /* SPARQL.HTTP.StaticFiles — string->string MIME lookup. */
  check_str("content_type_for_path(\"/index.html\")",
            SPARQL_HTTP_StaticFiles_content_type_for_path("/index.html"),
            "text/html; charset=utf-8");

  /* SPARQL.JSON.Escape — exercises the Parser.FastString byte stubs. */
  check_str("json_escape(\"a\\\"b\\n\")",
            SPARQL_JSON_Escape_json_escape("a\"b\n"), "a\\\"b\\n");

  if (failures == 0)
    printf("\nAll checks passed — F* -> krml -> C -> gcc round trip OK.\n");
  else
    printf("\n%d check(s) FAILED.\n", failures);
  return failures == 0 ? 0 : 1;
}
