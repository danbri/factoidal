"""
Adversarial RDF-term generators for the differential-testing corpus (issue #317).

Every function here is a pure generator of ONE term's lexical content, driven
by a `random.Random` instance the caller owns (so runs are reproducible from a
seed). Nothing here talks to the network or any reference implementation --
this module only produces strings that downstream serializers (rdfgen.py)
assemble into full RDF documents.

Bias, per the issue brief: blank-node-heavy graphs, unicode/escaping edge
cases, datatype boundary literals, deeply nested structures, unusual-case
language tags.
"""
from __future__ import annotations

import random

# ---------------------------------------------------------------------------
# IRIs
# ---------------------------------------------------------------------------

_IRI_UNICODE_SEGMENTS = [
    "héllo",              # e-acute
    "日本語",      # Japanese "nihongo"
    "абв",      # Cyrillic
    "مرحبا",  # Arabic (RTL)
    "\U0001F600",              # emoji (astral plane, surrogate pair in UTF-16)
    "café☕",         # e-acute + coffee emoji
    "naïve",
    "中文测试",  # Chinese
    "%C3%A9%20encoded",        # pre-percent-encoded segment
    "a~b!c$d&e'f(g)h*i+j,k;l=m",  # sub-delims legal in IRI path segments
    "x:y",                     # colon in a non-first segment
]

_IRI_SCHEMES = ["http", "https", "urn"]


def iri(rng: random.Random, ontology_safe: bool = False) -> str:
    """Generate an adversarial-but-legal absolute IRI.

    ontology_safe=True restricts to a namespace + clean local-name shape so
    the RDF/XML serializer can always split it into a QName (xmlns prefix +
    NCName-ish local part) -- full unicode freedom is still exercised in the
    local name, just not schemes/authorities, matching how a real ontology's
    predicate IRIs look.
    """
    if ontology_safe:
        local = rng.choice(
            [
                "p", "knows", "label", "value",
                "héllo",           # unicode local name
                "日本語",
                "prop_" + str(rng.randint(0, 9999)),
                "café",
            ]
        )
        return f"http://example.org/onto#{local}"

    scheme = rng.choice(_IRI_SCHEMES)
    if scheme == "urn":
        return f"urn:example:{rng.choice(_IRI_UNICODE_SEGMENTS)}-{rng.randint(0, 99999)}"
    segs = [rng.choice(_IRI_UNICODE_SEGMENTS) for _ in range(rng.randint(1, 3))]
    path = "/".join(segs)
    extra = ""
    if rng.random() < 0.25:
        extra += f"?q={rng.randint(0,999)}&r=v{rng.randint(0,9)}"
    if rng.random() < 0.25:
        extra += f"#frag{rng.randint(0,99)}"
    return f"{scheme}://example.org/{path}{extra}"


# ---------------------------------------------------------------------------
# Blank node labels (Turtle/TriG lexical form -- must respect BLANK_NODE_LABEL
# grammar: PN_CHARS_BASE ((PN_CHARS_U|'.')* PN_CHARS)? -- so no arbitrary
# unicode here, just enough variety to stress the parser's bnode-scoping.)
# ---------------------------------------------------------------------------

_BNODE_LABEL_SHAPES = [
    "b{n}",
    "B{n}",
    "_{n}",
    "n{n}_x",
    "x.{n}.y",
]


def bnode_label(rng: random.Random, n: int) -> str:
    shape = rng.choice(_BNODE_LABEL_SHAPES)
    return shape.format(n=n)


# ---------------------------------------------------------------------------
# Language tags -- unusual casing per BCP47 (tags are case-insensitive; a
# compliant parser must accept any casing and a compliant comparison must
# normalize case, per RDF 1.1 Concepts sec 3.3 which folds to lowercase for
# the primary + region convention (but does NOT mandate lowercasing storage
# for equality -- literal equality is case-insensitive on the tag)).
# ---------------------------------------------------------------------------

_LANG_TAGS = [
    "en", "EN", "En", "en-US", "en-us", "EN-US", "En-Us",
    "en-GB", "en-Latn-GB-boont", "zh-Hans-CN", "ZH-HANS-CN",
    "i-klingon",           # grandfathered irregular
    "x-private-tag",       # private use
    "de-CH-1901",          # variant subtag
    "az-Latn",
    "sr-Cyrl-RS",
    "en--x-extra",         # NOTE: deliberately absent -- would be invalid;
]
# drop the deliberately-invalid placeholder above; keep the list clean.
_LANG_TAGS = [t for t in _LANG_TAGS if t != "en--x-extra"]


def lang_tag(rng: random.Random) -> str:
    return rng.choice(_LANG_TAGS)


# ---------------------------------------------------------------------------
# Literal lexical forms + datatype boundaries
# ---------------------------------------------------------------------------

XSD = "http://www.w3.org/2001/XMLSchema#"

INTEGER_BOUNDARIES = [
    "0", "-0", "1", "-1",
    "2147483647", "-2147483648",              # int32 boundary
    "9223372036854775807", "-9223372036854775808",  # int64 boundary
    "99999999999999999999999999999999999999",       # bignum, beyond int64
    "-99999999999999999999999999999999999999",
    "007",                                     # leading zeros
]

_DECIMAL_BOUNDARIES = [
    "0.0", "-0.0", "1.0", "-1.0", "3.14159265358979323846",
    "1.500000", "0.1", "-0.1", "100000000000000000000.000000000000000001",
    "0.0000000000000000001",
]

_DOUBLE_BOUNDARIES = [
    "1.0E10", "1E-10", "0.0E0", "-0.0E0", "INF", "-INF", "NaN",
    "1.0E300", "1.0E-300", "1.7976931348623157E308",  # near double max
    "4.9E-324",                                        # near double min subnormal
]

_BOOLEAN_FORMS = ["true", "false", "1", "0"]

_DATETIME_BOUNDARIES = [
    "2024-02-29T00:00:00Z",             # leap day
    "0001-01-01T00:00:00Z",             # earliest 4-digit year
    "9999-12-31T23:59:59Z",
    "2024-01-01T00:00:00+14:00",        # max UTC offset
    "2024-01-01T00:00:00-14:00",
    "2024-01-01T00:00:00.123456789Z",   # nanosecond-ish fractional seconds
    "2024-01-01T00:00:00",              # no timezone
]

_STRING_ESCAPE_CASES = [
    'quote " inside',
    "backslash \\ inside",
    "newline\nembedded",
    "tab\tembedded",
    "carriage\rreturn",
    "both \"\\\" and backslash",
    "surrogate-pair emoji \U0001F600 grinning",
    "combining é (e + combining acute)",
    "rtl مرحبا text",
    "null-adjacent N-like control avoided but C kept",
    "zero-width​joiner",
    "",  # empty string literal
    "  leading and trailing spaces  ",
    "line1\nline2\nline3",
]


def literal(rng: random.Random):
    """Return (lexical, datatype_iri_or_None, lang_or_None)."""
    kind = rng.choices(
        ["plain", "lang", "integer", "decimal", "double", "boolean", "datetime", "custom_dt"],
        weights=[15, 20, 15, 10, 10, 8, 10, 5],
        k=1,
    )[0]
    if kind == "plain":
        return rng.choice(_STRING_ESCAPE_CASES), None, None
    if kind == "lang":
        return rng.choice(_STRING_ESCAPE_CASES), None, lang_tag(rng)
    if kind == "integer":
        return rng.choice(INTEGER_BOUNDARIES), XSD + "integer", None
    if kind == "decimal":
        return rng.choice(_DECIMAL_BOUNDARIES), XSD + "decimal", None
    if kind == "double":
        return rng.choice(_DOUBLE_BOUNDARIES), XSD + "double", None
    if kind == "boolean":
        return rng.choice(_BOOLEAN_FORMS), XSD + "boolean", None
    if kind == "datetime":
        return rng.choice(_DATETIME_BOUNDARIES), XSD + "dateTime", None
    # custom_dt: a made-up datatype IRI over an ordinary string -- exercises
    # datatype-IRI handling paths that aren't one of the built-ins.
    return rng.choice(_STRING_ESCAPE_CASES), "http://example.org/onto#CustomType", None
