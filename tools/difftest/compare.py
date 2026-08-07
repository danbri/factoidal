"""
Canonical-N-Quads comparison helpers for the differential harness (#317).

RDFC-1.0 defines a canonical serialization precisely enough that two
spec-compliant implementations parsing the SAME graph should emit
byte-identical canonical N-Quads lines (same blank-node labels c14n0,
c14n1, ... via the same deterministic hash-based ordering, same literal
escaping). So AFTER canonicalizing, plain line-level set comparison is the
correct (and simplest) check -- this is exactly what "compare via
canonicalisation, never string equality" means: never string-compare the
original fuzzed serializations, but DO string-compare their canonical
forms, because canonicalization is what makes that comparison valid.
"""
from __future__ import annotations

import signal

try:
    import rdflib
    from rdflib.compare import to_isomorphic
except ImportError:  # pragma: no cover
    rdflib = None


class _TimeoutError(Exception):
    pass


def _with_timeout(seconds, fn, *args, **kwargs):
    """SIGALRM-based hard timeout (main-thread only; this harness is
    single-threaded). rdflib's graph-isomorphism check is worst-case
    expensive on symmetric blank-node structures -- and this fuzz
    generator deliberately builds symmetric k-cycles (rdfgen._symmetric_cycle)
    as an RDFC-1.0 stress case, which is exactly the pathological input for
    a naive isomorphism check too. Measured live: an unbounded version of
    this check made a 40-instance batch exceed a 180s budget it normally
    clears in ~3s. Returns None on timeout so the caller can fall back to
    treating the case as an un-explained (conservatively over-reported,
    never silently dropped) disagreement rather than hanging the batch."""
    def _handler(signum, frame):
        raise _TimeoutError()

    old = signal.signal(signal.SIGALRM, _handler)
    signal.alarm(seconds)
    try:
        return fn(*args, **kwargs)
    except _TimeoutError:
        return None
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)


def normalize_canonical_lines(text: str) -> list:
    """Split canonical N-Quads text into a sorted list of lines with a
    trailing ' .' stripped (factoidal emits it, pyoxigraph's str(Quad)
    does not) so the two engines' output is comparable token-for-token."""
    lines = []
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.endswith(" ."):
            line = line[:-2].rstrip()
        elif line.endswith("."):
            line = line[:-1].rstrip()
        lines.append(line)
    return sorted(lines)


def diff_canonical(text_a: str, text_b: str):
    """Returns (agree: bool, only_in_a: list, only_in_b: list)."""
    a = normalize_canonical_lines(text_a)
    b = normalize_canonical_lines(text_b)
    set_a, set_b = set(a), set(b)
    only_a = sorted(set_a - set_b)
    only_b = sorted(set_b - set_a)
    return (not only_a and not only_b), only_a, only_b


def _langtag_casefold_key(line: str) -> str:
    """Fold ONLY a trailing @langtag to lowercase, leaving everything else
    (including string content, which may legitimately contain '@') alone.
    Used to auto-classify the known RDFC-1.0 language-tag-case ambiguity
    (see docs/designissues/2026-07-29-differential-testing-ledger.md) so it
    doesn't masquerade as a generic disagreement at fuzzing scale."""
    # A literal's closing quote is unambiguous: rfind the last '"' that is
    # not preceded by an odd run of backslashes is overkill for this
    # heuristic; canonical N-Quads literals never contain a raw '"' after
    # the closing quote, so rfind('"') + optional @tag is safe here.
    idx = line.rfind('"')
    if idx == -1:
        return line
    tail = line[idx + 1:]
    if tail.startswith("@"):
        return line[: idx + 1] + "@" + tail[1:].lower()
    return line


def isomorphic_after_langtag_fold(text_a: str, text_b: str, timeout_sec: int = 3) -> bool:
    """True if two canonical N-Quads texts describe graph-isomorphic
    datasets ONCE every language tag is lowercased on both sides. Hard-capped
    at timeout_sec (see _with_timeout) -- returns False (i.e. "not
    explained by this known class, report as a real disagreement") rather
    than hanging on a pathologically symmetric graph.

    Load-bearing distinction from is_only_langtag_case_difference below:
    RDFC-1.0's Hash N-Degree Quads step feeds a literal's EXACT bytes
    (including language-tag case) into the hash of every blank node in its
    transitive neighborhood. So ONE differently-cased language tag
    anywhere in a densely-connected blank-node graph can cascade into
    completely different canonical labels for MANY unrelated blank nodes
    -- the canonical-line-set diff then looks like a sea of unrelated
    disagreements, when the actual root cause is the single already-known
    ambiguity. Only a real graph-isomorphism check (via rdflib, a THIRD
    independent implementation, used here purely as a comparison oracle)
    can see through that cascade; a line-level heuristic cannot. Verified
    against the 2026-07-29 baseline run: a case caught by this function
    but NOT by is_only_langtag_case_difference had 42 "different" lines
    that were fully isomorphic once case was folded."""
    if rdflib is None:
        return False
    result = _with_timeout(timeout_sec, _isomorphic_after_langtag_fold_impl, text_a, text_b)
    return bool(result)


def _isomorphic_after_langtag_fold_impl(text_a: str, text_b: str) -> bool:
    def parse_either(text):
        # N-Quads grammar is a superset of N-Triples (optional 4th graph
        # term), so try it first. rdflib.Dataset (NOT the deprecated
        # ConjunctiveGraph, which mints a fresh random BNode as its
        # default-graph identifier on every instantiation -- verified live,
        # that alone made every graph-profile comparison spuriously "differ"
        # by graph-name-set) uses the stable urn:x-rdflib:default sentinel,
        # so two independently parsed Datasets' default graphs compare equal.
        g = rdflib.Dataset()
        try:
            g.parse(data=text, format="nquads")
            return g
        except Exception:  # noqa: BLE001
            pass
        g2 = rdflib.Graph()
        try:
            g2.parse(data=text, format="nt")
            return g2
        except Exception:  # noqa: BLE001
            return None

    g_a = parse_either(text_a)
    g_b = parse_either(text_b)
    if g_a is None or g_b is None:
        return False

    def fold_term(o):
        if isinstance(o, rdflib.Literal) and o.language:
            return rdflib.Literal(str(o), lang=o.language.lower(), datatype=o.datatype)
        return o

    def per_graph_triples(g):
        """dict: graph-name-string -> plain rdflib.Graph of its (folded)
        triples. Keeps named-graph partitioning meaningful (a quad
        assigned to the WRONG graph must NOT be masked by this check)."""
        by_ctx = {}
        if hasattr(g, "quads"):
            for s, p, o, ctx in g.quads():
                key = str(ctx.identifier) if hasattr(ctx, "identifier") else str(ctx)
                by_ctx.setdefault(key, rdflib.Graph()).add((s, p, fold_term(o)))
        else:
            for s, p, o in g:
                by_ctx.setdefault("", rdflib.Graph()).add((s, p, fold_term(o)))
        return by_ctx

    ctx_a = per_graph_triples(g_a)
    ctx_b = per_graph_triples(g_b)
    # graph-name SETS must match exactly -- a quad landing in the wrong
    # (or a phantom) named graph is a real bug, never explained away here.
    if set(ctx_a.keys()) != set(ctx_b.keys()):
        return False
    try:
        return all(to_isomorphic(ctx_a[k]) == to_isomorphic(ctx_b[k]) for k in ctx_a)
    except Exception:  # noqa: BLE001
        return False


def is_only_langtag_case_difference(only_a: list, only_b: list) -> bool:
    """True if only_a and only_b are the exact same multiset of lines once
    every trailing language tag is lowercased -- i.e. the entire
    disagreement reduces to language-tag casing, nothing else."""
    if not only_a or len(only_a) != len(only_b):
        return False
    folded_a = sorted(_langtag_casefold_key(l) for l in only_a)
    folded_b = sorted(_langtag_casefold_key(l) for l in only_b)
    if folded_a != folded_b:
        return False
    # only_a/only_b are already disjoint (by construction in diff_canonical,
    # they're a set difference) so folded_a == folded_b here can only be
    # true because folding erased a real distinction -- confirm at least
    # one line actually carries an @langtag, so this heuristic can't
    # accidentally swallow a same-line coincidence some other way.
    return any("@" in l for l in only_a)
