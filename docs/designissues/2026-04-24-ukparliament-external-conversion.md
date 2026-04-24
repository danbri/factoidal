# UK Parliament TriG — external-canonicaliser preprocessing probe

**Date:** 2026-04-24
**Agent:** Beta
**Target file:** `/Users/danbri/working/factoidal/third_party/data/ukparliament/ukparliament-rdf-2019-07-27.trig` (331 MB)

## Goal

Determine whether we can count triples end-to-end by routing the UK Parliament
TriG dump through an external canonicaliser (Jena `riot`, raptor `rapper`,
`serd`, `rdf-canon`) and then feeding the emitted N-Quads or N-Triples to our
fast F*-extracted counter at `bin/darwin-arm64/factoidal --count --data …`.

## Probe results (tools installed on this host)

```
$ which rapper raptor serd riot arq canonicalize jena sparql
rapper        not found
raptor        not found
serd          not found
riot          not found
arq           not found
canonicalize  not found
jena          not found
sparql        not found

$ brew list | grep -iE "raptor|serd|jena|canon|rdf"
(no output)
```

Additionally checked:

- `python3`  = 3.x present at `/opt/homebrew/bin/python3`
- `rdflib`   **NOT installed** (`ModuleNotFoundError: No module named 'rdflib'`)
- `java`     = `/usr/bin/java` present (Apple stock JRE — but no Jena jar)

## Conclusion

**No external RDF canonicaliser is installed on this machine.** We cannot run
the planned rapper / riot / serd pipeline without first installing something.

## Install-path recommendations (NOT executed — awaiting user approval)

Pick ONE of the following. They are roughly in order of speed / footprint for
this 331 MB TriG task:

1. **raptor / rapper** (C, small, fastest for pure syntax conversion)
   ```
   brew install raptor
   rapper -i trig -o nquads ukparliament-rdf-2019-07-27.trig > /tmp/ukpar.nq
   ```

2. **serd** (C, even smaller than raptor, streaming)
   ```
   brew install serd
   serdi -i trig -o nquads ukparliament-rdf-2019-07-27.trig > /tmp/ukpar.nq
   ```

3. **Apache Jena `riot`** (Java, heaviest but most permissive + best error
   messages)
   ```
   brew install apache-jena
   riot --output=NQuads ukparliament-rdf-2019-07-27.trig > /tmp/ukpar.nq
   # or, to collapse graphs into default graph:
   riot --output=NT  ukparliament-rdf-2019-07-27.trig > /tmp/ukpar.nt
   ```

4. **rdflib** (Python, slowest, last resort — probably will blow memory on 331 MB)
   ```
   pip3 install rdflib
   python3 -c "from rdflib import ConjunctiveGraph; g=ConjunctiveGraph(); g.parse('...','trig'); …"
   ```

## Next step after install

Wrap the chosen converter in a perl-alarm 300 s cap (no GNU `timeout` on
macOS), measure `/usr/bin/time -lp`, then feed output to
`./bin/darwin-arm64/factoidal --count --data /tmp/ukpar.nq` and compare the
triple count from the external tool against ours.

## Verdict

**"install raptor (or apache-jena) first"** — none of the planned external
canonicalisers are available. Recommendation: `brew install raptor` is the
smallest, fastest path; `brew install apache-jena` is the fallback if rapper
chokes on any syntax quirk in the Parliament dump.
