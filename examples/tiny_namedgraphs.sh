#!/bin/bash

cat > /tmp/test.nq <<'EOF'
<http://example.org/s1> <http://example.org/p1> <http://example.org/o1> . 
<http://example.org/s2> <http://example.org/p2> "hello" <http://example.org/g1> . 
<http://example.org/s3> <http://example.org/p3> "world" <http://example.org/g1> . 
<http://example.org/s4> <http://example.org/p4> "other" <http://example.org/g2> . 
EOF

./factoidal -d /tmp/test.nq -e 'SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }'

