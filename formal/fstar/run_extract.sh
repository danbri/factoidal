#!/usr/bin/env bash
set -uo pipefail
cd /home/user/factoidal/formal/fstar
eval $(opam env --switch=fstar)
rm -f EXTRACT_DONE extract.log
RC=0
./build-ocaml.sh extract > extract.log 2>&1 || RC=$?
echo "EXTRACT_RC=$RC" >> extract.log
touch EXTRACT_DONE
