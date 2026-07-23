#!/usr/bin/env bash
set -uo pipefail
cd /home/user/factoidal/formal/fstar
eval $(opam env --switch=fstar)
rm -f COMPILE_DONE compile.log
RC=0
./build-ocaml.sh compile > compile.log 2>&1 || RC=$?
echo "COMPILE_RC=$RC" >> compile.log
touch COMPILE_DONE
