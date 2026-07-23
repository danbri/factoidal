#!/usr/bin/env bash
set -uo pipefail
cd /home/user/factoidal/formal/fstar
eval $(opam env --switch=fstar)
rm -f VERIFY_DONE verify.log
RC=0
fstar.exe --z3version 4.13.3 --cache_checked_modules SHACL.Validation.fst > verify.log 2>&1 || RC=$?
echo "VERIFY_RC=$RC" >> verify.log
touch VERIFY_DONE
