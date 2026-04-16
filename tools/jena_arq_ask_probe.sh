#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
ASK_ROOT="${1:-/tmp/jena/jena-arq/testing/ARQ/Ask}"
TMPDIR="${TMPDIR:-/tmp}"

if [[ ! -x "${BIN}" ]]; then
  echo "factoidal binary not found at ${BIN}" >&2
  exit 1
fi

if [[ ! -d "${ASK_ROOT}" ]]; then
  echo "Jena ARQ Ask root not found at ${ASK_ROOT}" >&2
  exit 1
fi

expected_bool() {
  local result_file="$1"
  case "${result_file}" in
    *.srx)
      if rg -q '<boolean>true</boolean>' "${result_file}"; then
        printf 'true\n'
      else
        printf 'false\n'
      fi
      ;;
    *.srj)
      if rg -q '"boolean"[[:space:]]*:[[:space:]]*true' "${result_file}"; then
        printf 'true\n'
      else
        printf 'false\n'
      fi
      ;;
    *.ttl)
      if rg -q 'rs:boolean[[:space:]]+"true"\^\^xsd:boolean' "${result_file}"; then
        printf 'true\n'
      else
        printf 'false\n'
      fi
      ;;
    *)
      echo "unsupported result file: ${result_file}" >&2
      return 1
      ;;
  esac
}

pass=0
fail=0

for query in "${ASK_ROOT}"/ask-*.rq; do
  name="$(basename "${query}" .rq)"
  result_file=""
  for ext in srx srj ttl; do
    if [[ -f "${ASK_ROOT}/${name}.${ext}" ]]; then
      result_file="${ASK_ROOT}/${name}.${ext}"
      break
    fi
  done
  if [[ -z "${result_file}" ]]; then
    echo "SKIP ${name} missing-result"
    continue
  fi

  expected="$(expected_bool "${result_file}")"
  output_file="${TMPDIR}/factoidal_jena_ask_${name}.out"
  err_file="${TMPDIR}/factoidal_jena_ask_${name}.err"

  if "${BIN}" --data "${ASK_ROOT}/data.ttl" --query "${query}" >"${output_file}" 2>"${err_file}"; then
    actual="$(tr -d '\r' < "${output_file}" | tail -n 1 | tr -d '[:space:]')"
    if [[ "${actual}" == "${expected}" ]]; then
      echo "PASS ${name} ${actual}"
      pass=$((pass + 1))
    else
      echo "FAIL ${name} expected=${expected} actual=${actual}"
      sed -n '1,40p' "${err_file}"
      fail=$((fail + 1))
    fi
  else
    echo "FAIL ${name} execution"
    sed -n '1,40p' "${err_file}"
    fail=$((fail + 1))
  fi
done

echo "pass=${pass} fail=${fail}"

if [[ "${fail}" -ne 0 ]]; then
  exit 1
fi
