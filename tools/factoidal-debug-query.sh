#!/bin/bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"

detect_platform() {
  local uname_s uname_m
  uname_s="$(uname -s)"
  uname_m="$(uname -m)"
  if [[ "$uname_s" == "Darwin" && "$uname_m" == "arm64" ]]; then
    printf "darwin-arm64"
  elif [[ "$uname_s" == "Darwin" && "$uname_m" == "x86_64" ]]; then
    printf "darwin-x86_64"
  elif [[ "$uname_s" == "Linux" && "$uname_m" == "x86_64" ]]; then
    printf "linux-x86_64"
  elif [[ "$uname_s" == "Linux" && "$uname_m" == "aarch64" ]]; then
    printf "linux-arm64"
  else
    printf "%s-%s" "${uname_s,,}" "$uname_m"
  fi
}

PLATFORM="${FACTOIDAL_PLATFORM:-$(detect_platform)}"
FACTOIDAL_BIN="${ROOT_DIR}/bin/${PLATFORM}/factoidal"
FACTOIDAL_BYTE="${ROOT_DIR}/bin/${PLATFORM}/factoidal.byte"
OCAMLDEBUG_BIN="${OCAMLDEBUG_BIN:-$HOME/.opam/fstar/bin/ocamldebug}"
FACTOIDAL_PYTHON="${FACTOIDAL_PYTHON:-}"
FACTOIDAL_SERIALIZER="${FACTOIDAL_SERIALIZER:-}"

usage() {
  cat <<EOF
factoidal-debug-query.sh — helper for COTTAS corpus setup + planner/debug sessions

Usage:
  tools/factoidal-debug-query.sh build-debug
  tools/factoidal-debug-query.sh build-serializer
  tools/factoidal-debug-query.sh import-cottas --input FILE --corpus-root DIR --dataset-name NAME [--chunk-name NAME] [--parser factoidal|auto|python|pyoxigraph|rdflib]
  tools/factoidal-debug-query.sh cottas-path --corpus-root DIR --chunk-name NAME [--version v1]
  tools/factoidal-debug-query.sh cottas-info --data-cottas FILE
  tools/factoidal-debug-query.sh explain --data-cottas FILE (--query FILE | -e 'SPARQL') [--explain-out FILE]
  tools/factoidal-debug-query.sh debug --data-cottas FILE (--query FILE | -e 'SPARQL') [--break MODULE:LINE]
  tools/factoidal-debug-query.sh trace-experiment --data-cottas FILE (--query FILE | -e 'SPARQL') [--name NAME] [--exec-timeout-sec SEC] [--trace-mode plan|exec|debug]

Notes:
  - build-debug uses formal/fstar/build-ocaml-debug.sh and does NOT alter the normal build path.
  - build-serializer builds a minimal fallback RDF -> canonical N-Quads serializer.
  - import-cottas uses tools/corpus_pipeline.py and accepts --parser.
    The current default is --parser factoidal, which uses "factoidal dump-nq"
    from the main binary when available, and falls back to the standalone
    serializer only if needed.
  - explain uses the native factoidal "--explain" mode against an on-disk COTTAS store.
  - debug launches ocamldebug on factoidal.byte. Today that query path can load
    --data-cottas, but it goes through the CLI's eager COTTAS loader rather than the
    server's GB_CottasOnDisk backend.
  - trace-experiment wraps --explain-only plus a real CLI execution and writes
    a first-cut trace JSON + human-readable report under tmp/query-trace-experiment/.
EOF
}

ensure_factoidal_bin() {
  if [[ ! -x "$FACTOIDAL_BIN" ]]; then
    echo "error: missing native factoidal binary: $FACTOIDAL_BIN" >&2
    echo "build it with: cd formal/fstar && ./build-ocaml.sh compile" >&2
    exit 1
  fi
}

resolve_factoidal_python() {
  if [[ -n "$FACTOIDAL_PYTHON" && -x "$FACTOIDAL_PYTHON" ]]; then
    printf "%s" "$FACTOIDAL_PYTHON"
    return 0
  fi
  if [[ -x "${ROOT_DIR}/tmp/pycottas-venv/bin/python" ]]; then
    printf "%s" "${ROOT_DIR}/tmp/pycottas-venv/bin/python"
    return 0
  fi
  if command -v python3 >/dev/null 2>&1; then
    printf "%s" "python3"
    return 0
  fi
  return 1
}

ensure_debug_bytecode() {
  if [[ ! -x "$FACTOIDAL_BYTE" ]]; then
    echo "debug bytecode missing; building it now..." >&2
    (cd "${ROOT_DIR}/formal/fstar" && ./build-ocaml-debug.sh factoidal)
  fi
  if [[ ! -x "$FACTOIDAL_BYTE" ]]; then
    echo "error: debug bytecode build did not produce $FACTOIDAL_BYTE" >&2
    exit 1
  fi
}

ensure_factoidal_serializer() {
  if [[ -x "$FACTOIDAL_BIN" ]]; then
    export FACTOIDAL_BIN
    return 0
  fi
  if [[ -n "$FACTOIDAL_SERIALIZER" && -x "$FACTOIDAL_SERIALIZER" ]]; then
    export FACTOIDAL_BIN="$FACTOIDAL_SERIALIZER"
    return 0
  fi
  local serializer_native="${ROOT_DIR}/bin/${PLATFORM}/factoidal-dump-nq"
  local serializer_byte="${ROOT_DIR}/bin/${PLATFORM}/factoidal-dump-nq.byte"
  if [[ -x "$serializer_native" ]]; then
    export FACTOIDAL_BIN="$serializer_native"
    return 0
  fi
  if [[ -x "$serializer_byte" ]]; then
    export FACTOIDAL_BIN="$serializer_byte"
    return 0
  fi
  echo "factoidal serializer fallback missing; building it now..." >&2
  (
    cd "${ROOT_DIR}/formal/fstar"
    eval "$(opam env --switch=fstar)"
    ./build-ocaml-serializer.sh
  )
  if [[ -x "$serializer_native" ]]; then
    export FACTOIDAL_BIN="$serializer_native"
    return 0
  fi
  if [[ -x "$serializer_byte" ]]; then
    export FACTOIDAL_BIN="$serializer_byte"
    return 0
  fi
  echo "error: serializer build did not produce $serializer_native or $serializer_byte" >&2
  exit 1
}

ensure_ocamldebug() {
  if [[ ! -x "$OCAMLDEBUG_BIN" ]]; then
    echo "error: ocamldebug not found at $OCAMLDEBUG_BIN" >&2
    echo "hint: eval \$(opam env --switch=fstar) and check ~/.opam/fstar/bin/ocamldebug" >&2
    exit 1
  fi
}

require_query_arg() {
  local query_file="$1"
  local inline_query="$2"
  if [[ -z "$query_file" && -z "$inline_query" ]]; then
    echo "error: need --query FILE or -e 'SPARQL'" >&2
    exit 2
  fi
}

subcmd="${1:-}"
if [[ -z "$subcmd" ]]; then
  usage
  exit 2
fi
shift

case "$subcmd" in
  help|-h|--help)
    usage
    ;;

  build-debug)
    (cd "${ROOT_DIR}/formal/fstar" && ./build-ocaml-debug.sh factoidal)
    echo "bytecode: $FACTOIDAL_BYTE"
    ;;

  build-serializer)
    (
      cd "${ROOT_DIR}/formal/fstar"
      eval "$(opam env --switch=fstar)"
      ./build-ocaml-serializer.sh
    )
    echo "serializer: ${ROOT_DIR}/bin/${PLATFORM}/factoidal-dump-nq"
    ;;

  import-cottas)
    parser_name="factoidal"
    for ((i=1; i<=$#; i++)); do
      if [[ "${!i}" == "--parser" ]]; then
        next=$((i + 1))
        parser_name="${!next}"
      fi
    done
    if [[ "$parser_name" == "factoidal" || "$parser_name" == "auto" ]]; then
      ensure_factoidal_serializer
    fi
    pybin="$(resolve_factoidal_python || true)"
    if [[ -z "${pybin:-}" ]]; then
      echo "error: no usable Python found for tools/corpus_pipeline.py" >&2
      echo "set FACTOIDAL_PYTHON=/path/to/python if needed" >&2
      exit 1
    fi
    exec "$pybin" "${ROOT_DIR}/tools/corpus_pipeline.py" materialize-nq-cottas-corpus "$@"
    ;;

  cottas-path)
    corpus_root=""
    chunk_name=""
    version="v1"
    while [[ $# -gt 0 ]]; do
      case "$1" in
        --corpus-root) corpus_root="$2"; shift 2 ;;
        --chunk-name) chunk_name="$2"; shift 2 ;;
        --version) version="$2"; shift 2 ;;
        *) echo "error: unknown arg for cottas-path: $1" >&2; exit 2 ;;
      esac
    done
    if [[ -z "$corpus_root" || -z "$chunk_name" ]]; then
      echo "error: cottas-path requires --corpus-root and --chunk-name" >&2
      exit 2
    fi
    python3 - <<EOF
from pathlib import Path
print((Path("$corpus_root") / "$chunk_name" / "$version" / "data.cottas").resolve())
EOF
    ;;

  cottas-info)
    ensure_factoidal_bin
    if [[ "${1:-}" == "--data-cottas" ]]; then
      shift
    fi
    exec "$FACTOIDAL_BIN" cottas-info "$@"
    ;;

  explain)
    ensure_factoidal_bin
    exec "$FACTOIDAL_BIN" --explain-only "$@"
    ;;

  trace-experiment)
    pybin="$(resolve_factoidal_python || true)"
    if [[ -z "${pybin:-}" ]]; then
      echo "error: no usable Python found for tools/query_trace_experiment.py" >&2
      echo "set FACTOIDAL_PYTHON=/path/to/python if needed" >&2
      exit 1
    fi
    exec "$pybin" "${ROOT_DIR}/tools/query_trace_experiment.py" "$@"
    ;;

  debug)
    ensure_debug_bytecode
    ensure_ocamldebug
    data_cottas=""
    query_file=""
    inline_query=""
    break_spec="Factoidal_cli:950"
    passthrough=()
    while [[ $# -gt 0 ]]; do
      case "$1" in
        --data-cottas) data_cottas="$2"; passthrough+=("$1" "$2"); shift 2 ;;
        --query) query_file="$2"; passthrough+=("$1" "$2"); shift 2 ;;
        -e|--explain) inline_query="$2"; passthrough+=("-e" "$2"); shift 2 ;;
        --break) break_spec="$2"; shift 2 ;;
        *) passthrough+=("$1"); shift ;;
      esac
    done
    if [[ -z "$data_cottas" ]]; then
      echo "error: debug requires --data-cottas FILE" >&2
      exit 2
    fi
    require_query_arg "$query_file" "$inline_query"
    module_name="${break_spec%%:*}"
    line_no="${break_spec##*:}"
    cmdfile="$(mktemp "${TMPDIR:-/tmp}/factoidal-ocamldebug.XXXXXX")"
    cat > "$cmdfile" <<EOF
set arguments ${passthrough[*]}
break @ ${module_name} ${line_no}
run
EOF
    echo "Launching ocamldebug with:"
    echo "  bytecode: $FACTOIDAL_BYTE"
    echo "  args: ${passthrough[*]}"
    echo "  initial breakpoint: ${module_name}:${line_no}"
    echo "Useful commands once it stops: where, print query_text, step, backstep, reverse"
    exec "$OCAMLDEBUG_BIN" -s "$cmdfile" "$FACTOIDAL_BYTE"
    ;;

  *)
    echo "error: unknown subcommand '$subcmd'" >&2
    usage >&2
    exit 2
    ;;
esac
