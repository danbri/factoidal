#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="./formal/fstar/ocaml-output/parquet_probe"
TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-parquet-footer-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

INPUT="${ROOT}/tests/local/data/cottas_sample.nq"
CORPUS_ROOT="${WORKDIR}/CorpusCOTTA"
ARTIFACT_FILE="${CORPUS_ROOT}/sample-cottas/v1/data.cottas"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"

"${PYCOTTAS_PYTHON}" "${ROOT}/tools/corpus_pipeline.py" materialize-nq-cottas-corpus \
  --input "${INPUT}" \
  --corpus-root "${CORPUS_ROOT}" \
  --dataset-name sample-cottas \
  --chunk-name sample-cottas \
  >/dev/null

cd "${ROOT}"

output="$(bash -lc "\"${BIN}\" \"${ARTIFACT_FILE}\"")"

if ! printf '%s\n' "${output}" | rg -q '^magic=PAR1$'; then
  echo "FAIL parquet-magic"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^metadata_len=[1-9][0-9]*$'; then
  echo "FAIL parquet-metadata-len"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^num_rows=5$'; then
  echo "FAIL parquet-num-rows"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_groups=1$'; then
  echo "FAIL parquet-row-groups"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_num_rows=5$'; then
  echo "FAIL parquet-row-group0-num-rows"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_columns=4$'; then
  echo "FAIL parquet-row-group0-columns"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_name=s$'; then
  echo "FAIL parquet-row-group0-col0-name"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_data_page_offset=4$'; then
  echo "FAIL parquet-row-group0-col0-data-page-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_name=p$'; then
  echo "FAIL parquet-row-group0-col1-name"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_name=o$'; then
  echo "FAIL parquet-row-group0-col2-name"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_name=g$'; then
  echo "FAIL parquet-row-group0-col3-name"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_data_page_offset=116$'; then
  echo "FAIL parquet-row-group0-col1-data-page-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_data_page_offset=219$'; then
  echo "FAIL parquet-row-group0-col2-data-page-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_data_page_offset=330$'; then
  echo "FAIL parquet-row-group0-col3-data-page-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_compression=ZSTD$'; then
  echo "FAIL parquet-row-group0-col0-compression"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_compression=ZSTD$'; then
  echo "FAIL parquet-row-group0-col1-compression"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_compression=ZSTD$'; then
  echo "FAIL parquet-row-group0-col2-compression"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_compression=ZSTD$'; then
  echo "FAIL parquet-row-group0-col3-compression"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_num_values=5$'; then
  echo "FAIL parquet-row-group0-col0-num-values"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_num_values=5$'; then
  echo "FAIL parquet-row-group0-col1-num-values"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_num_values=5$'; then
  echo "FAIL parquet-row-group0-col2-num-values"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_num_values=5$'; then
  echo "FAIL parquet-row-group0-col3-num-values"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_total_compressed_size=112$'; then
  echo "FAIL parquet-row-group0-col0-total-compressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_total_compressed_size=103$'; then
  echo "FAIL parquet-row-group0-col1-total-compressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_total_compressed_size=111$'; then
  echo "FAIL parquet-row-group0-col2-total-compressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_total_compressed_size=109$'; then
  echo "FAIL parquet-row-group0-col3-total-compressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_total_uncompressed_size=340$'; then
  echo "FAIL parquet-row-group0-col0-total-uncompressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_total_uncompressed_size=237$'; then
  echo "FAIL parquet-row-group0-col1-total-uncompressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_total_uncompressed_size=255$'; then
  echo "FAIL parquet-row-group0-col2-total-uncompressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_total_uncompressed_size=372$'; then
  echo "FAIL parquet-row-group0-col3-total-uncompressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_page_header_type=DATA_PAGE$'; then
  echo "FAIL parquet-row-group0-col0-page-header-type"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_page_header_type=DATA_PAGE$'; then
  echo "FAIL parquet-row-group0-col1-page-header-type"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_page_header_type=DATA_PAGE$'; then
  echo "FAIL parquet-row-group0-col2-page-header-type"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_page_header_type=DATA_PAGE$'; then
  echo "FAIL parquet-row-group0-col3-page-header-type"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_page_header_uncompressed_size=321$'; then
  echo "FAIL parquet-row-group0-col0-page-header-uncompressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_page_header_uncompressed_size=218$'; then
  echo "FAIL parquet-row-group0-col1-page-header-uncompressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_page_header_uncompressed_size=236$'; then
  echo "FAIL parquet-row-group0-col2-page-header-uncompressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_page_header_uncompressed_size=353$'; then
  echo "FAIL parquet-row-group0-col3-page-header-uncompressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_page_header_compressed_size=93$'; then
  echo "FAIL parquet-row-group0-col0-page-header-compressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_page_header_compressed_size=84$'; then
  echo "FAIL parquet-row-group0-col1-page-header-compressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_page_header_compressed_size=92$'; then
  echo "FAIL parquet-row-group0-col2-page-header-compressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_page_header_compressed_size=90$'; then
  echo "FAIL parquet-row-group0-col3-page-header-compressed-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_page_header_num_values=5$'; then
  echo "FAIL parquet-row-group0-col0-page-header-num-values"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_page_header_num_values=5$'; then
  echo "FAIL parquet-row-group0-col1-page-header-num-values"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_page_header_num_values=5$'; then
  echo "FAIL parquet-row-group0-col2-page-header-num-values"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_page_header_num_values=5$'; then
  echo "FAIL parquet-row-group0-col3-page-header-num-values"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_page_header_length=19$'; then
  echo "FAIL parquet-row-group0-col0-page-header-length"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_page_header_length=19$'; then
  echo "FAIL parquet-row-group0-col1-page-header-length"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_page_header_length=19$'; then
  echo "FAIL parquet-row-group0-col2-page-header-length"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_page_header_length=19$'; then
  echo "FAIL parquet-row-group0-col3-page-header-length"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_page_payload_offset=23$'; then
  echo "FAIL parquet-row-group0-col0-page-payload-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_page_payload_offset=135$'; then
  echo "FAIL parquet-row-group0-col1-page-payload-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_page_payload_offset=238$'; then
  echo "FAIL parquet-row-group0-col2-page-payload-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_page_payload_offset=349$'; then
  echo "FAIL parquet-row-group0-col3-page-payload-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_page_data_encoding=DELTA_LENGTH_BYTE_ARRAY$'; then
  echo "FAIL parquet-row-group0-col0-page-data-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_page_data_encoding=DELTA_LENGTH_BYTE_ARRAY$'; then
  echo "FAIL parquet-row-group0-col1-page-data-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_page_data_encoding=DELTA_LENGTH_BYTE_ARRAY$'; then
  echo "FAIL parquet-row-group0-col2-page-data-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_page_data_encoding=DELTA_LENGTH_BYTE_ARRAY$'; then
  echo "FAIL parquet-row-group0-col3-page-data-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_page_definition_level_encoding=RLE$'; then
  echo "FAIL parquet-row-group0-col0-page-definition-level-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_page_definition_level_encoding=RLE$'; then
  echo "FAIL parquet-row-group0-col1-page-definition-level-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_page_definition_level_encoding=RLE$'; then
  echo "FAIL parquet-row-group0-col2-page-definition-level-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_page_definition_level_encoding=RLE$'; then
  echo "FAIL parquet-row-group0-col3-page-definition-level-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_page_repetition_level_encoding=RLE$'; then
  echo "FAIL parquet-row-group0-col0-page-repetition-level-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_page_repetition_level_encoding=RLE$'; then
  echo "FAIL parquet-row-group0-col1-page-repetition-level-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_page_repetition_level_encoding=RLE$'; then
  echo "FAIL parquet-row-group0-col2-page-repetition-level-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_page_repetition_level_encoding=RLE$'; then
  echo "FAIL parquet-row-group0-col3-page-repetition-level-encoding"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_page_payload_magic=28B52FFD$'; then
  echo "FAIL parquet-row-group0-col0-page-payload-magic"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_page_payload_magic=28B52FFD$'; then
  echo "FAIL parquet-row-group0-col1-page-payload-magic"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_page_payload_magic=28B52FFD$'; then
  echo "FAIL parquet-row-group0-col2-page-payload-magic"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_page_payload_magic=28B52FFD$'; then
  echo "FAIL parquet-row-group0-col3-page-payload-magic"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_zstd_frame_header_size=7$'; then
  echo "FAIL parquet-row-group0-col0-zstd-frame-header-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_zstd_frame_header_size=6$'; then
  echo "FAIL parquet-row-group0-col1-zstd-frame-header-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_zstd_frame_header_size=6$'; then
  echo "FAIL parquet-row-group0-col2-zstd-frame-header-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_zstd_frame_header_size=7$'; then
  echo "FAIL parquet-row-group0-col3-zstd-frame-header-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_zstd_first_block_type=COMPRESSED$'; then
  echo "FAIL parquet-row-group0-col0-zstd-first-block-type"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_zstd_first_block_type=COMPRESSED$'; then
  echo "FAIL parquet-row-group0-col1-zstd-first-block-type"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_zstd_first_block_type=COMPRESSED$'; then
  echo "FAIL parquet-row-group0-col2-zstd-first-block-type"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_zstd_first_block_type=COMPRESSED$'; then
  echo "FAIL parquet-row-group0-col3-zstd-first-block-type"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_zstd_first_block_last_flag=1$'; then
  echo "FAIL parquet-row-group0-col0-zstd-first-block-last-flag"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_zstd_first_block_last_flag=1$'; then
  echo "FAIL parquet-row-group0-col1-zstd-first-block-last-flag"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_zstd_first_block_last_flag=1$'; then
  echo "FAIL parquet-row-group0-col2-zstd-first-block-last-flag"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_zstd_first_block_last_flag=1$'; then
  echo "FAIL parquet-row-group0-col3-zstd-first-block-last-flag"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_zstd_first_block_size=83$'; then
  echo "FAIL parquet-row-group0-col0-zstd-first-block-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_zstd_first_block_size=75$'; then
  echo "FAIL parquet-row-group0-col1-zstd-first-block-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_zstd_first_block_size=83$'; then
  echo "FAIL parquet-row-group0-col2-zstd-first-block-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_zstd_first_block_size=80$'; then
  echo "FAIL parquet-row-group0-col3-zstd-first-block-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_zstd_first_block_header_size=3$'; then
  echo "FAIL parquet-row-group0-col0-zstd-first-block-header-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_zstd_first_block_header_size=3$'; then
  echo "FAIL parquet-row-group0-col1-zstd-first-block-header-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_zstd_first_block_header_size=3$'; then
  echo "FAIL parquet-row-group0-col2-zstd-first-block-header-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_zstd_first_block_header_size=3$'; then
  echo "FAIL parquet-row-group0-col3-zstd-first-block-header-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_zstd_first_block_payload_offset=33$'; then
  echo "FAIL parquet-row-group0-col0-zstd-first-block-payload-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_zstd_first_block_payload_offset=144$'; then
  echo "FAIL parquet-row-group0-col1-zstd-first-block-payload-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_zstd_first_block_payload_offset=247$'; then
  echo "FAIL parquet-row-group0-col2-zstd-first-block-payload-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_zstd_first_block_payload_offset=359$'; then
  echo "FAIL parquet-row-group0-col3-zstd-first-block-payload-offset"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_zstd_frame_accounted_size=93$'; then
  echo "FAIL parquet-row-group0-col0-zstd-frame-accounted-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_zstd_frame_accounted_size=84$'; then
  echo "FAIL parquet-row-group0-col1-zstd-frame-accounted-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_zstd_frame_accounted_size=92$'; then
  echo "FAIL parquet-row-group0-col2-zstd-frame-accounted-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_zstd_frame_accounted_size=90$'; then
  echo "FAIL parquet-row-group0-col3-zstd-frame-accounted-size"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_zstd_frame_size_matches_page=1$'; then
  echo "FAIL parquet-row-group0-col0-zstd-frame-size-matches-page"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_zstd_frame_size_matches_page=1$'; then
  echo "FAIL parquet-row-group0-col1-zstd-frame-size-matches-page"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_zstd_frame_size_matches_page=1$'; then
  echo "FAIL parquet-row-group0-col2-zstd-frame-size-matches-page"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_zstd_frame_size_matches_page=1$'; then
  echo "FAIL parquet-row-group0-col3-zstd-frame-size-matches-page"
  printf '%s\n' "${output}"
  exit 1
fi

for idx in 0 1 2 3; do
  if ! printf '%s\n' "${output}" | rg -q "^row_group0_col${idx}_decompressed_payload_len="; then
    echo "FAIL parquet-row-group0-col${idx}-decompressed-payload-len"
    printf '%s\n' "${output}"
    exit 1
  fi
  if ! printf '%s\n' "${output}" | rg -q "^row_group0_col${idx}_first_level_section_len=2$"; then
    echo "FAIL parquet-row-group0-col${idx}-first-level-section-len"
    printf '%s\n' "${output}"
    exit 1
  fi
  if ! printf '%s\n' "${output}" | rg -q "^row_group0_col${idx}_dlba_values_offset=6$"; then
    echo "FAIL parquet-row-group0-col${idx}-dlba-values-offset"
    printf '%s\n' "${output}"
    exit 1
  fi
  if ! printf '%s\n' "${output}" | rg -q "^row_group0_col${idx}_dlba_values_prefix=80100805"; then
    echo "FAIL parquet-row-group0-col${idx}-dlba-values-prefix"
    printf '%s\n' "${output}"
    exit 1
  fi
  if ! printf '%s\n' "${output}" | rg -q "^row_group0_col${idx}_dlba_block_size=2048$"; then
    echo "FAIL parquet-row-group0-col${idx}-dlba-block-size"
    printf '%s\n' "${output}"
    exit 1
  fi
  if ! printf '%s\n' "${output}" | rg -q "^row_group0_col${idx}_dlba_miniblocks=8$"; then
    echo "FAIL parquet-row-group0-col${idx}-dlba-miniblocks"
    printf '%s\n' "${output}"
    exit 1
  fi
  if ! printf '%s\n' "${output}" | rg -q "^row_group0_col${idx}_dlba_value_count=5$"; then
    echo "FAIL parquet-row-group0-col${idx}-dlba-value-count"
    printf '%s\n' "${output}"
    exit 1
  fi
done

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_dlba_first_length=27$'; then
  echo "FAIL parquet-row-group0-col0-dlba-first-length"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_dlba_first_length=27$'; then
  echo "FAIL parquet-row-group0-col1-dlba-first-length"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_dlba_first_length=25$'; then
  echo "FAIL parquet-row-group0-col2-dlba-first-length"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_dlba_first_length=34$'; then
  echo "FAIL parquet-row-group0-col3-dlba-first-length"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_dlba_first_min_delta=-12$'; then
  echo "FAIL parquet-row-group0-col0-dlba-first-min-delta"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_dlba_first_min_delta=-1$'; then
  echo "FAIL parquet-row-group0-col1-dlba-first-min-delta"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_dlba_first_min_delta=-18$'; then
  echo "FAIL parquet-row-group0-col2-dlba-first-min-delta"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_dlba_first_min_delta=-27$'; then
  echo "FAIL parquet-row-group0-col3-dlba-first-min-delta"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col0_dlba_first_bit_width=5$'; then
  echo "FAIL parquet-row-group0-col0-dlba-first-bit-width"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col1_dlba_first_bit_width=2$'; then
  echo "FAIL parquet-row-group0-col1-dlba-first-bit-width"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col2_dlba_first_bit_width=5$'; then
  echo "FAIL parquet-row-group0-col2-dlba-first-bit-width"
  printf '%s\n' "${output}"
  exit 1
fi

if ! printf '%s\n' "${output}" | rg -q '^row_group0_col3_dlba_first_bit_width=6$'; then
  echo "FAIL parquet-row-group0-col3-dlba-first-bit-width"
  printf '%s\n' "${output}"
  exit 1
fi

for expected in \
  'row_group0_col0_dlba_length_0=27' \
  'row_group0_col0_dlba_length_1=27' \
  'row_group0_col0_dlba_length_2=25' \
  'row_group0_col0_dlba_length_3=37' \
  'row_group0_col0_dlba_length_4=25' \
  'row_group0_col1_dlba_length_0=27' \
  'row_group0_col1_dlba_length_1=26' \
  'row_group0_col1_dlba_length_2=26' \
  'row_group0_col1_dlba_length_3=28' \
  'row_group0_col1_dlba_length_4=27' \
  'row_group0_col2_dlba_length_0=25' \
  'row_group0_col2_dlba_length_1=7' \
  'row_group0_col2_dlba_length_2=5' \
  'row_group0_col2_dlba_length_3=9' \
  'row_group0_col2_dlba_length_4=10' \
  'row_group0_col3_dlba_length_0=34' \
  'row_group0_col3_dlba_length_1=34' \
  'row_group0_col3_dlba_length_2=34' \
  'row_group0_col3_dlba_length_3=7' \
  'row_group0_col3_dlba_length_4=32'
do
  if ! printf '%s\n' "${output}" | rg -q "^${expected}$"; then
    echo "FAIL parquet-${expected}"
    printf '%s\n' "${output}"
    exit 1
  fi
done

for expected in \
  'row_group0_col0_dlba_value_data_offset=174' \
  'row_group0_col1_dlba_value_data_offset=78' \
  'row_group0_col2_dlba_value_data_offset=174' \
  'row_group0_col3_dlba_value_data_offset=206' \
  'row_group0_col0_dlba_value_0=<https://example.org/alice>' \
  'row_group0_col0_dlba_value_1=<https://example.org/alice>' \
  'row_group0_col0_dlba_value_2=<https://example.org/bob>' \
  'row_group0_col0_dlba_value_3=<https://example.org/default-subject>' \
  'row_group0_col0_dlba_value_4=<https://example.org/doc>' \
  'row_group0_col1_dlba_value_0=<https://example.org/knows>' \
  'row_group0_col1_dlba_value_1=<https://example.org/name>' \
  'row_group0_col1_dlba_value_2=<https://example.org/name>' \
  'row_group0_col1_dlba_value_3=<https://example.org/status>' \
  'row_group0_col1_dlba_value_4=<https://example.org/title>' \
  'row_group0_col2_dlba_value_0=<https://example.org/bob>' \
  'row_group0_col2_dlba_value_1="Alice"' \
  'row_group0_col2_dlba_value_2="Bob"' \
  'row_group0_col2_dlba_value_3="default"' \
  'row_group0_col2_dlba_value_4="Specimen"' \
  'row_group0_col3_dlba_value_0=<https://example.org/graph/people>' \
  'row_group0_col3_dlba_value_1=<https://example.org/graph/people>' \
  'row_group0_col3_dlba_value_2=<https://example.org/graph/people>' \
  'row_group0_col3_dlba_value_3=DEFAULT' \
  'row_group0_col3_dlba_value_4=<https://example.org/graph/docs>'
do
  if ! printf '%s\n' "${output}" | rg -q "^${expected}$"; then
    echo "FAIL parquet-${expected}"
    printf '%s\n' "${output}"
    exit 1
  fi
done

if ! printf '%s\n' "${output}" | rg -q '^meta_string=duckdb_schema$'; then
  echo "FAIL parquet-metadata-strings"
  printf '%s\n' "${output}"
  exit 1
fi

echo "PASS parquet-magic"
echo "PASS parquet-metadata-len"
echo "PASS parquet-num-rows"
echo "PASS parquet-row-groups"
echo "PASS parquet-row-group0-num-rows"
echo "PASS parquet-row-group0-columns"
echo "PASS parquet-row-group0-col0-name"
echo "PASS parquet-row-group0-col0-data-page-offset"
echo "PASS parquet-row-group0-col1-name"
echo "PASS parquet-row-group0-col2-name"
echo "PASS parquet-row-group0-col3-name"
echo "PASS parquet-row-group0-col1-data-page-offset"
echo "PASS parquet-row-group0-col2-data-page-offset"
echo "PASS parquet-row-group0-col3-data-page-offset"
echo "PASS parquet-row-group0-col0-compression"
echo "PASS parquet-row-group0-col1-compression"
echo "PASS parquet-row-group0-col2-compression"
echo "PASS parquet-row-group0-col3-compression"
echo "PASS parquet-row-group0-col0-num-values"
echo "PASS parquet-row-group0-col1-num-values"
echo "PASS parquet-row-group0-col2-num-values"
echo "PASS parquet-row-group0-col3-num-values"
echo "PASS parquet-row-group0-col0-total-compressed-size"
echo "PASS parquet-row-group0-col1-total-compressed-size"
echo "PASS parquet-row-group0-col2-total-compressed-size"
echo "PASS parquet-row-group0-col3-total-compressed-size"
echo "PASS parquet-row-group0-col0-total-uncompressed-size"
echo "PASS parquet-row-group0-col1-total-uncompressed-size"
echo "PASS parquet-row-group0-col2-total-uncompressed-size"
echo "PASS parquet-row-group0-col3-total-uncompressed-size"
echo "PASS parquet-row-group0-col0-page-header-type"
echo "PASS parquet-row-group0-col1-page-header-type"
echo "PASS parquet-row-group0-col2-page-header-type"
echo "PASS parquet-row-group0-col3-page-header-type"
echo "PASS parquet-row-group0-col0-page-header-uncompressed-size"
echo "PASS parquet-row-group0-col1-page-header-uncompressed-size"
echo "PASS parquet-row-group0-col2-page-header-uncompressed-size"
echo "PASS parquet-row-group0-col3-page-header-uncompressed-size"
echo "PASS parquet-row-group0-col0-page-header-compressed-size"
echo "PASS parquet-row-group0-col1-page-header-compressed-size"
echo "PASS parquet-row-group0-col2-page-header-compressed-size"
echo "PASS parquet-row-group0-col3-page-header-compressed-size"
echo "PASS parquet-row-group0-col0-page-header-num-values"
echo "PASS parquet-row-group0-col1-page-header-num-values"
echo "PASS parquet-row-group0-col2-page-header-num-values"
echo "PASS parquet-row-group0-col3-page-header-num-values"
echo "PASS parquet-row-group0-col0-page-header-length"
echo "PASS parquet-row-group0-col1-page-header-length"
echo "PASS parquet-row-group0-col2-page-header-length"
echo "PASS parquet-row-group0-col3-page-header-length"
echo "PASS parquet-row-group0-col0-page-payload-offset"
echo "PASS parquet-row-group0-col1-page-payload-offset"
echo "PASS parquet-row-group0-col2-page-payload-offset"
echo "PASS parquet-row-group0-col3-page-payload-offset"
echo "PASS parquet-row-group0-col0-page-data-encoding"
echo "PASS parquet-row-group0-col1-page-data-encoding"
echo "PASS parquet-row-group0-col2-page-data-encoding"
echo "PASS parquet-row-group0-col3-page-data-encoding"
echo "PASS parquet-row-group0-col0-page-definition-level-encoding"
echo "PASS parquet-row-group0-col1-page-definition-level-encoding"
echo "PASS parquet-row-group0-col2-page-definition-level-encoding"
echo "PASS parquet-row-group0-col3-page-definition-level-encoding"
echo "PASS parquet-row-group0-col0-page-repetition-level-encoding"
echo "PASS parquet-row-group0-col1-page-repetition-level-encoding"
echo "PASS parquet-row-group0-col2-page-repetition-level-encoding"
echo "PASS parquet-row-group0-col3-page-repetition-level-encoding"
echo "PASS parquet-row-group0-col0-page-payload-magic"
echo "PASS parquet-row-group0-col1-page-payload-magic"
echo "PASS parquet-row-group0-col2-page-payload-magic"
echo "PASS parquet-row-group0-col3-page-payload-magic"
echo "PASS parquet-row-group0-col0-zstd-frame-header-size"
echo "PASS parquet-row-group0-col1-zstd-frame-header-size"
echo "PASS parquet-row-group0-col2-zstd-frame-header-size"
echo "PASS parquet-row-group0-col3-zstd-frame-header-size"
echo "PASS parquet-row-group0-col0-zstd-first-block-type"
echo "PASS parquet-row-group0-col1-zstd-first-block-type"
echo "PASS parquet-row-group0-col2-zstd-first-block-type"
echo "PASS parquet-row-group0-col3-zstd-first-block-type"
echo "PASS parquet-row-group0-col0-zstd-first-block-last-flag"
echo "PASS parquet-row-group0-col1-zstd-first-block-last-flag"
echo "PASS parquet-row-group0-col2-zstd-first-block-last-flag"
echo "PASS parquet-row-group0-col3-zstd-first-block-last-flag"
echo "PASS parquet-row-group0-col0-zstd-first-block-size"
echo "PASS parquet-row-group0-col1-zstd-first-block-size"
echo "PASS parquet-row-group0-col2-zstd-first-block-size"
echo "PASS parquet-row-group0-col3-zstd-first-block-size"
echo "PASS parquet-row-group0-col0-zstd-first-block-header-size"
echo "PASS parquet-row-group0-col1-zstd-first-block-header-size"
echo "PASS parquet-row-group0-col2-zstd-first-block-header-size"
echo "PASS parquet-row-group0-col3-zstd-first-block-header-size"
echo "PASS parquet-row-group0-col0-zstd-first-block-payload-offset"
echo "PASS parquet-row-group0-col1-zstd-first-block-payload-offset"
echo "PASS parquet-row-group0-col2-zstd-first-block-payload-offset"
echo "PASS parquet-row-group0-col3-zstd-first-block-payload-offset"
echo "PASS parquet-row-group0-col0-zstd-frame-accounted-size"
echo "PASS parquet-row-group0-col1-zstd-frame-accounted-size"
echo "PASS parquet-row-group0-col2-zstd-frame-accounted-size"
echo "PASS parquet-row-group0-col3-zstd-frame-accounted-size"
echo "PASS parquet-row-group0-col0-zstd-frame-size-matches-page"
echo "PASS parquet-row-group0-col1-zstd-frame-size-matches-page"
echo "PASS parquet-row-group0-col2-zstd-frame-size-matches-page"
echo "PASS parquet-row-group0-col3-zstd-frame-size-matches-page"
echo "PASS parquet-row-group0-col0-decompressed-payload-len"
echo "PASS parquet-row-group0-col1-decompressed-payload-len"
echo "PASS parquet-row-group0-col2-decompressed-payload-len"
echo "PASS parquet-row-group0-col3-decompressed-payload-len"
echo "PASS parquet-row-group0-col0-first-level-section-len"
echo "PASS parquet-row-group0-col1-first-level-section-len"
echo "PASS parquet-row-group0-col2-first-level-section-len"
echo "PASS parquet-row-group0-col3-first-level-section-len"
echo "PASS parquet-row-group0-col0-dlba-values-offset"
echo "PASS parquet-row-group0-col1-dlba-values-offset"
echo "PASS parquet-row-group0-col2-dlba-values-offset"
echo "PASS parquet-row-group0-col3-dlba-values-offset"
echo "PASS parquet-row-group0-col0-dlba-values-prefix"
echo "PASS parquet-row-group0-col1-dlba-values-prefix"
echo "PASS parquet-row-group0-col2-dlba-values-prefix"
echo "PASS parquet-row-group0-col3-dlba-values-prefix"
echo "PASS parquet-row-group0-col0-dlba-block-size"
echo "PASS parquet-row-group0-col1-dlba-block-size"
echo "PASS parquet-row-group0-col2-dlba-block-size"
echo "PASS parquet-row-group0-col3-dlba-block-size"
echo "PASS parquet-row-group0-col0-dlba-miniblocks"
echo "PASS parquet-row-group0-col1-dlba-miniblocks"
echo "PASS parquet-row-group0-col2-dlba-miniblocks"
echo "PASS parquet-row-group0-col3-dlba-miniblocks"
echo "PASS parquet-row-group0-col0-dlba-value-count"
echo "PASS parquet-row-group0-col1-dlba-value-count"
echo "PASS parquet-row-group0-col2-dlba-value-count"
echo "PASS parquet-row-group0-col3-dlba-value-count"
echo "PASS parquet-row-group0-col0-dlba-first-length"
echo "PASS parquet-row-group0-col1-dlba-first-length"
echo "PASS parquet-row-group0-col2-dlba-first-length"
echo "PASS parquet-row-group0-col3-dlba-first-length"
echo "PASS parquet-row-group0-col0-dlba-first-min-delta"
echo "PASS parquet-row-group0-col1-dlba-first-min-delta"
echo "PASS parquet-row-group0-col2-dlba-first-min-delta"
echo "PASS parquet-row-group0-col3-dlba-first-min-delta"
echo "PASS parquet-row-group0-col0-dlba-first-bit-width"
echo "PASS parquet-row-group0-col1-dlba-first-bit-width"
echo "PASS parquet-row-group0-col2-dlba-first-bit-width"
echo "PASS parquet-row-group0-col3-dlba-first-bit-width"
echo "PASS parquet-row-group0-col0-dlba-length-stream"
echo "PASS parquet-row-group0-col1-dlba-length-stream"
echo "PASS parquet-row-group0-col2-dlba-length-stream"
echo "PASS parquet-row-group0-col3-dlba-length-stream"
echo "PASS parquet-row-group0-col0-dlba-values"
echo "PASS parquet-row-group0-col1-dlba-values"
echo "PASS parquet-row-group0-col2-dlba-values"
echo "PASS parquet-row-group0-col3-dlba-values"
echo "PASS parquet-metadata-strings"
