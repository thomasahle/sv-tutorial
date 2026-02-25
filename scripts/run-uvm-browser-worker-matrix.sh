#!/usr/bin/env bash
set -euo pipefail

DEFAULT_LESSONS=(
  reporting
  seq-item
  sequence
  driver
  constrained-random
  monitor
  env
  covergroup
  cross-coverage
  coverage-driven
  factory-override
)

TRANSIENT_ERROR_RE='Execution context was destroyed|Cannot find context with specified id|Target page, context or browser has been closed|page.goto: Timeout|vite dev server did not become ready'

usage() {
  cat <<'EOF'
Usage: run-uvm-browser-worker-matrix.sh [options]

Options:
  --smoke              Run only the reporting lesson
  --full               Run the full UVM lesson matrix (default)
  --lesson <slug>      Add one lesson slug to run (repeatable)
  --lessons <csv>      Comma-separated lesson list
  --retries <n>        Retry count per lesson (default: 3)
  --log-dir <path>     Directory for per-lesson logs
EOF
}

retries="${UVM_MATRIX_RETRIES:-3}"
log_dir="${UVM_MATRIX_LOG_DIR:-}"
declare -a selected_lessons=()

while (($# > 0)); do
  case "$1" in
    --smoke)
      selected_lessons=(reporting)
      shift
      ;;
    --full)
      selected_lessons=("${DEFAULT_LESSONS[@]}")
      shift
      ;;
    --lesson)
      if (($# < 2)); then
        echo "error: --lesson requires a value" >&2
        usage
        exit 2
      fi
      selected_lessons+=("$2")
      shift 2
      ;;
    --lessons)
      if (($# < 2)); then
        echo "error: --lessons requires a value" >&2
        usage
        exit 2
      fi
      IFS=',' read -r -a csv_lessons <<<"$2"
      selected_lessons+=("${csv_lessons[@]}")
      shift 2
      ;;
    --retries)
      if (($# < 2)); then
        echo "error: --retries requires a value" >&2
        usage
        exit 2
      fi
      retries="$2"
      shift 2
      ;;
    --log-dir)
      if (($# < 2)); then
        echo "error: --log-dir requires a value" >&2
        usage
        exit 2
      fi
      log_dir="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown option: $1" >&2
      usage
      exit 2
      ;;
  esac
done

if ! [[ "$retries" =~ ^[0-9]+$ ]] || [[ "$retries" -lt 1 ]]; then
  echo "error: --retries must be a positive integer" >&2
  exit 2
fi

if ((${#selected_lessons[@]} == 0)); then
  selected_lessons=("${DEFAULT_LESSONS[@]}")
fi

if [[ -z "$log_dir" ]]; then
  log_dir="$(mktemp -d)"
else
  mkdir -p "$log_dir"
fi

echo "[uvm-matrix] logs: $log_dir"
echo "[uvm-matrix] lessons: ${selected_lessons[*]}"
echo "[uvm-matrix] retries: $retries"

failures=0

for lesson in "${selected_lessons[@]}"; do
  passed=0
  for ((attempt = 1; attempt <= retries; attempt += 1)); do
    log_file="$log_dir/${lesson}.attempt${attempt}.log"
    echo "== $lesson (attempt $attempt/$retries) =="
    if node scripts/repro-uvm-browser-worker-assert.mjs --expect-pass --simulate --lesson "$lesson" >"$log_file" 2>&1; then
      echo "PASS $lesson (attempt $attempt)"
      passed=1
      break
    fi

    if grep -Eq "$TRANSIENT_ERROR_RE" "$log_file"; then
      echo "TRANSIENT $lesson (attempt $attempt): retrying"
      sleep "$attempt"
      continue
    fi

    echo "FAIL $lesson (non-transient)"
    sed -n '1,200p' "$log_file"
    failures=$((failures + 1))
    break
  done

  if [[ "$passed" -ne 1 ]]; then
    if [[ "$failures" -eq 0 ]]; then
      echo "FAIL $lesson (transient failure persisted after $retries attempts)"
      sed -n '1,200p' "$log_dir/${lesson}.attempt${retries}.log"
      failures=$((failures + 1))
    fi
  fi
done

if [[ "$failures" -gt 0 ]]; then
  echo "[uvm-matrix] FAILED with $failures failing lesson(s)"
  exit 1
fi

echo "[uvm-matrix] PASS"
