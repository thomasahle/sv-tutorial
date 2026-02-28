#!/usr/bin/env bash
# test-sv-lessons.sh — compile and simulate every SV lesson, checking that
#   • the solution files produce PASS output, and
#   • the starter (incomplete) files do NOT produce PASS output.
#
# Requirements: native circt-verilog and circt-sim binaries.
# Default location: vendor/circt/build-native/bin/
# Override: CIRCT_VERILOG=/path/to/circt-verilog CIRCT_SIM=/path/to/circt-sim
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LESSONS_DIR="$REPO_ROOT/src/lessons/sv"

CIRCT_VERILOG="${CIRCT_VERILOG:-$REPO_ROOT/vendor/circt/build-native/bin/circt-verilog}"
CIRCT_SIM="${CIRCT_SIM:-$REPO_ROOT/vendor/circt/build-native/bin/circt-sim}"

if [[ ! -x "$CIRCT_VERILOG" ]]; then
  echo "ERROR: circt-verilog not found: $CIRCT_VERILOG"
  echo "Build native tools first, or set CIRCT_VERILOG=/path/to/binary"
  exit 1
fi
if [[ ! -x "$CIRCT_SIM" ]]; then
  echo "ERROR: circt-sim not found: $CIRCT_SIM"
  echo "Build native tools first, or set CIRCT_SIM=/path/to/binary"
  exit 1
fi

VERILOG_FLAGS=(--ir-llhd --timescale 1ns/1ns --single-unit)

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

pass=0
fail=0
skip=0

# ─── helpers ──────────────────────────────────────────────────────────────────

red()   { printf '\033[31m%s\033[0m' "$*"; }
green() { printf '\033[32m%s\033[0m' "$*"; }
dim()   { printf '\033[2m%s\033[0m'  "$*"; }

# compile_and_sim <label> <sv-file>...
# Compiles the given SV files to MLIR and simulates with top=tb.
# Prints simulation stdout+stderr. Returns compile exit code on error.
compile_and_sim() {
  local label="$1"; shift
  local mlir="$WORK/${label}.mlir"
  local compile_log="$WORK/${label}.compile.log"

  if ! "$CIRCT_VERILOG" "${VERILOG_FLAGS[@]}" "$@" -o "$mlir" \
       >"$compile_log" 2>&1; then
    printf 'COMPILE_ERROR\n'
    cat "$compile_log"
    return 0
  fi

  "$CIRCT_SIM" --top tb "$mlir" 2>&1 || true
}

# has_pass <output>  — true if any line starts with "PASS"
has_pass() { echo "$1" | grep -q "^PASS"; }

# ─── main loop ────────────────────────────────────────────────────────────────

printf '\n%s\n' "$(dim "circt: $CIRCT_VERILOG")"
printf '%s\n\n' "$(dim "lessons: $LESSONS_DIR")"

for lesson_dir in "$LESSONS_DIR"/*/; do
  lesson="$(basename "$lesson_dir")"

  # Skip description-only lessons (no testbench)
  if [[ ! -f "$lesson_dir/tb.sv" ]]; then
    printf '  %s %s\n' "$(dim "SKIP")" "$(dim "$lesson (no testbench)")"
    (( skip++ )) || true
    continue
  fi

  # Collect starter files (.sv but not .sol.sv)
  mapfile -t starter_files < <(
    find "$lesson_dir" -maxdepth 1 -name "*.sv" ! -name "*.sol.sv" | sort
  )

  # Collect solution files (.sol.sv)
  mapfile -t sol_files < <(
    find "$lesson_dir" -maxdepth 1 -name "*.sol.sv" | sort
  )

  if [[ ${#sol_files[@]} -eq 0 ]]; then
    printf '  %s %s\n' "$(dim "SKIP")" "$(dim "$lesson (no solution file)")"
    (( skip++ )) || true
    continue
  fi

  printf '%-32s' "$lesson"

  # ── solution run ──────────────────────────────────────────────────────────
  # For each starter .sv, substitute the .sol.sv if one exists;
  # keep all other starters (e.g. sram.sv) unchanged.
  solution_files=()
  for f in "${starter_files[@]}"; do
    base="$(basename "$f" .sv)"
    sol_counterpart="$lesson_dir/${base}.sol.sv"
    if [[ -f "$sol_counterpart" ]]; then
      solution_files+=("$sol_counterpart")
    else
      solution_files+=("$f")
    fi
  done

  sol_out="$(compile_and_sim "${lesson}-sol" "${solution_files[@]}")"

  if has_pass "$sol_out"; then
    printf ' %s' "$(green "sol=PASS")"
    (( pass++ )) || true
  else
    printf '\n  %s solution: expected PASS\n' "$(red "FAIL")"
    echo "$sol_out" | sed 's/^/    /'
    (( fail++ )) || true
  fi

  # ── starter run ───────────────────────────────────────────────────────────
  start_out="$(compile_and_sim "${lesson}-start" "${starter_files[@]}")"

  if echo "$start_out" | grep -q "^COMPILE_ERROR"; then
    printf '  %s\n' "$(green "start=FAIL(compile)")"
    (( pass++ )) || true
  elif has_pass "$start_out"; then
    printf '\n  %s starter: unexpectedly printed PASS\n' "$(red "FAIL")"
    echo "$start_out" | sed 's/^/    /'
    (( fail++ )) || true
  else
    printf '  %s\n' "$(green "start=FAIL")"
    (( pass++ )) || true
  fi
done

# ─── summary ──────────────────────────────────────────────────────────────────

printf '\n%s\n' "─────────────────────────────────"
if [[ $fail -eq 0 ]]; then
  printf '%s  %d passed, %d skipped\n' "$(green "ALL PASS")" "$pass" "$skip"
else
  printf '%s  %d passed, %d failed, %d skipped\n' \
    "$(red "FAILURES")" "$pass" "$fail" "$skip"
fi
printf '%s\n' "─────────────────────────────────"

[[ $fail -eq 0 ]]
