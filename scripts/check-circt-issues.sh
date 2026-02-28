#!/usr/bin/env bash
# Polls thomasnormal/circt issues blocking tutorial lessons for state changes.
# Usage: ./scripts/check-circt-issues.sh [--loop]
#   --loop  : run every 5 minutes until interrupted (default: check once)
#
# Tracked issues (open):
#   #14  virtual if in separate file → compiler crash  (UVM driver/env/monitor/coverage lessons)
#   #20  interface signal writes in tasks don't drive DUT  (sv/tasks-functions)
#   #21  UVM run_phase phase-cleanup deadlock  (uvm/constrained-random, sequence)
#   #22  class-level constraints ignored on plain randomize()  (uvm/seq-item)
#   #23  UVM factory type_id::set_type_override() no effect  (uvm/factory-override)

set -uo pipefail

BASELINE_FILE="${XDG_CACHE_HOME:-$HOME/.cache}/circt-issue-baseline.txt"

fetch_state() {
  gh api repos/thomasnormal/circt/issues \
    --jq '.[] | select(.number | IN(14,20,21,22,23)) | "\(.number)|\(.state)|\(.comments)|\(.updated_at)"' \
    2>/dev/null | grep -v '^$' | sort -t'|' -k1,1n
}

print_issues() {
  gh api repos/thomasnormal/circt/issues \
    --jq '.[] | select(.number | IN(14,20,21,22,23)) | "#\(.number) [\(.state)] \(.title)  (comments:\(.comments), updated:\(.updated_at))"' \
    2>/dev/null | sort -t'#' -k2,2n
}

check_once() {
  local current
  current=$(fetch_state)

  echo "=== thomasnormal/circt open issues (blocking tutorial) ==="
  print_issues
  echo

  if [[ -f "$BASELINE_FILE" ]]; then
    local prev
    prev=$(cat "$BASELINE_FILE")
    if [[ "$current" != "$prev" ]]; then
      echo "⚡ CHANGES DETECTED since last check:"
      diff <(echo "$prev") <(echo "$current") 2>/dev/null | grep '^[<>]' | while IFS= read -r line; do
        local num state comments updated
        IFS='|' read -r num state comments updated <<< "${line:2}"
        echo "  Issue #$num: state=$state comments=$comments updated=$updated"
      done
      echo
    else
      echo "(no changes since last check)"
    fi
  fi

  echo "$current" > "$BASELINE_FILE"
}

if [[ "${1:-}" == "--loop" ]]; then
  echo "Monitoring circt issues #14, #20-#23 (every 5 min, Ctrl+C to stop)…"
  while true; do
    echo
    echo "[$(date '+%H:%M:%S')]"
    check_once
    sleep 300
  done
else
  check_once
fi
