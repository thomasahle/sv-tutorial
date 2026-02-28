#!/usr/bin/env bash
# Polls thomasnormal/circt issues #8-#13 for state changes.
# Usage: ./scripts/check-circt-issues.sh [--loop]
#   --loop  : run every 5 minutes until interrupted (default: check once)

set -uo pipefail

ISSUES=(8 9 10 11 12 13)
BASELINE_FILE="${XDG_CACHE_HOME:-$HOME/.cache}/circt-issue-baseline.txt"

fetch_state() {
  gh api repos/thomasnormal/circt/issues \
    --jq '.[] | select(.number | IN(8,9,10,11,12,13)) | "\(.number)|\(.state)|\(.comments)|\(.updated_at)"' \
    2>/dev/null | grep -v '^$' | sort -t'|' -k1,1n
}

print_issues() {
  gh api repos/thomasnormal/circt/issues \
    --jq '.[] | select(.number | IN(8,9,10,11,12,13)) | "#\(.number) [\(.state)] \(.title)  (comments:\(.comments), updated:\(.updated_at))"' \
    2>/dev/null | sort -t'#' -k2,2n
}

check_once() {
  local current
  current=$(fetch_state)

  echo "=== thomasnormal/circt issues #8-#13 ==="
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
  echo "Monitoring circt issues #8-#13 (every 5 min, Ctrl+C to stop)…"
  while true; do
    echo
    echo "[$(date '+%H:%M:%S')]"
    check_once
    sleep 300
  done
else
  check_once
fi
