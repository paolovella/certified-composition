#!/usr/bin/env bash
# Parse the boundary warden's answer (P0-12), fail-closed.
#   tools/gate/warden-verdict.sh FILE
# The last non-blank line must be exactly `WARDEN: clear` (exit 0) or `WARDEN: escalate`
# (exit 1). Anything else, an empty answer included, counts as escalate: the warden is an
# agent, so only its escalation is believed, and a clear it did not plainly give is not one.
set -uo pipefail
[ $# -eq 1 ] || { echo "usage: warden-verdict.sh FILE"; exit 2; }
last=$(grep -v '^[[:space:]]*$' "$1" 2>/dev/null | tail -1 | tr -d '\r')
case "$last" in
  "WARDEN: clear")    echo "warden: clear"; exit 0 ;;
  "WARDEN: escalate") echo "warden: ESCALATE, needs the user's key"; exit 1 ;;
  *) echo "warden: MALFORMED answer, counted as escalate (last line: ${last:0:80})"; exit 1 ;;
esac
