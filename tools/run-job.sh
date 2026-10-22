#!/usr/bin/env bash
# Runs a long job (Kani, Verus, big builds) with receipts, so a job that dies leaves evidence.
# The stage G loop search ran for 35 minutes, died, and left nothing but a truncated .out in an
# untracked directory; this wrapper exists so that cannot happen silently again.
#
#   tools/run-job.sh NAME -- command args...
#
# Writes tools/receipts/NAME.start before running and tools/receipts/NAME.end (with exit code
# and duration) after. render-state.sh reports any .start without an .end.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
[ "$#" -ge 3 ] && [ "$2" = "--" ] || { echo "usage: tools/run-job.sh NAME -- command..." >&2; exit 1; }
name=$1; shift 2
mkdir -p tools/receipts
log="tools/receipts/$name.log"
t0=$(date +%s)
printf 'started: %s\nhead: %s\ncommand: %s\nlog: %s\n' \
  "$(date -Is)" "$(git rev-parse --short HEAD)" "$*" "$log" > "tools/receipts/$name.start"
"$@" > "$log" 2>&1
rc=$?
printf 'ended: %s\nexit: %s\nseconds: %s\n' "$(date -Is)" "$rc" "$(( $(date +%s) - t0 ))" \
  > "tools/receipts/$name.end"
echo "$name: exit $rc ($(( $(date +%s) - t0 )) s), log $log"
exit $rc
