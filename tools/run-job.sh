#!/usr/bin/env bash
# Runs a long job (Kani, Verus, big builds) with receipts, so a job that dies leaves evidence.
# The stage G loop search ran for 35 minutes, died, and left nothing but a truncated .out in an
# untracked directory; this wrapper exists so that cannot happen silently again.
#
#   tools/run-job.sh NAME -- command args...
#
# Writes tools/receipts/NAME.start before running and tools/receipts/NAME.end (with exit code
# and duration) after. render-state.sh reports any .start without an .end.
#
# A TERM, INT or HUP still writes the .end receipt (exit "signal NAME"), and the signal is passed
# on to the job. I-0002: a `pkill -f` whose pattern matched this wrapper's own command line
# killed it while it waited in the foreground, and bash defers traps until a foreground child
# exits, so the job is run in the background and waited for. Only SIGKILL leaves no .end, and
# render-state.sh reports that. RUNJOB_ROOT overrides the repo root (the self-test uses it).
set -uo pipefail
cd "${RUNJOB_ROOT:-$(git rev-parse --show-toplevel)}"
[ "$#" -ge 3 ] && [ "$2" = "--" ] || { echo "usage: tools/run-job.sh NAME -- command..." >&2; exit 1; }
name=$1; shift 2
mkdir -p tools/receipts
log="tools/receipts/$name.log"
t0=$(date +%s)
printf 'started: %s\nhead: %s\ncommand: %s\nlog: %s\n' \
  "$(date -Is)" "$(git rev-parse --short HEAD)" "$*" "$log" > "tools/receipts/$name.start"
finish() {
  printf 'ended: %s\nexit: %s\nseconds: %s\n' "$(date -Is)" "$1" "$(( $(date +%s) - t0 ))" \
    > "tools/receipts/$name.end"
  echo "$name: exit $1 ($(( $(date +%s) - t0 )) s), log $log"
}
"$@" > "$log" 2>&1 &
child=$!
for sig in TERM INT HUP; do
  trap "kill -$sig $child 2>/dev/null; wait $child 2>/dev/null; finish 'signal $sig'; exit 143" "$sig"
done
wait "$child"
rc=$?
finish "$rc"
exit $rc
