#!/usr/bin/env bash
# tools/ring0.lock (P0-03) and tools/checkers.lock (P0-11): what the frozen statements mean, and
# the checkers they name, hashed.
#   tools/ring0-lock.sh             rewrite both (only with the user's key: ring0.lock is Ring 0)
#   tools/ring0-lock.sh --checkers  rewrite only tools/checkers.lock; fail if ring0.lock is stale
#   tools/ring0-lock.sh --check     fail, showing the diff, if either is stale
# ring0.lock holds the SHA-256 of the challenge and its comparator config, the list of checkers,
# and one structural hash per definition in the frozen statements' dependency closure that does
# not pass through a checker (tools/gate/Ring0Lock.lean). That part is why the lock exists: a
# statement is weakened as surely by editing `CostAtMost` as by editing its text.
# checkers.lock holds each checker's own closure. A change may rewrite it: an edit to a checker
# cannot weaken a statement, which must still be proved against ring0.lock. The base gate limits
# how many checkers one change may touch (tools/gate/base-gate.sh, CHECKER_LIMIT).
set -euo pipefail
cd "$(git rev-parse --show-toplevel 2>/dev/null || dirname "$(dirname "$(readlink -f "$0")")")"
mode=${1:-}
raw=$(mktemp) fresh=$(mktemp) freshc=$(mktemp)
trap 'rm -f "$raw" "$fresh" "$freshc"' EXIT
{
  for f in workspace/Statements.lean comparator.json; do
    printf 'file\t%s\t%s\n' "$f" "$(sha256sum "$f" | cut -d' ' -f1)"
  done
  lake build StatementsProof >/dev/null 2>&1 || { echo "ring0-lock: StatementsProof does not build" >&2; exit 1; }
  lake env lean tools/gate/Ring0Lock.lean
} > "$raw"
grep -v $'^checker\t' "$raw" > "$fresh" || true
grep $'^checker\t' "$raw" > "$freshc" || true
stale=0
if [ -n "$mode" ]; then
  if ! diff -u tools/ring0.lock "$fresh"; then
    echo "ring0-lock: tools/ring0.lock does not match; a frozen statement or a definition it rests on changed (needs the user's key)"
    exit 1
  fi
fi
case "$mode" in
  --check)
    if ! diff -u tools/checkers.lock "$freshc"; then
      echo "ring0-lock: tools/checkers.lock is stale; a checker changed: run tools/ring0-lock.sh --checkers"
      stale=1
    fi
    [ "$stale" = 0 ] || exit 1
    echo "ring0-lock: current ($(grep -c . "$fresh") entries; checkers.lock $(grep -c . "$freshc"))"
    ;;
  --checkers)
    cp "$freshc" tools/checkers.lock
    echo "ring0-lock: ring0.lock current; wrote tools/checkers.lock ($(grep -c . "$freshc") entries)"
    ;;
  "")
    cp "$fresh" tools/ring0.lock
    cp "$freshc" tools/checkers.lock
    echo "ring0-lock: wrote tools/ring0.lock ($(grep -c . "$fresh") entries) and tools/checkers.lock ($(grep -c . "$freshc"))"
    ;;
  *) echo "usage: ring0-lock.sh [--check|--checkers]"; exit 2 ;;
esac
