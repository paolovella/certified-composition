#!/usr/bin/env bash
# The witness registry (P0-04): every checker must have an accepted and a refused witness.
#   tools/witnesses.sh          rewrite tools/witnesses.expected
#   tools/witnesses.sh --check  fail if a checker lacks either witness, or if the committed table
#                               is stale (show the diff)
# The table is committed so that a checker losing a witness, or a new checker arriving without
# one, is a reviewed diff and not a silent count.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
fresh=$(mktemp)
trap 'rm -f "$fresh"' EXIT
( cd conf-typing && lake env lean WitnessRegistry.lean ) > "$fresh"
summary=$(tail -1 "$fresh")
case "$summary" in
  "registry: "*" checkers, 0 missing a witness") ok=1 ;;
  "registry: "*) ok=0 ;;
  *) echo "witnesses: the registry did not run: $summary"; exit 1 ;;
esac
if [ "${1:-}" = "--check" ]; then
  if [ "$ok" = 0 ]; then
    awk -F'\t' 'NF>=3 && ($2==0 || $3==0) {print "  " $1 ": accepted " $2 ", refused " $3}' "$fresh"
    echo "witnesses: $summary"
    exit 1
  fi
  if ! diff -u tools/witnesses.expected "$fresh"; then
    echo "witnesses: tools/witnesses.expected is stale; run tools/witnesses.sh and review the diff"
    exit 1
  fi
  echo "witnesses: $summary"
else
  cp "$fresh" tools/witnesses.expected
  echo "witnesses: wrote tools/witnesses.expected ($summary)"
fi
