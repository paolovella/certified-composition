#!/usr/bin/env bash
# tools/ring0.lock (P0-03): what the frozen statements mean, hashed.
#   tools/ring0-lock.sh          rewrite tools/ring0.lock (only with the user's key: it is Ring 0)
#   tools/ring0-lock.sh --check  fail, showing the diff, if anything it covers has changed
# Two parts: the SHA-256 of the challenge and its comparator config, and one structural hash per
# definition in the frozen statements' dependency closure (tools/gate/Ring0Lock.lean). The second
# part is why the lock exists: a statement is weakened as surely by editing `CostAtMost` as by
# editing its text.
set -euo pipefail
cd "$(git rev-parse --show-toplevel 2>/dev/null || dirname "$(dirname "$(readlink -f "$0")")")"
fresh=$(mktemp)
trap 'rm -f "$fresh"' EXIT
{
  for f in workspace/Statements.lean comparator.json; do
    printf 'file\t%s\t%s\n' "$f" "$(sha256sum "$f" | cut -d' ' -f1)"
  done
  lake build StatementsProof >/dev/null 2>&1 || { echo "ring0-lock: StatementsProof does not build" >&2; exit 1; }
  lake env lean tools/gate/Ring0Lock.lean
} > "$fresh"
if [ "${1:-}" = --check ]; then
  if ! diff -u tools/ring0.lock "$fresh"; then
    echo "ring0-lock: tools/ring0.lock does not match; a frozen statement or a definition it rests on changed (needs the user's key)"
    exit 1
  fi
  echo "ring0-lock: current ($(grep -c . "$fresh") entries)"
else
  cp "$fresh" tools/ring0.lock
  echo "ring0-lock: wrote tools/ring0.lock ($(grep -c . "$fresh") entries)"
fi
