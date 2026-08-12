#!/usr/bin/env bash
# Everything that must hold before a commit is honest. The CI workflow calls this and
# nothing else, so what runs on push is exactly what runs locally -- the two cannot drift.
#
#   tools/ci.sh          full run (includes the mathlib package; slow)
#   tools/ci.sh --fast   skip transport-kernel (mathlib), for the inner loop
set -uo pipefail
cd "$(dirname "$0")/.."

FAST=0
[ "${1:-}" = "--fast" ] && FAST=1

fail=0
step() {
  printf '\n=== %s\n' "$1"; shift
  if "$@"; then printf '    ok\n'; else printf '    FAILED\n'; fail=1; fi
}

build() {  # build a lake package, succeed only on a clean build
  local dir="$1"
  ( cd "$dir" && lake build 2>&1 | tail -3 | grep -q "Build completed successfully" )
}

step "conf-typing builds"          build conf-typing
step "transport-calculus builds"   build transport-calculus
[ "$FAST" = 0 ] && step "transport-kernel builds (mathlib)" build transport-kernel

step "no sorry in our sources"     bash -c '! git ls-files "*.lean" | xargs grep -n "\\bsorry\\b"'
step "check-claims (drift guards)" bash -c 'bash tools/check-claims.sh | tail -1 | grep -q "^check-claims: clean$"'
step "guard-selftest (the guards actually fire)" \
     bash -c 'bash tools/guard-selftest.sh | tail -1 | grep -qE "^guard self-test: [0-9]+ passed, 0 failed$"'
step "walk-check (numeric claims in the notes)" \
     bash -c 'python3 tools/walk-check.py | tail -1 | grep -q "^all checks PASS$"'

printf '\n'
if [ "$fail" = 0 ]; then printf 'CI: all steps passed\n'; else printf 'CI: FAILURES ABOVE\n'; fi
exit "$fail"
