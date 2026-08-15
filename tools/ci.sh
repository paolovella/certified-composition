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

# The stage D combinator is an executable, so `lake build` on the library does not cover
# it. Build it and run it on the emission corpus: a parser that stops parsing real bytes
# is the one failure the Lean samples cannot catch.
step "certcompose builds and consumes the emission" \
     bash -c 'cd conf-typing && lake build certcompose >/dev/null 2>&1 &&
              ./.lake/build/bin/certcompose corpus/jasmin/accept.expected \
                | grep -q "^  SCT level:  #secret"'

# The cross-check crate is an independent re-implementation used as an adversary. Its
# concrete witnesses are cheap and must not rot; the Kani harnesses are minutes-long and are
# run by hand, not here. Skipped when cargo is absent so the Lean gates still run.
if command -v cargo >/dev/null 2>&1; then
  step "cross-check witnesses (independent Rust port)" \
       bash -c 'cd cross-check/leak-kani && cargo test --quiet 2>&1 | grep -q "test result: ok"'
fi

# Stage K's verified checker. Verus is not assumed present (it is not on PATH by default
# here); when it is, the file must verify and the binary must still decide correctly.
VERUS_BIN="${VERUS:-/home/paolo/verus/verus-bin/verus-x86-linux/verus}"
if [ -x "$VERUS_BIN" ]; then
  step "verus lcheck verifies and runs" \
       bash -c 'cd cross-check/verus && "'"$VERUS_BIN"'" --compile lcheck.rs -o lcheck-bin 2>&1 \
                  | grep -q "0 errors" &&
                ./lcheck-bin > /tmp/lcheck-verdicts.txt &&
                grep -q "^alloc p ; free p .*ACCEPT" /tmp/lcheck-verdicts.txt &&
                grep -q "^alloc p  *REFUSE"          /tmp/lcheck-verdicts.txt &&
                grep -q "^b06 (CWE-401) *REFUSE"     /tmp/lcheck-verdicts.txt &&
                grep -q "^b06, repaired *ACCEPT"     /tmp/lcheck-verdicts.txt'
fi

step "no sorry in our sources"     bash -c '! git ls-files "*.lean" | xargs grep -n "\\bsorry\\b"'
step "check-claims (drift guards)" bash -c 'bash tools/check-claims.sh | tail -1 | grep -q "^check-claims: clean$"'
step "guard-selftest (the guards actually fire)" \
     bash -c 'bash tools/guard-selftest.sh | tail -1 | grep -qE "^guard self-test: [0-9]+ passed, 0 failed$"'
step "walk-check (numeric claims in the notes)" \
     bash -c 'python3 tools/walk-check.py | tail -1 | grep -q "^all checks PASS$"'

printf '\n'
if [ "$fail" = 0 ]; then printf 'CI: all steps passed\n'; else printf 'CI: FAILURES ABOVE\n'; fi
exit "$fail"
