#!/usr/bin/env bash
# Witnesses for the witness registry (P0-04). Each case copies conf-typing, changes one thing,
# rebuilds, and runs WitnessRegistry.lean; the expected count of checkers missing a witness
# must come out. Without the refused cases, `0 missing` would also be printed by a registry
# that finds nothing.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
REPO=$(pwd)
pass=0; fail=0
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
W=ConfTyping/Witnesses.lean

case_() {  # case_ NAME EXPECTED_SUMMARY MUTATION...
  local name=$1 want=$2; shift 2
  local d="$tmp/$name"
  mkdir -p "$d" && cp -a "$REPO/conf-typing" "$d/" && cp -a "$REPO/transport-calculus" "$d/"
  ( cd "$d/conf-typing" && "$@" ) >/dev/null 2>&1
  local got
  got=$(cd "$d/conf-typing" && lake build >/dev/null 2>&1 && lake env lean WitnessRegistry.lean 2>&1 | tail -1)
  if [ "$got" = "$want" ]; then
    printf '  ok    %-40s %s\n' "$name" "$got"; pass=$((pass+1))
  else
    printf '  FAIL  %-40s expected "%s", got "%s"\n' "$name" "$want" "$got"; fail=$((fail+1))
  fi
  rm -rf "$d"
}

echo "registry witnesses"
n=$(tail -1 tools/witnesses.expected | sed -E 's/^registry: ([0-9]+) checkers.*/\1/')
case_ unchanged "registry: $n checkers, 0 missing a witness" true
case_ witness-deleted "registry: $n checkers, 1 missing a witness" \
  sed -i '/^theorem wcheck_accepts_skip/d' "$W"
case_ checker-without-witness "registry: $((n+1)) checkers, 1 missing a witness" \
  bash -c "sed -i 's/^end ConfTyping\$/def gateWitnessCheck : Nat → Bool := fun _ => true\n\nend ConfTyping/' $W"
case_ forall-witness-ignored "registry: $n checkers, 1 missing a witness" \
  sed -i 's/^theorem wcheck_accepts_skip : wcheck Phigh .skip = true := by decide$/theorem wcheck_accepts_skip : ∀ _n : Nat, wcheck Phigh .skip = true := fun _ => by decide/' "$W"

echo "registry witnesses: $pass passed, $fail failed"
[ "$fail" = 0 ]
