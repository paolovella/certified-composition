#!/usr/bin/env bash
# Witnesses for the base-branch gate (P0-06). BASE is this working tree; each case builds a PR
# tree from it with one change and expects the gate's verdict on that check.
#
#   tools/gate/base-gate-witness.sh          the quick cases (ring0, manifest, checkers,
#                                            mutants), seconds
#   tools/gate/base-gate-witness.sh --full   also the two that run ci.sh (~10 min each)
#
# The full refused case is the one PLAN-2026-10 §14 names: a PR that rewrites tools/ci.sh to
# `exit 0` and breaks a proof. Its own ci.sh passes it, which is the vacuity witness; the gate,
# running BASE's ci.sh, must fail it.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
REPO=$(pwd)
FULL=0; [ "${1:-}" = --full ] && FULL=1
pass=0; fail=0
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

mkpr() {  # mkpr DIR: a PR tree identical to this working tree, with its .git and caches
  mkdir -p "$1"
  ( cd "$REPO" && git ls-files -co --exclude-standard -z | tar --null -T - -cf - ) | tar -x -C "$1"
  cp -a "$REPO/.git" "$1/.git"
  local c
  for c in .lake conf-typing/.lake transport-calculus/.lake; do
    [ -d "$REPO/$c" ] && mkdir -p "$1/$(dirname "$c")" && cp -a "$REPO/$c" "$1/$c"
  done
  return 0
}

case_() {  # case_ NAME ONLY EXPECT_RC EXPECT_LINE MUTATION...
  local name=$1 only=$2 want=$3 line=$4; shift 4
  local d="$tmp/$name"; mkpr "$d"
  ( cd "$d" && "$@" ) >/dev/null 2>&1
  local out rc
  out=$(GATE_ONLY="$only" bash "$REPO/tools/gate/base-gate.sh" "$REPO" "$d" 2>&1); rc=$?
  if [ "$rc" = "$want" ] && echo "$out" | grep -q -- "$line"; then
    printf '  ok    %-44s %s\n' "$name" "$line"; pass=$((pass+1))
  else
    printf '  FAIL  %-44s expected rc %s and "%s", got rc %s\n' "$name" "$want" "$line" "$rc"
    echo "$out" | sed 's/^/        /' | tail -15; fail=$((fail+1))
  fi
  rm -rf "$d"
}

echo "base-gate witnesses"
case_ unchanged-pr-quick "ring0 manifest" 0 "^gate: ring0 untouched$" true
case_ unchanged-pr-manifest "manifest" 0 "^gate: manifest additions only (0 added)$" true
case_ pr-adds-manifest-line "manifest" 0 "^gate: manifest additions only (1 added)$" \
  bash -c 'printf "Witness.new\tWitness\t\n" >> tools/axioms.expected'
case_ pr-touches-claude-md "ring0" 1 "^gate: ring0 TOUCHED" \
  bash -c 'echo "an agent edit" >> CLAUDE.md'
case_ pr-touches-toolchain "ring0" 1 "^  conf-typing/lean-toolchain$" \
  bash -c 'echo leanprover/lean4:v4.34.0 > conf-typing/lean-toolchain'
case_ pr-touches-only-receipts "ring0" 0 "^gate: ring0 untouched$" \
  bash -c 'echo x > tools/receipts/witness-only.end'
case_ pr-drops-manifest-line "manifest" 1 "^gate: manifest lines REMOVED or CHANGED (1)" \
  bash -c 'sed -i 1d tools/axioms.expected'
case_ pr-changes-a-footprint "manifest" 1 "^gate: manifest lines REMOVED or CHANGED (1)" \
  bash -c 'sed -i "1s/\t[^\t]*$/\tpropext/" tools/axioms.expected'
# P0-11: checkers.lock and mutants.expected are data a PR may change, within the gate's rules.
# bump N: change the hash of the first entry of each of the first N checkers in checkers.lock,
# as an edit to N checkers would.
bump() {
  python3 -I - "$1" <<'EOF2'
import sys
n = int(sys.argv[1]); p = "tools/checkers.lock"
rows = open(p).read().splitlines(); done = []
for i, r in enumerate(rows):
    f = r.split("\t")
    if f[1] not in done and len(done) < n:
        done.append(f[1]); f[3] = str(int(f[3]) ^ 1); rows[i] = "\t".join(f)
assert len(done) == n
open(p, "w").write("\n".join(rows) + "\n")
EOF2
}
export -f bump
case_ pr-touches-only-checkers-lock "ring0" 0 "^gate: ring0 untouched$" bash -c 'bump 1'
case_ unchanged-pr-checkers "checkers" 0 "^gate: checkers: 0 changed (limit 3)$" true
case_ pr-changes-one-checker "checkers" 0 "^gate: checkers: 1 changed (limit 3): " bash -c 'bump 1'
case_ pr-changes-three-checkers "checkers" 0 "^gate: checkers: 3 changed (limit 3): " bash -c 'bump 3'
case_ pr-changes-four-checkers "checkers" 1 "^gate: checkers: 4 changed, over the limit of 3" bash -c 'bump 4'
# the table's own row count: a checker edit that moves sites must not break this witness
nmut=$(grep -vc '^mutants: ' "$REPO/tools/mutants.expected")
case_ pr-touches-only-mutants-table "ring0 mutants" 0 "^gate: mutants: all $nmut killed$" \
  bash -c 'sed -i "1s/:[0-9]*:/:999:/" tools/mutants.expected'
case_ pr-mutant-survives "mutants" 1 "^gate: mutants: rows not killed (1)" \
  bash -c 'sed -i "1s/\tkilled$/\tsurvived/" tools/mutants.expected'

if [ "$FULL" = 1 ]; then
  case_ unchanged-pr-full "" 0 "^gate: PASS$" true
  # the weakening PR: its own ci.sh says yes to anything, and one proof is broken.
  weaken() {
    printf '#!/usr/bin/env bash\necho "CI: all steps that ran passed"\nexit 0\n' > tools/ci.sh
    printf '\ntheorem gateWitnessBroken : (1 : Nat) = 2 := rfl\n' >> conf-typing/ConfTyping/Imp.lean
  }
  d="$tmp/vacuity"; mkpr "$d"; ( cd "$d" && weaken )
  if ( cd "$d" && bash tools/ci.sh ) >/dev/null 2>&1; then
    printf '  ok    %-44s %s\n' "weakened-pr-own-ci (vacuity)" "its own ci.sh passes it"; pass=$((pass+1))
  else
    printf '  FAIL  %-44s its own ci.sh did not pass it\n' "weakened-pr-own-ci (vacuity)"; fail=$((fail+1))
  fi
  rm -rf "$d"
  export -f weaken
  case_ weakened-pr-judged-by-base "ci" 1 "^gate: ci FAILED$" bash -c weaken
fi

echo "base-gate witnesses: $pass passed, $fail failed"
[ "$fail" = 0 ]
