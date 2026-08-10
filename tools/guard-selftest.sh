#!/usr/bin/env bash
# Mutation self-test for tools/check-claims.sh.
#
# Why this exists: a guard was once spliced into check-claims.sh by an edit that
# silently failed, so the guard never landed — and its negative tests passed
# *vacuously*, reporting success. A guard that cannot fail is worse than no guard,
# because it is believed. This script breaks the repo in one known way per guard
# family and asserts that check-claims.sh notices each time.
#
# Runs against an export of the **working tree** (tracked + untracked-not-ignored),
# not of HEAD: a self-test that checks the last commit instead of what you are about
# to commit is the same "believed but ineffective" failure it exists to prevent —
# which is exactly how it first behaved. It never touches the worktree and never
# copies .lake.
set -u
cd "$(dirname "$0")/.." || exit 1
REPO=$(pwd)
pass=0; fail=0

run_case() {                      # run_case <name> <expect: pass|drift> <mutation...>
  local name="$1" expect="$2"; shift 2
  local tmp; tmp=$(mktemp -d)
  ( cd "$REPO" && git ls-files -co --exclude-standard -z \
      | tar --null -T - -cf - ) 2>/dev/null | tar -x -C "$tmp" 2>/dev/null
  ( cd "$tmp" && "$@" ) >/dev/null 2>&1
  local out; out=$(cd "$tmp" && bash tools/check-claims.sh 2>&1)
  local got="pass"; echo "$out" | grep -q "^DRIFT" && got="drift"
  if [ "$got" = "$expect" ]; then
    printf '  ok    %-38s (%s)\n' "$name" "$got"; pass=$((pass+1))
  else
    printf '  FAIL  %-38s expected %s, got %s\n' "$name" "$expect" "$got"; fail=$((fail+1))
  fi
  rm -rf "$tmp"
}

echo "guard self-test — each case breaks one guard family and expects it to fire"

# 0. The unmutated export must be clean, or every result below is meaningless.
run_case "pristine worktree export" pass true

# 1. retired-phrase guard
run_case "retired phrase resurfaces" drift \
  bash -c 'printf "\nremaining brick\n" >> README.md'

# 1b. top-level README must mention each tier-bearing module/note
run_case "top README drops a module" drift \
  bash -c 'sed -i "s/OmegaOneCoherent/REMOVED_NAME/g" README.md'

# 1b-prime. machine-checked set-theory names must exist in the Lean
run_case "set-theory theorem renamed" drift \
  bash -c 'sed -i "s/omega1_downDip_trivial/renamed_away/g" \
             transport-kernel/TransportKernel/OmegaOneCoherent.lean'

# 1b-second. READMEs must reference the latest notes section
run_case "README falls behind the notes" drift \
  bash -c 'sed -i "s/§57/§56/g" README.md transport-calculus/README.md'

# 1b4. the class count must match the documented convention
run_case "class count contradicts §2½" drift \
  bash -c 'sed -i "s/bricks, sixteen classes)/bricks, fifteen classes)/" VULN-COVERAGE.md'

# 1c. every Lean name VULN-COVERAGE cites must exist
run_case "cited VULN theorem renamed" drift \
  bash -c 'sed -i "s/theorem medCheck_sound/theorem gone_away/" \
             conf-typing/ConfTyping/Mediation.lean'

# module-import guard
run_case "brick module not imported" drift \
  bash -c 'sed -i "/import ConfTyping.Mediation/d" conf-typing/ConfTyping.lean'

# required README headings: the stage-1i failure - a splice that ate its own anchor
run_case "README heading spliced away" drift \
  bash -c 'sed -i "/^## \xc2\xa711 pre-mechanization checklist/d" conf-typing/README.md'

# the independence claim must stay qualified where it is made
run_case "no-interaction claim unqualified" drift \
  bash -c 'sed -i "s/ni_and_memory_do_not_factor/that other theorem/" \
             transport-calculus/TransportCalculus.lean'

# 1g. duplicate name in the flat namespace
run_case "duplicate top-level name" drift \
  bash -c 'printf "\ntheorem medCheck_sound : True := trivial\n" >> conf-typing/ConfTyping/Race.lean'

# transport-kernel module must be mentioned in its README
run_case "kernel module undocumented" drift \
  bash -c 'sed -i "s/OmegaOneCoherent.lean/OTHER.lean/g" transport-kernel/README.md'

echo
echo "guard self-test: $pass passed, $fail failed"
[ "$fail" -eq 0 ] || exit 1
