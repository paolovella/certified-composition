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
# NOTE: computes the current highest notes section rather than hardcoding one. An
# earlier version pinned the number and went stale the next time the notes grew, so the
# case silently stopped testing anything - caught by this suite, which is its job.
run_case "README falls behind the notes" drift \
  bash -c 'm=$(grep -oE "^## [0-9]+\." transport-calculus/NOTES-coherent-escapee.md \
               | grep -oE "[0-9]+" | sort -n | tail -1); \
           sed -i "s/§$m/§0/g" README.md transport-calculus/README.md'

# 1b4. the class count must match the documented convention
run_case "class count contradicts §2½" drift \
  bash -c 'sed -i "s/bricks, sixteen classes)/bricks, fifteen classes)/" VULN-COVERAGE.md'

# 1c. every Lean name VULN-COVERAGE cites must exist
run_case "cited VULN theorem renamed" drift \
  bash -c 'sed -i "s/theorem medCheck_sound/theorem gone_away/" \
             conf-typing/ConfTyping/Mediation.lean'

# stage 2j: the counted loop's two headline measurements
run_case "counted-loop budget changes" drift \
  bash -c 'sed -i "s/some (\\[\"db\"\\], \\[\\], 40)/some ([\"db\"], [], 41)/" conf-typing/ConfTyping/CountedLoop.lean'

# stage 2i: the fused invariant is the stage's content - if it stops carrying the
# memory-safety fields the trace theorem is no longer the one stage 2g asked for
run_case "fused invariant drops SepInv" drift \
  bash -c 'sed -i "s/^  sep  : SepInv/  sepx : SepInv/" conf-typing/ConfTyping/SpecFused.lean'

run_case "trace theorem renamed" drift \
  bash -c 'sed -i "s/theorem jcheck_strace/theorem gone_away/" conf-typing/ConfTyping/SpecFused.lean'

# stage B: the CN reception. The first three cases guard the theorems; the last two
# guard against the failure mode that actually matters here, which is not a broken
# proof but an OVERCLAIM - dropping the "we did not check this against CN" sentence,
# or dropping the hypothesis that makes the reception cost anything.
run_case "CN reception theorem renamed" drift \
  bash -c 'sed -i "s/theorem cn_comp_ledger/theorem gone_away/" \
             conf-typing/ConfTyping/CNReceive.lean'

run_case "CN reception caveat removed" drift \
  bash -c 'sed -i "s/not checked against CN/checked against CN/" \
             conf-typing/ConfTyping/CNReceive.lean'

run_case "Bridge.ofCN stops demanding frame" drift \
  bash -c 'sed -i "s/(h : ModifiesOnly f F)/(h : Frame f F)/" \
             conf-typing/ConfTyping/CNReceive.lean'

run_case "CN transcription reverts to Owned<T>" drift \
  bash -c 'sed -i "s/RW<unsigned int>/Owned<unsigned int>/g" \
             conf-typing/corpus/cn/SOURCES.md'

# stage C: the finding is a counterexample plus a sufficient condition, and a claim about
# which producer was transcribed. All three are things that go quiet rather than loud.
run_case "stage C counterexample renamed" drift \
  bash -c 'sed -i "s/theorem arch_reconciliation_insufficient/theorem gone_away/" \
             conf-typing/ConfTyping/HeteroCompose.lean'

run_case "sctGA stops intersecting" drift \
  bash -c 'sed -i "s/exact propext and_assoc/exact propext or_assoc/" \
             conf-typing/ConfTyping/HeteroCompose.lean'

run_case "stage C claims a Jasmin reception" drift \
  bash -c 'sed -i "s/modelled, not transcribed/transcribed from Jasmin/" \
             conf-typing/ConfTyping/HeteroCompose.lean'

# stage C second pass. The level PAIR is the finding; collapsing it leaves everything
# compiling and means nothing, which is the exact failure this suite exists for.
run_case "SLvl collapses to one level" drift \
  bash -c 'sed -i "/^  spec   : Lvl/d" conf-typing/ConfTyping/JasminSCT.lean'

run_case "transient/public distinction dropped" drift \
  bash -c 'sed -i "s/theorem slvl_transient_ne_public/theorem gone_away/" \
             conf-typing/ConfTyping/JasminSCT.lean'

run_case "Jasmin reception caveat removed" drift \
  bash -c 'sed -i "s/unchecked against the Jasmin checker/checked by Jasmin/" \
             conf-typing/ConfTyping/JasminSCT.lean'

run_case "Jasmin transcription loses fig3a annot" drift \
  bash -c 'sed -i "s/ptr: transient, val: transient/ptr: public, val: public/g" \
             conf-typing/corpus/jasmin/SOURCES.md'

# stage D. The emitted corpus is real tool output; the coverage figure and the
# no-native_decide rule are both things that would go quiet rather than loud.
run_case "emitted corpus edited" drift \
  bash -c 'printf "modmsf extra : #public ->\n#public\noutput corruption: #public\n constraints:\n" \
             >> conf-typing/corpus/jasmin/accept.expected'

run_case "stage D combinator theorem renamed" drift \
  bash -c 'sed -i "s/theorem compose_lvl_is_sctLvlGA/theorem gone_away/" \
             conf-typing/ConfTyping/JasminCert.lean'

run_case "native_decide creeps in" drift \
  bash -c 'printf "\nexample : 1 = 1 := by native_decide\n" >> conf-typing/ConfTyping/CNReceive.lean'

run_case "EMISSION drops the CN verdict" drift \
  bash -c 'sed -i "s/## CN — no/## CN/" conf-typing/corpus/jasmin/EMISSION.md'

# The claim template's gap list. Dropping a gap makes the bulletproof claim STRONGER
# looking and weaker in fact, which is the direction errors actually travel.
run_case "bound gap leaves the claim template" drift \
  bash -c 'sed -i "s/^- \*\*Bound gap\*\*/- **Bounded note**/" VULN-COVERAGE.md'

# stage F. The negative result and the non-factorization are the stage; both would go
# quiet rather than loud if deleted.
run_case "min-unsoundness counterexample dropped" drift \
  bash -c 'sed -i "s/theorem min_unsound/theorem gone_away/" \
             conf-typing/ConfTyping/BoundedCert.lean'

run_case "bmul stops subtracting growth" drift \
  bash -c 'sed -i "s/min i.bound (o.bound - i.growth)/min i.bound o.bound/" \
             conf-typing/ConfTyping/BoundedCert.lean'

run_case "non-factorization result dropped" drift \
  bash -c 'sed -i "s/theorem bounded_grade_does_not_factor/theorem gone_away/" \
             conf-typing/ConfTyping/BoundedCert.lean'

# The leak certificate closed the map's one admitted false-accept. Both the certificate
# and its restriction are things that would go quiet rather than loud.
run_case "leak certificate theorem renamed" drift \
  bash -c 'sed -i "s/theorem leakSafe_sound/theorem gone_away/" \
             conf-typing/ConfTyping/LeakCert.lean'

run_case "LeakFree drops the completing-run limit" drift \
  bash -c 'sed -i "s/dead = false/dead = maybe/g" conf-typing/ConfTyping/LeakCert.lean'

run_case "row 6 forgets the leak restriction" drift \
  bash -c 'sed -i "s/may still leak/is fine/" VULN-COVERAGE.md'

# stage E. The captures are real tool output; the Kani finding inverts the naive reading.
run_case "Kani unwind finding reverted" drift \
  bash -c 'sed -i "s/unwind annotation is not the bound/unwind annotation is the bound/" \
             conf-typing/corpus/estate/EMISSION.md'

run_case "Alloy receipt loses its scopes" drift \
  bash -c 'sed -i "s/scopes/bounds_removed/g" \
             conf-typing/corpus/estate/captures/alloy-receipt.json'

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

# CI and the local script must not drift
run_case "CI workflow stops calling tools/ci.sh" drift \
  bash -c 'sed -i "s#bash tools/ci.sh --fast#echo skip#" .github/workflows/ci.yml'

run_case "tools/ci.sh drops a gate" drift \
  bash -c 'sed -i "/walk-check.py/d" tools/ci.sh'

# 1g. duplicate name in the flat namespace
run_case "duplicate top-level name" drift \
  bash -c 'printf "\ntheorem medCheck_sound : True := trivial\n" >> conf-typing/ConfTyping/Race.lean'

# transport-kernel module must be mentioned in its README
run_case "kernel module undocumented" drift \
  bash -c 'sed -i "s/OmegaOneCoherent.lean/OTHER.lean/g" transport-kernel/README.md'

echo
echo "guard self-test: $pass passed, $fail failed"
[ "$fail" -eq 0 ] || exit 1
