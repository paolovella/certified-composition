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
  # A mutation that fails (for instance one that checks its own anchor matched) is reported: a
  # case whose mutation did not apply passes vacuously (P0-03 found one).
  if ! ( cd "$tmp" && "$@" ) >/dev/null 2>&1; then
    printf '  FAIL  %-38s the mutation did not apply\n' "$name"; fail=$((fail+1)); rm -rf "$tmp"; return
  fi
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

# stage H. Dropping the overflow guard makes Alloy "refute" a proved theorem, which is the
# most misleading failure available here.
run_case "Alloy model drops overflow bound" drift \
  bash -c 'sed -i "/^pred small/,/^}/d" cross-check/alloy/BoundedGrade.als'

# stage G. A negative result whose vacuity witness has gone missing is the failure mode.
run_case "vacuity witness harness removed" drift \
  bash -c 'sed -i "s/fn accepted_programs_can_allocate/fn gone_away/" \
             cross-check/leak-kani/src/lib.rs'

run_case "cross-check drops the loop bound caveat" drift \
  bash -c 'sed -i "s/loop. IS modelled, bounded/loops are fully covered/" \
             cross-check/leak-kani/src/lib.rs'

# stage K. Making the spec talk about the machine word is the transliteration trap the
# stage's kill criterion names, and it would still verify.
run_case "Verus spec becomes a transliteration" drift \
  bash -c 'sed -i "s/spec_step(tag: u8, x: nat, o: Set<nat>) -> Option<Set<nat>>/spec_step(tag: u8, x: nat, o: u8) -> Option<u8>/" \
             cross-check/verus/lcheck.rs'

# stage K, the loop rule. This is the one claim that went stale in the DOCUMENT while the
# code was right, so the document half is tested as well as the code half.
run_case "Verus loses the loop fixpoint clause" drift \
  bash -c 'sed -i "s/p\[i\].tag == T_LOOP/p[i].tag == T_NEVER/" cross-check/verus/lcheck.rs'

run_case "plan re-denies the verified loop rule" drift \
  bash -c 'sed -i "s/^- \*\*Done, third pass — the loop rule\*\*/- **Still not done.** the fixpoint rule is not in the verified implementation/" \
             PLAN-MULTITOOL.md'

run_case "loop body index stops being checked" drift \
  bash -c 'sed -i "s/n.tag == T_LOOP \&\& n.l >= p.len()/false/" cross-check/verus/lcheck.rs'

run_case "accepted-loop witness removed" drift \
  bash -c 'sed -i "s/theorem loop_balanced_accepted/theorem gone_away/" \
             conf-typing/ConfTyping/LeakCert.lean'

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

# cross-tool tripwire must not vanish silently
run_case "cross-tool tripwire renamed" drift \
  bash -c 'sed -i "s/cn_jasmin_obligations_disjoint/RENAMED_X/g" conf-typing/ConfTyping/CrossToolIndex.lean'

# transport-kernel module must be mentioned in its README
run_case "kernel module undocumented" drift \
  bash -c 'sed -i "s/OmegaOneCoherent.lean/OTHER.lean/g" transport-kernel/README.md'

# the axiom manifest (P0-01): a footprint change must reach the doc claim, and a non-standard
# axiom must never pass, however it got into the build
run_case "claimed choice-free theorem gains choice" drift \
  bash -c 'sed -i "s/^\(ConfTyping\.wsecTy_sound\t[^\t]*\t\).*/\1Classical.choice,Quot.sound,propext/" tools/axioms.expected'

run_case "axiom-free claim on a propext theorem" drift \
  bash -c 'sed -i "s/\`med_victim_bypasses\` (propext-only;/\`med_victim_bypasses\` (axiom-free;/" VULN-COVERAGE.md'

run_case "sorryAx appears in the manifest" drift \
  bash -c 'sed -i "s/^\(ConfTyping\.uexec_seq_eq\t[^\t]*\t\).*/\1sorryAx/" tools/axioms.expected'

run_case "manifest deleted" drift \
  bash -c 'rm tools/axioms.expected'

run_case "module claim breaks" drift \
  bash -c 'sed -i "0,/^ConfTyping\.[^\t]*\tConfTyping\.MinimalCompose\t/s/^\(ConfTyping\.[^\t]*\tConfTyping\.MinimalCompose\t\).*/\1Classical.choice/" tools/axioms.expected'

# the process guards (PLAN-2026-10 s10): each one is broken the way it would rot
run_case "CLAUDE.md loses the plan of record" drift \
  bash -c 'sed -i "s/PLAN-2026-10.md/PLAN-OLD.md/g" CLAUDE.md'

run_case "kill switch set to a bogus value" drift \
  bash -c 'echo yolo > AUTONOMY'

run_case "backlog item loses its status" drift \
  bash -c 'sed -i "/^status: /d" backlog/P0-01.md'

run_case "backlog item gets an unknown status" drift \
  bash -c 'sed -i "s/^status: .*/status: someday/" backlog/P0-01.md'

run_case "hook script deleted" drift \
  bash -c 'rm tools/hooks/stop.sh'

run_case "job receipts dropped from run-job" drift \
  bash -c 'sed -i "s/\.end/.fin/g" tools/run-job.sh'

run_case "BEq Int pin deleted" drift \
  bash -c 'sed -i "/^instance (priority := high) intBEqOfDecEq/d" conf-typing/ConfTyping/Imp.lean'

run_case "Std.le_refl erasure deleted" drift \
  bash -c 'sed -i "/^attribute \[-simp\] Std.le_refl$/d" conf-typing/ConfTyping/MemSafe.lean'

run_case "README states a stale toolchain" drift \
  bash -c 'sed -i "s/(v4\.35\.0), mathlib-free/(v4.31.0), mathlib-free/" conf-typing/README.md'

run_case "root toolchain drifts from packages" drift \
  bash -c 'echo leanprover/lean4:v4.34.0 > lean-toolchain'

run_case "transport-kernel toolchain drifts back" drift \
  bash -c 'echo leanprover/lean4:v4.31.0 > transport-kernel/lean-toolchain'

run_case "run-job loses its signal trap" drift \
  bash -c 'sed -i "/^for sig in TERM INT HUP; do$/,/^done$/d" tools/run-job.sh'

run_case "base gate stops classifying CLAUDE.md" drift \
  bash -c 'sed -i "s/\"CLAUDE.md\", //" tools/gate/base-gate.sh'

run_case "a checker gains a mutation site" drift \
  bash -c 'sed -i "s/^  | _,  .skip => true\$/  | _,  .skip => if true then true else false/" conf-typing/ConfTyping/SecTyD.lean'

run_case "the challenge gains a def" drift \
  bash -c 'printf "\nnamespace ConfTyping\ndef frozenHole : Nat := sorry\nend ConfTyping\n" >> workspace/Statements.lean'

run_case "a challenge sorry hides inside a proof" drift \
  bash -c 'sed -i "0,/ := sorry\$/s// := by exact sorry/" workspace/Statements.lean'

run_case "a file imports the challenge" drift \
  bash -c 'sed -i "s/^import TransportCalculus\$/import TransportCalculus\nimport Statements/" workspace/StatementsProof.lean'

run_case "comparator.json drops a frozen name" drift \
  bash -c 'python3 -c "import json;c=json.load(open(\"comparator.json\"));c[\"theorem_names\"].pop();json.dump(c,open(\"comparator.json\",\"w\"))"'

run_case "CLAUDE.md adds a Ring 0 path the gate lacks" drift \
  bash -c 'sed -i "s/^frozen statement file\.\$/\`l-core\/\`, and frozen statement file./" CLAUDE.md && grep -q "^\`l-core/\`, and frozen statement file\.\$" CLAUDE.md'

run_case "the README raises the checker limit" drift \
  bash -c 'sed -i "s/if it touches at most 3 checkers/if it touches at most 9 checkers/" README.md && grep -q "at most 9 checkers" README.md'

run_case "ring0.lock loses a definition the README counts" drift \
  bash -c 'sed -i "\$d" tools/ring0.lock'

echo
echo "guard self-test: $pass passed, $fail failed"
[ "$fail" -eq 0 ] || exit 1
