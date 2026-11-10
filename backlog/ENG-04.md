---
id: ENG-04
title: "Two scheduled adversaries: every checker's mutants and every QEMU comparison rerun on a schedule, with a finding opening an item"
ring: 0
tier: G-0
milestone: M2 (2026-12-18)
deps: [CI-03, P0-06]
closes: ['PLAN-2026-10 §8: the challenge engine; mutants and QEMU comparisons run when a session remembers them']
acceptance: a scheduled workflow on the heavy runner runs each l-core and conf-typing mutant script and each QEMU differential, with fresh random inputs and a recorded seed; a surviving mutant or a disagreement fails the run, writes an incident and opens a backlog item; planted - a checker rule weakened on a branch is caught by the schedule, and a model edited to disagree with QEMU is caught; a run that did not happen is reported as missing, not as green
kill: -
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2026-12-14 to 2026-12-18. This is challenge engine v1, reduced to the two adversaries that already exist as scripts.

1. **Mutants:** `slice2_mut`, `slice2_low_mut`, `ctout_mut`, `cfront_mut`, `boundr_mut`, `tools/mutants.py`. Each has a baseline that must build first.
2. **Differential:** `rv_diff.py` and `w32_diff.py` with new random cases each night. The seed is in the receipt, so a failure reproduces.
3. **Capped:** each child runs under a time limit and a memory limit, and its process group is killed on timeout. The box is shared.
4. **Missing runs:** `STATE.md` prints the last run's date, and `check-claims` fails if it is more than 3 days old while `AUTONOMY` is not `off`.

**Not in 1.0:** the agent adversary that writes new attacks, and the frozen-statement challenge beyond what `workspace/Statements.lean` holds today.

## Log
