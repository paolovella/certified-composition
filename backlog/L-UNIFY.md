---
id: L-UNIFY
title: "One language for L's certificates: combine ucmdLangI, ucmdLangW and ucmdLangH, and carry them through passes"
ring: 0
tier: G-0
deps: [F5]
closes: ['F5: certificates on separate languages, not carried through a pass']
acceptance: one lawful language of which ucmdLangS, ucmdLangI, ucmdLangW and ucmdLangH are proved special cases; one theorem giving a single program its properties together; splitPass carries them, or a recorded reason why one cannot be
kill: if re-proving splitPass over the combined language needs a new certificate shape or weakens a frozen statement, stop and bring the evidence to the user
status: planned
---

## Plan

Recorded by the user's decision of 2026-11-02. Not started: the user reviews this plan before any code,
because it can change what F6 locks.

**The gap.** F5 stated each property on its own language, and each one connects back to `ucmdLangS` on
its own (`ucmdLangI_empty`, `ucmdLangW_zero`, `ucmdLangH_strip`).
- Rows 3, 14 and 7b are on `ucmdLangI`, row 9 on `ucmdLangW`, row 6's leaks on `ucmdLangH`.
- No theorem gives one program several of these properties at once. Row 4 changes the partition, which
  is one more thing no theorem combines.
- `splitPass` is over `ucmdLangS`, so none of these certificates reaches compiled code, and L's goal is
  certificates that reach RISC-V bytes.
- `tools/ring0.lock` names `ucmdLangS` and `ucmdLangT`, and none of the three variants or `splitPass`.

**The starting design, untested.** One language with strings as an input, the window as a parameter and
the exit report included. The variants become its special cases: empty strings, window 0, the report
removed. A pass over it would carry these certificates together.

**The questions it must answer first.**
1. Is one `Lang` right, or a family indexed by attacker? Injection wants a chosen attacker and a chosen
   observer, while `rel` fixes both. `ucmdLangW` changes the cost, so `bound` cannot be the same number.
2. What does `splitPass` cost to re-prove? Its `ev_sim` and `cost_sim` would see transient commands and
   the exit report. That cost is the kill rule's measure.
3. What does F6 lock: the combined language, or the variants as they stand?

## Log
