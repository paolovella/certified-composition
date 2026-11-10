---
id: SPEC-02
title: "Row 9 on bytes: no secret leaks under branch misprediction, on the literal image in the speculating model"
ring: 1
tier: G-X
milestone: M6 (2027-03-19)
deps: [SPEC-01]
closes: ['VULN-COVERAGE §3.0 row 9: bcheck_relW holds on ucmdLangW and is carried by no pass']
acceptance: a checker on the slice language whose acceptance gives Cert.rel on the literal image in rvSpecLang by transfer alone, for every directive stream; accepted: verify16 and HChaCha20 as they are, or with a stated mask; refused: a bounds-checked load indexed by an input, whose image leaks in the model under one directive stream, by decide
kill: if the checker refuses code that ctCheck accepts and that has no speculative leak in the model, measure how much on the certified programs and report before changing a rule
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track A, 2027-03-08 to 2027-03-19. The rule to start from is `ConfTyping.bcheck_relW` (`SpecL.lean`).

1. `sctCheck` on `Slice2.Prog`: `ctCheck`, and in addition no load or store whose address depends on a value that a mispredicted branch could have let through. The starting form is the simple one: every memory index is public on both arms of every enclosing branch.
2. Soundness at the source's speculating semantics, for every directive stream.
3. The image, by `SPEC-01`'s pass certificates.
4. Witnesses and mutants. The vacuity witness is the gadget of `S-SPEC`.

**Fourth in the cut order** (`PLAN-2026-11` §5): the narrow form is `rel` for the attacker who mispredicts conditional branches, and nothing about `bound`.

**Not claimed:** anything about a real processor. The claim is about the model, and the contract says what a processor must do for the model to describe it.

## Log
