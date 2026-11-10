---
id: UNI-01
title: "One checker and one theorem: lcheck accepts a program, and every row's certificate holds on its literal image"
ring: 1
tier: G-X
milestone: M7 (2027-03-26)
deps: [MED-01, REL-01, INJ-01, PATH-01, HEAP-02, SPEC-02]
closes: ['F5 and L-UNIFY: the rows are certificates on separate languages', 'PLAN-2026-11 §2 point 2']
acceptance: lcheck on the slice language, the conjunction of the row checkers under one declaration of partitions, sinks, resources and budget; one theorem that takes lcheck p = true and gives each row's certificate on the literal image, with no hypothesis beyond the passes' side conditions; the theorem's statement is proposed for workspace/Statements.lean; a program refused by exactly one row for each row
kill: if two row checkers need incompatible declarations for one program, stop and report which
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2027-03-01 to 2027-03-12. The earlier shape of this on L is `ConfTyping.Unified` and `AllFive`.

1. **One declaration record**: the partition, the tenant partition, the sinks and their delimiter tables, the resources, the budget.
2. `lcheck` is the `&&` of the row checkers. No new rule.
3. The theorem is a conjunction, each part by the row item's own theorem. The work is in making the declarations agree, and in the language being one: every row item extended the same `Slice2.Cmd`.
4. **Independence witnesses**: for each row a program that every other row accepts. They show that no row's checker is implied by the others.
5. Rows that were cut are named in the theorem's doc comment and in the map, with their records.

The frozen statement is Ring 0. This item proposes it, and the user merges it at RC.

## Log
