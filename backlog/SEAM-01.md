---
id: SEAM-01
title: "Row 12 on bytes: two checked components in sequence are a checked program, and the image is the image of the whole"
ring: 1
tier: G-X
milestone: M7 (2027-03-26)
deps: [UNI-01]
closes: ['VULN-COVERAGE §3.0 row 12: bcheck_seam holds on UCmd; on bytes only passes compose']
acceptance: a theorem that from lcheck a and lcheck b, under a stated condition on what a leaves for b, gives lcheck (a ;; b), so the image of the sequence carries every row; a witness of two components that are each accepted and whose sequence is refused because the condition fails, with its leaking image
kill: -
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2027-03-08 to 2027-03-12. The rule to start from is `ConfTyping.bcheck_seam` (`SeamL.lean`).

1. The condition at the seam: the rights, taints, ownership states and budget that `a` ends with are those `b` starts from.
2. The theorem, by the checkers' own sequencing arms.
3. The witness: `a` ends with a tainted buffer, and `b` assumes it clean.

**Not claimed:** separate compilation. The two components are compiled together, as one program. Linking two images is `PH6`, which is parked.

## Log
