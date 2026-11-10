---
id: MUSEUM-01
title: "The thirteen UCmd-family languages move to museum/, built and frozen, and the map is rewritten around the one language"
ring: 0
tier: G-0
milestone: RC (2027-04-16)
deps: [UNI-01]
closes: ['PLAN-2026-11 §2 points 1 and 6', 'PH3''s acceptance: inductive Cmd count outside museum = 1']
acceptance: conf-typing's languages build under museum/ with their manifests and witnesses intact; a guard counts inductive declarations matching Cmd outside museum/ and requires 1, with an accepted and a refused witness; VULN-COVERAGE §3.0 names, for each row, the theorem on bytes or a correction of record; an island table gives each package outside l-core a row (the claim about L it checks and the CI step that checks it, or the label history), and a guard fails when a package has no row, with an accepted and a refused witness; no frozen statement is weakened
kill: if a frozen statement names a declaration that the move renames, the move keeps the name; if it cannot, stop and bring the evidence to the user
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, both tracks and the user, 2027-04-12 to 2027-04-16. The move touches lakefiles, the manifests and the guards, so it is a proposal for the user's key.

1. **What moves:** the `conf-typing` package as a whole, to `museum/conf-typing`. It stays built in CI, and its theorems stay true of what they were about. Nothing in `l-core` imports it but `LAdapter`, which moves with it.
2. **What does not:** `transport-kernel`, and the kernel.
3. **The guard**, with its two witnesses.
4. **The map.** `VULN-COVERAGE.md` §3 is rewritten row by row. Each row that was stated on a `UCmd` language gets a correction of record: what it said, from when to when, and where the row now holds.
5. `tools/axioms.expected`, `witnesses.expected`, `mutants.expected` follow the paths. The ratchets' counts do not fall.
6. **The island table** (from `F5`, 2026-11-10). One row per package outside `l-core`: today `conf-typing`, `transport-kernel`, `transport-calculus`, `cross-check`, `bench`, `history` and `third_party`. Each row says what claim about L the package checks and which CI step runs it, or says "history". The table also names the top-level directories that are not code (`backlog`, `incidents`, `research`, `tools`, `workspace`), so the guard can list every top-level directory and fail on one the table does not name.

## Log
- 2026-11-10, **a clause added to the acceptance, from `F5`** ([`M0-01`](M0-01.md)). `F5` closed today with its clause "island table with a guard" not met, and no other item held it. It is here because this item is where each package is sorted into live code or built history. The acceptance before had no island clause; the rest is unchanged. Plan step 6 is new.
