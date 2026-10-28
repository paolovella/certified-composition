---
id: EXPR-03
title: "Path-correlated allocation: free under the same public flag that allocated"
ring: 1
tier: G-X
deps: [S-EXPR]
closes: ['S-EXPR follow-up']
acceptance: blind program 18 is accepted; a program that frees under a different flag, or under a flag reassigned in between, is refused
kill: -
status: planned
---

## Plan

At an `if`, `bcheck` keeps the intersection of both branches' tracked pointers (`interStr`),
so a pointer allocated under `flag` and freed under the same `flag` is refused. PLAN-2026-08
§1.2 lists this rule; S-EXPR's 18 hit it blind.

Plan (to be refined before code):
1. Design first: a tracked entry may carry a guard, the public variable whose non-zero value it
   depends on. It is valid while that variable is unwritten. `ite` on the same variable
   discharges the guard in the then-branch.
2. Measure the cost before committing to it: this touches the memory invariant
   (`FullCert`), and the soundness proof is the expensive part. Kill: if it needs a change to
   any frozen statement's meaning, stop and open a G-0 item.
3. Witnesses: the accepted 18; refused if the flag differs or is reassigned between the two
   `if`s.
