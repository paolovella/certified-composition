---
id: EXPR-03
title: "Path-correlated allocation: free under the same public flag that allocated"
ring: 1
tier: G-X
deps: [S-EXPR]
closes: ['S-EXPR follow-up']
acceptance: blind program 18 is accepted; a program that frees under a different flag, or under a flag reassigned in between, is refused
kill: -
status: blocked
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

## Log

- 2026-10-28, design step. **The kill rule fires.**
  - `bcheck_sound` (frozen) must produce a `FullCert`, whose memory part is a `JSecTy`
    derivation (`HeapJoint.lean`).
  - `JSecTy`'s only rule for an `if` is `iteL`, which concludes with
    `interStr V₁ V₂`: the pointers tracked after an `if` are the intersection of the two
    branches'.
  - For program 18 (`if flag { alloc p } else { skip } ; … ; if flag { free p } else { skip }`),
    no `JSecTy` derivation keeps `p` tracked into the second `if`, whatever the checker does.
  - `JSecTy` and `FullCert` are in `tools/ring0.lock`: they are what the statements mean.
    Accepting 18 needs a change to the meaning, which is G-0, so this stops here, as the plan
    says.
- Options for the user:
  1. **A path-correlated `if` rule in `JSecTy`**, for example a pair of `if`s on the same
     public, unwritten guard. It needs the memory-safety and noninterference proofs for the
     new rule, a new `ring0.lock`, and the key. It is the most work and moves the meaning.
  2. **Leave it, documented.** The second blind author wrote 18 with the allocation and free
     inside one branch, and it was accepted (`corpus/blind/RESULTS.md`, Replication). So a
     natural alternative exists. Revisit when PH3 re-states the certificates on L's Core,
     where the meaning is being redesigned anyway.
  - Recommendation: option 2 now; carry the rule into PH3's `Cert` design.
