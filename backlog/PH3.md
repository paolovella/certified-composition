---
id: PH3
title: "Release candidate, L core v1: one language, the 1.0 statements frozen, Ring 0 v1 locked with the user's key"
ring: 0
tier: G-0
milestone: RC (2027-04-16)
deps: [PH1, F6, UNI-01, MUSEUM-01, FLAG-01]
closes: ['13 non-composing languages; abort-in-loop divergence; Int pointers']
acceptance: Ring 0 v1 frozen with the user's key; inductive Cmd count outside museum = 1
kill: -
status: planned
---

## Plan

Re-scoped on 2026-11-10 by [`PLAN-2026-11`](../PLAN-2026-11.md) §3, milestone RC, 2027-04-12 to 2027-04-16. The acceptance is unchanged. What "L core v1" contains is narrower than `PLAN-2026-10` §12 had it, and the log says by how much.

1. **One language**: `MUSEUM-01`'s move and its guard.
2. **The 1.0 statements** enter `workspace/Statements.lean`: `UNI-01`'s theorem, the flagship's, and each row's transfer. Each is proposed with its `stmt_strengthens` where it replaces an older one.
3. **Ring 0 v1 is locked**: `tools/ring0-lock.sh` over the kernel, the gates, the RV64 model and the hardware contract, and the READING notes' pinned inputs. One key merge.
4. **Route 2** runs on the frozen statements, as `ROUTE2-01` decided on 2026-12-01.
5. `bash tools/ci.sh` green here and in Actions, from a clean clone.

After the lock, a change to Ring 0 is a version: v1.1, with its own record.

## Log
- 2026-11-10, **re-scoped and unblocked.**
  - The title before: "Phase 3 L core v1: W64, sorts, halting abort, PrimTable, Wire, proof-carrying validators, 13 languages to 1". Deps before: [PH1, S-PRIM, F6]. Status before: `blocked`, with the plan "See PLAN-2026-10.md".
  - **Kept:** 13 languages to 1; the lock with the user's key; the word type, which the slice already has (`W32-01` reads `uint32_t` over it).
  - **Not in v1, parked with records:** the primitive table (`S-PRIM`) and the Wire format; L's own syntax (`LSYN-01`). The slice's source is C read by the front end.
  - **Still open from the old title, and stated here so it is not lost:** "halting abort" (an abort inside a loop diverging) was a defect of `UCmd`. Whether the slice language has it is checked in `HEAP-02` step 2, where faults are settled.
