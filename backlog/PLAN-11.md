---
id: PLAN-11
title: "The whole-project plan with dates: PLAN-2026-11, its milestones as checked data, and every item on the route filed"
ring: 0
tier: G-0
deps: [W32-01, S-USABLE]
closes: ['the user, 2026-11-10: the project has a direction and a route, but no end point and no dates']
acceptance: PLAN-2026-11.md is on master and CLAUDE.md names it as the plan of record; every id in its milestone table is a backlog item with an acceptance and a kill rule; STATE.md prints the next milestone and the days left; check-claims fails on a milestone more than 7 days past its date that is neither done nor moved, with an accepted and a refused witness in guard-selftest
kill: -
status: in-progress
---

## Plan

The user asked, on 2026-11-10, for a plan of the whole project "with clear deadlines and final product", and chose its scope in the same session:
- the final product is a general secure language, the vulnerability map carried to RV64 bytes;
- L 1.0 is tagged on 2027-04-30;
- the agent engine and speculation are in 1.0, and HChaCha20 comes first;
- the acceptance test is a request handler, and the 40 blind tasks are ported as a measure.

The user approved the plan the same day. This item lands it in two parts, since the second is Ring 0.

**Part 1, doc-only, on branch `plan/2026-11`** (from `w32/shift`, with `spike/usable` merged in, since the route's items were filed there):
1. `PLAN-2026-11.md`: the plan as approved.
2. A backlog item for each id in its milestone table, with an acceptance and a kill rule. Existing items are re-aimed where the plan re-aims them (`REL-01`, `PH2`, `PH3`).
3. The parked items and the superseded ones get a dated record each. None is deleted.
4. `PLAN-2026-10.md` gets a pointer at its head: its design stands, and its roadmap (§12) is replaced.

**Part 2, Ring 0, on branch `g0/plan-2026-11`, a proposal for the user's key:**
1. `tools/milestones.tsv`: one row per milestone (id, date, status, earlier dates, acceptance). It sits under `tools/` so that a date moves only with the key.
2. `tools/render-state.sh` prints the next milestone, its date and the days left, and names any that are late.
3. `tools/check-claims.sh`, rule (s):
   - a milestone still `open` more than 7 days past its date is drift (the plan's "5 working days");
   - each row's id and date are on one line of the plan's table, so the plan and the data cannot disagree;
   - a moved date is named in the plan's corrections.
   - Rule (a) asks `CLAUDE.md` for `PLAN-2026-11.md`.
4. `tools/guard-selftest.sh`: a refused case for each of the three, and an accepted case (a milestone marked `done` after its date, and a moved date with its correction).
5. `CLAUDE.md` names `PLAN-2026-11.md` as the plan of record, and `PLAN-2026-10.md` as its design.

**Closing the old in-progress items** (`F1`, `F3`, `F5`, `EXPR-01`, `EXPR-04`) is M0's work, by 2026-11-13, each against its own acceptance. It is not done by this item's first commit.

## Log
- 2026-11-10, **part 1 filed**, on branch `plan/2026-11`.
  - `PLAN-2026-11.md`, and 23 new items: `L-IO`, `MED-01`, `ISO-01`, `STR-01`, `INJ-01`, `PATH-01`, `S-SPEC`, `S-HEAP`, `HEAP-01`, `HEAP-02`, `HEAP-03`, `SPEC-01`, `SPEC-02`, `UNI-01`, `SEAM-01`, `FLAG-01`, `BLIND-01`, `MUSEUM-01`, `ENG-01` to `ENG-04`, `V1`. Each has an acceptance and a kill rule. Five have the kill rule "-": `PATH-01`, `HEAP-03`, `SEAM-01`, `ENG-02`, `ENG-04`. For the first two the cut order is what happens when they fail.
  - Re-aimed, with the header before recorded in each log: `REL-01` (from `UCmd`, Ring 0, to the slice language, Ring 1), `PH2` (unblocked, with its parts and dates), `PH3` (the release candidate).
  - Parked, `planned` to `blocked`, with a record each: `LSYN-01`, `S-PRIM`, `MUL-01`, `RC-04`, `PH4`, `PH6`, `P0-07`, `S-COST`.
  - `L-UNIFY` is `killed`, superseded by `UNI-01`. `L-BYTES` is `in-progress`. `PH5`, `F7`, `P0-06`, `EXPR-03` and `EXPR-04` each say where they close.
  - `PLAN-2026-10.md` has the pointer at its head.
  - **Two differences from the approved text**, recorded in `PLAN-2026-11` §9: `milestones.tsv` goes under `tools/` (part 2), and `FLAG-01` asks for the handler's C text by 2026-12-04.
  - **Not done here:** part 2, and M0's judging of `F1`, `F3`, `F5`, `EXPR-01` and `EXPR-04`.
