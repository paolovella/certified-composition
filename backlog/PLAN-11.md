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
  - Checked: `bash tools/ci.sh` green on 28 steps (receipt `plan11-ci`). Commit `e6e50d3`, PR #26 on top of #25.
- 2026-11-10, **part 2 proposed**, on branch `g0/plan-2026-11`, from `e6e50d3`. It is Ring 0: it waits for the user's key, and this item stays `in-progress` until that merge.
  - `tools/milestones.tsv`: 13 rows, all `open`, none moved.
  - `tools/check-claims.sh`:
    - Rule (a) asks `CLAUDE.md` for the sentence that names `PLAN-2026-11.md` as the plan of record, and still asks it for `PLAN-2026-10.md`.
    - Rule (s) is the plan's three checks (late and open; the file and the table agree; a moved date has its record).
    - Rule (s) also has five checks the plan did not list: the status is one of three, a cut has its record, a row has an acceptance, the file exists and has rows, and each row of the table is in the file.
  - `tools/render-state.sh`: a "Schedule" section, with the next open milestone and the days to it, or the late one and the days since, then every row. Tried in a scratch repository with a late row, a done row, a cut row, all rows done, and no file.
  - `tools/guard-selftest.sh`: 14 new cases, 10 refused and 4 accepted.
    - Open and 8 days late is refused; open and 7 days late is accepted; done and years past is accepted. So the boundary is the one written, and it is the lateness that fires.
    - A date that differs from the plan's is refused.
    - Moved with no record is refused; moved twice with one record is refused; moved twice with both is accepted.
    - Cut with no record is refused; cut with its record is accepted.
    - A status that is not one, a row with no acceptance, a row deleted and the file deleted are each refused.
    - `CLAUDE.md` without `PLAN-2026-11.md` is refused. The older case, without `PLAN-2026-10.md`, still is.
    - The self-test fixes the day once (`MILESTONES_TODAY`) and every case inherits it, so a run across midnight cannot split "7 days ago" from "today".
  - **What the rule cannot see:** a false `done`, and a date changed in the file and the table together with no earlier date kept. Both are edits under `tools/`.
  - **What it costs:** the rule depends on the day. Eight days after a missed date `check-claims` is red everywhere until a record is merged with the key, and that includes the self-test's accepted cases. `PLAN-2026-11` §8 says so.
    - **Each refusal fires for its own reason.** A drift case passes if any guard fires, so each refused mutation was applied to an export and the `DRIFT` lines printed: one line each, and it is the clause the case is named for.
    - The self-test went from 103 cases to 117 and from 34 s to 37 s, against a budget of 49 s.
  - The rule was replayed on the unchanged tree: clean today and at `MILESTONES_TODAY=2026-11-20`, drift for M0 at `2026-11-21`, and drift for a value that is not a date.
  - Checked: `bash tools/ci.sh` green on 28 steps (receipt `g0plan11-ci`, 858 s). Inside CI the self-test took 42 s, 7 s under its budget and 7 s more than in the run before (`plan11-ci`, 35 s). About 3 s of that is the 14 cases; the rest is the load of a full run. The next cases added to it will need the budget looked at, which is the user's decision.
  - `CLAUDE.md`: the pointer. `README.md` names both plans too.
  - `PLAN-2026-11.md`: §3 and §8 say what the rule does, with a correction of record in §9 for the two sentences that said nothing checked the dates, and the status note at its head is corrected the same way.
