---
id: PH2
title: Phase 2 engine: tiers, classifier, ratchets, auto-revert, kill switch, receipts, challenge engine v1
ring: 0
tier: G-0
milestone: M2 (2026-12-18)
deps: [P0-06, F6, CI-02, CI-03, TP-01, ENG-01, ENG-02, ENG-03, ENG-04]
closes: ['gates as the only defence']
acceptance: cells-only autonomy switched on
kill: gate flake above 5%: fix first
status: planned
---

## Plan

Written on 2026-11-10 from [`PLAN-2026-11`](../PLAN-2026-11.md) §3, milestone M2, Track B, 2026-11-16 to 2026-12-18. `PLAN-2026-10` §7 is the design. This item is the milestone, and its parts are items of their own. Every one is Ring 0: the agent proposes each on a branch, and the user merges.

| Dates | Item | What it adds |
|---|---|---|
| by 2026-11-20 | `P0-06`, `F7` | the key mechanism and the heavy runner. The runner needs a token only the user can create |
| 2026-11-16 to 11-20 | `CI-02`, `CI-03`, `TP-01` | the CI step that fails by rebuild; L's checkers under CI's mutants and witnesses; vendored source under the key |
| to 2026-11-27 | `ENG-01` | the tier classifier and the type manifest |
| to 2026-12-04 | `ENG-02` | ratchets against BASE, and merge on green below G-0 |
| to 2026-12-11 | `ENG-03` | the post-merge audit, auto-revert, incidents, the kill switch |
| to 2026-12-18 | `ENG-04` | two scheduled adversaries |

**The switch, on 2026-12-18, is the user's.** `AUTONOMY` goes from `off` to `cells-only` when four planted failures have each done what they should:
1. a PR that weakens a guard is judged by master's gate and fails;
2. a bad cell that passes the gate is reverted by the audit, with an incident;
3. a second one within 7 days turns `AUTONOMY` off;
4. a planted audit failure on a Ring 0 path turns it off at once.

**The assumption on review:** a Ring 0 PR is reviewed within 2 working days. Slower than that moves M2 one for one (`PLAN-2026-11` §4).

**Not in M2:** the agent adversary and generated challenges (`PLAN-2026-10` §8 beyond `ENG-04`), claim records (`P0-07`, parked), `full` autonomy.

## Log
- 2026-11-10, **unblocked and given its steps.** It was `blocked` with the plan "See PLAN-2026-10.md". `F6` is done, and `P0-06`'s base gate has run live (PR #2). Deps before: [P0-06, F6]. The acceptance and the kill rule are unchanged.
