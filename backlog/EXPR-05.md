---
id: EXPR-05
title: "Second blind author on the same 40 tasks: how much of S-EXPR is one author"
ring: 3
tier: G-P
deps: [S-EXPR]
closes: ['S-EXPR follow-up']
acceptance: a second isolated author's programs for the same frozen TASKS.md, run with the v1 reference, and the two authors' verdicts compared task by task
kill: -
status: done
---

## Plan

S-EXPR is one author, one run. Repeat step 3 with a fresh `claude -p --restricted` agent, the
same frozen `TASKS.md` and the same v1 `REFERENCE.md`, in `corpus/blind/p2/`. Commit before
running. Report agreement per task (same class), and whether the false refusals recur in the
same tasks. A second model family as author would also be informative, if one is available.

## Log

- 2026-10-28: done. A second isolated author on the same frozen tasks and the v1 reference:
  38/40 same verdicts; SAFE falsely refused 5/30 (17%) against author 1's 6/29 (21%); 8/8 unsafe
  refused by both. The same causes recur (the secret-pointer rule, nested loops). Results in
  `conf-typing/corpus/blind/RESULTS.md` (Replication).
