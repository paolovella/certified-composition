---
id: BLIND-01
title: "The blind measure: the 40 tasks of conf-typing/corpus/blind ported to L and counted, as agent cells through the engine"
ring: 2
tier: G-P
milestone: M8 (2027-04-09)
deps: [FLAG-01, PH2]
closes: ['S-EXPR measured the premise on UCmd, which does not compile', 'PLAN-2026-11 §2 points 4 and 5']
acceptance: for each of the 40 tasks one of four outcomes, with its file - accepted with its literal image, correctly refused, falsely refused, or not expressible with the missing construct named; the counts reported as measured, beside S-EXPR's; each port merged as a cell by the engine on green, without the user; the task list and its tags unchanged from the frozen list
kill: more than 30% of the expressible safe tasks falsely refused is reported as a finding against 1.0, and does not block the tag; the user decides what it means
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B and agents, 2027-03-29 to 2027-04-09.

1. **The protocol is `S-EXPR`'s.** The list in `conf-typing/corpus/blind/TASKS.md` is frozen. A port is written from the task's text and the language's manual, without reading the checkers.
2. **Each task is one cell**: a C file, the expected outcome from the task's tag, and the result. Tier G-P, so the engine merges it on green. This is the engine's first real load, and the item reports the gate's flake rate and merge times.
3. **The count**, in `research/2027-04/BLIND-01.md`, with every number from a file in the corpus.
4. A falsely refused task is a finding. The rule is not changed to accept it in this item.

**First in the cut order** (`PLAN-2026-11` §5): the report covers however many tasks were ported by 2027-04-09, and says how many were not.

## Log
