---
id: S-EXPR
title: "Spike: measure L's premise on tasks the rules' author did not write: a blind task set with a sealed holdout"
ring: 3
tier: G-P
deps: []
closes: ['the false-rejection rate has only ever been measured on the rules author''s own 25 programs']
acceptance: a frozen task list written before any program; programs written by an author with no access to the checkers' source; inexpressible / accepted / correctly refused / falsely refused counted, with the holdout half sealed
kill: more than 30% of expressible safe tasks falsely refused, or more than 30% inexpressible, means the witness language needs redesign before Phase 3 (PLAN-2026-10 §8)
status: done
---

## Plan

From `research/2026-10/STOCKTAKE-2026-10-27.md` §4.1 and §5.1. PLAN-2026-08 §1.1 said the
corpus was rigged: every program in the repo was written after the rule that certifies it. The
2026-10-28 re-run (`conf-typing/corpus/RESULTS.md`) confirms the frozen corpus still reads
21/25, which only shows nothing regressed. L's bet is that AI authors make annotation burden free,
but a false refusal is not burden, it is a wall. This spike gives that bet its first number.

1. **The task list, frozen first.** 40 tasks in `corpus/blind/TASKS.md`, from the CWE Top-25 and
   ordinary handler patterns (auth, retry, parse-then-emit, pooled allocation, nested loops,
   stored data). Each task gives intent and the property expected to hold; none mentions a
   checker rule. It is committed before any program exists, and the commit hash goes in
   `RESULTS.md`.
2. **Split.** A fixed seed splits the list 20/20 into `open` and `holdout`. The holdout's programs
   are written but sealed: not run until the open half is reported, and never used to tune a
   rule (PLAN-2026-10 §8, "sealed holdout").
3. **The blind author.** An agent writes the programs in the current surface syntax. It is given
   the language reference (`README.md`'s syntax section, the examples) and the task list. It is
   not given `conf-typing/ConfTyping/` or any checker source, and it is told so. It cannot run
   `certcheck`. This is PLAN-2026-10 §8's "Blind transcriber". Spawning it needs the user's
   word, and it runs as a separate agent so the author of the rules cannot leak them.
4. **Classify** each task: inexpressible (no program possible; with the reason), accepted,
   correctly refused (really unsafe), falsely refused (safe, refused; with the rule). The
   classification of "really unsafe" is argued in the results, task by task.
5. **Report the open half**, then unseal and report the holdout with no rule changed in between.
   If the two halves disagree by more than 15 points, the open half was not representative, and
   that is reported too.

Not done here: fixing any false refusal. Fixes are their own items, measured against this
frozen set.

## Log

- 2026-10-28, branch `s-expr/blind`. Steps 1–5 as planned.
  - Both agents ran as `claude -p --restricted`, with file tools confined to an otherwise empty
    directory (receipts `sexpr-task-writer`, `sexpr-blind-author`). The user started them
    ("start a separate agent").
  - The task list (b43b601) and all programs (29bcb61) were committed before any checker run.
    The open half was reported (869c465) before the holdout was run.
  - **Result** (`conf-typing/corpus/blind/RESULTS.md`):
    - SAFE: 3/32 inexpressible; 23/29 accepted; **6/29 falsely refused (21%)**.
    - UNSAFE: 8/8 refused.
    - The kill rule does not fire.
  - **Causes of the false refusals:** nested counted loops 2; the `if` join 1; an undocumented
    secret-pointer rule 3, which is a defect in the reference the measurer wrote.
  - **Not covered by acceptance:** 06 is accepted with a path-traversal hole, because `san` is
    quote-only. 29 is certified without bounds.
  - Follow-ups for the user to file or decline:
    - document the secret-pointer rule;
    - nested counted loops, open since August;
    - the `if` join;
    - `san`'s name, or `certcheck` running `PathCert`;
    - a second blind author on the same tasks.
