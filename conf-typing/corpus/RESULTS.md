# Baseline measurement — 2026-08-13

Method: `TASKS.md` was written first, from ordinary handler patterns and CWE Top-25
categories. Every program in `p/` was written before the checker was run once. Tasks
26–30 were added to the list *before* running, precisely because I suspected the language
could not express them; they have no program, and that is the finding.

Command: `certcheck p/NN.uc --secret pw,scopy`

## Headline

| | count | |
|---|---|---|
| tasks | 30 | |
| **inexpressible in the language** | **5** | **17% of tasks — no program can be written** |
| expressible | 25 | |
| accepted | 20 | 80% of expressible |
| rejected | 5 | |
| — of those, **correct** refusals | 3 | the program really is unsafe |
| — of those, **false** refusals | 2 | **8% of expressible programs; 9% of the safe ones** |

## The five rejections, classified

| # | program | verdict | why |
|---|---|---|---|
| 09 | `emit db input` | **CORRECT** | unsanitized untrusted data reaching a sink — the injection this is for |
| 11 | `if flag { alloc p } else { skip } ; free p` | **CORRECT** | on the `else` path `p` is never allocated, so `free p` frees a wild pointer |
| 21 | `for i = 5 { alloc t } ; free t` | **CORRECT** | allocates five cells and frees one — a leak, and the tracked set genuinely is not a fixpoint |
| 17 | `for i = 3 { check db ; access db }` | **FALSE** | a retry loop that re-authorizes. Refused because stage 2j's `for` rule demands the body return the mediation set *unchanged*, and `check` extends it |
| 24 | `for i = 3 { for j = 3 { alloc t ; free t } }` | **FALSE** | nested counted loops. Refused because `bcheck`'s `for` rule checks the body with `allcheck`, which has no loop rule — recorded in stage 2j as "nesting is a follow-on, not a claim" |

Both false rejections are in **one rule**, the counted-loop rule added in stage 2j, and
neither is a soundness matter: both programs are safe.

## What this does and does not establish

It establishes a number that did not exist: **8%**. It is measured on programs written to
a task list rather than to the rules, which is the methodological point.

It does **not** establish that the checker is precise in general. The corpus is 25 small
programs (1–8 statements) written by the same person who wrote the rules, in a language
with ten constructors. The 17% inexpressibility figure is the more damning of the two
numbers, and it is a lower bound: the task list was itself written by someone who knew
what the language has.

## Baseline, frozen

`git` commit of this file is the baseline. Any later claim of improvement is measured
against this table, on this corpus, with the corpus unchanged.
