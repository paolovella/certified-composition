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
| 21 | `for i = 5 { alloc t } ; free t` | **CORRECT** | the tracked set is genuinely not a fixpoint. *(Reason corrected 2026-08-13: this was first recorded as "a leak", but no certificate here detects leaks — see `ext/RESULTS.md`. The refusal is right; the stated reason was not.)* |
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

---

# After stage 2k — 2026-08-13, same corpus, unchanged

The widening below was written *because* of program 17, not before it. The corpus was not
touched.

| | baseline | after 2k |
|---|---|---|
| accepted | 20/25 | **21/25** |
| correct refusals | 3 | 3 |
| **false refusals** | **2 (8%)** | **1 (4%)** |

**What changed, and why it is not a weakening.** Stage 2j's `for` rule demanded the body
return the mediation set *unchanged*. `UCert.forU` now takes `A ⊆ A'` and still concludes
`A`: the body may *grow* the authorization set, and the loop's post-condition stays `A`
because at zero iterations the body never runs. That is `JSecTy.whileW`'s widening, one
component over, and it needs `UMedInv.mono` — weakening `A` weakens the demand that
everything in `A` was authorized. The checker tests `subStr A A₂` instead of `A₂ == A`.

The three correct refusals (09, 11, 21) are still refused. `loopHandler_checks` still
`decide`s at budget 40. No soundness statement was touched.

**What is still refused, and why it is not being fixed today.** Program 24, nested counted
loops: `bcheck` checks the loop body with `allcheck`, which has no loop rule. Fixing it
means `bcheck` recursing into the body, which is a fuel-indexed refactor of the checker's
signature (well-founded recursion would break the `decide`-based measurements this repo
relies on). That is a real change and it should be its own stage.

**And the honest reason not to chase 0% here.** This corpus is 25 small programs written
by the same person who wrote the rules. Driving it to zero would be re-rigging by a slower
route. The number that matters next is on a corpus this author did not write — which is
what §5 Stage A of `../PLAN-2026-08.md` should have said, and now does.

---

# Re-run 2026-10-28, Lean v4.35.0, same corpus, unchanged

After the 4.35 move (P0-02), the deprecation renames (P0-09) and every Phase 0 gate, the 25
programs were run again with the same command (`certcheck p/NN.uc --secret pw,scopy`, receipt
`corpus-rerun-build`). The verdicts are the same as after stage 2k: **21/25 accepted**; 09, 11
and 21 correctly refused; **24 still falsely refused (4%)**. Nothing since August changed what
the checkers accept. That is a regression check, not new evidence: the corpus is still the one
written by the rules' author, and the next number has to come from tasks this author did not
write (`research/2026-10/STOCKTAKE-2026-10-27.md` §4.1, §5.1).
