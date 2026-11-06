---
id: BOUND-01
title: "A budget over loops: the boundR shape, its transfer, and a counted for loop that the checker can bound, down to RV64 bytes"
ring: 0
tier: G-0
deps: [VS-2]
closes: ['VS-2: over loops only rel reaches the bytes, and Cert.bound cannot state a budget that depends on input']
acceptance: Cert.boundR in the kernel with boundR_transfer, bound_iff_boundR, a refused witness that no program with unbounded cost has one, and boundR_late_vacuous recording why the budget is chosen before the fuel; a counted for loop in sliceLang whose checker gives a budget as a function of the inputs, and a capped form for e max N whose budget is a constant; one program with a for loop whose literal RV64 image carries rel and boundR by transfer alone; QEMU's instruction counts within the transformed budget on every input tried
kill: if boundR's transfer needs a proof about a pass, or about a certificate, stop and report. If the checker's budget cannot be computed by kernel evaluation at the sizes VS-2 used, stop and report
status: planned
---

## Plan

The user's decisions of 2026-11-06: "grow sliceLang", and "boundR plus a counted for loop". This item is the second. The first is recorded in
`L-BYTES`.

**Checked before this plan was written** ([`research/2026-11/BoundRSketch.lean`](../research/2026-11/BoundRSketch.lean), against the real kernel):
`boundR_transfer` with no axioms, `bound_iff_boundR`, `no_budget_if_unbounded`. One thing in VS-2-RESEARCH's sketch was wrong and is corrected there:
the budget must be chosen before the fuel, or every program has one.

**The shape.** `boundR L R p := ∀ i, L.Adm i → ∃ k, R i k ∧ ∀ n, (L.run n p i).cost ≤ k`. On the target, `liftR pc t R u k := ∃ i k', S.Adm i ∧
pc.enc i = u ∧ R i k' ∧ k = t.cost k'`. **A limit to state:** a budget that depends only on public input does not lift in general, since a target
input may encode several source inputs. It does when `enc` is injective on admissible inputs, which `slotPass` and `rvPass` should meet. That is a
lemma per pass, about `enc` alone and not about a certificate.

**Steps.** Each ends with a report to the user.
1. **The kernel (Ring 0, on the user's word above).** `Cert.boundR` beside `bound` in `Kernel/Cert.lean`, and `boundR_transfer` beside
   `bound_transfer` in `Kernel/Pass.lean`, with the witnesses from the sketch. Frozen statements for the shape and its transfer in
   `workspace/Statements.lean`, and `ring0.lock` regenerated. Every change to the lock is listed for the user before it is committed.
2. **The construct.** `for e body` in `sliceLang`: `e` is evaluated once, and the body runs that many times. **Open, to settle in this step:**
   whether it is a source construct or sugar for `c := e; loop c (body; c := c + -1)` with a fresh `c`. As sugar, `slotPass` stays lockstep and the
   lowering is VS-2's. As a construct, the checker's bound is easier to prove, and `slotPass` stops being lockstep. **I would take the sugar**, with the
   checker recognising it.
3. **The checker's budget.** `e` must be low, as a `while`'s guard is, and its value must be a function of the inputs. That means a literal, or an
   input that is not assigned before the loop. The budget is `value(e) * (cost body + c) + c'`. A `while` keeps `rel` and gets no budget.
   Witnesses: an accepted program with a budget, a refused one whose bound is assigned before the loop, and one whose bound is secret.
   **The cap, the user's decision of 2026-11-06, "1 and 3 together".** A side agent pointed out that a formula budget proves the program finishes,
   not that it finishes quickly: with a 64-bit count, a true budget can be astronomically large, and whoever controls the public input controls the
   running time. So both forms are in:
   - **`for e body`**, with the formula budget above, for a reader who judges whether the inputs they allow keep it reasonable.
   - **`for e max N body`**, which runs `min(value(e), N)` times, with `N` a literal. Its budget is a constant, so the plain `bound`, and so
     `bound_iff_boundR`, give it. This is how a program states a hard limit and has the checker prove it. Witnesses: an input above `N` runs `N`
     times, and the budget holds there.
4. **To the bytes.** A program with a `for` loop over the array, as a literal image, with `rel` and `boundR` by transfer alone.
   `enc` injective for both passes.
5. **QEMU.** The instruction count on every input tried is at most the transformed budget, and the comparison can fail: a budget one too small is
   seen to be exceeded.
6. **The account,** including how tight the budget is.

## Log
