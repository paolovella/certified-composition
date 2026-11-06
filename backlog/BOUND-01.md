---
id: BOUND-01
title: "A budget over loops: the boundR shape, its transfer, and a counted for loop that the checker can bound, down to RV64 bytes"
ring: 0
tier: G-0
deps: [VS-2]
closes: ['VS-2: over loops only rel reaches the bytes, and Cert.bound cannot state a budget that depends on input']
acceptance: Cert.boundR in the kernel with boundR_transfer, bound_iff_boundR, a refused witness that no program with unbounded cost has one, and boundR_late_vacuous recording why the budget is chosen before the fuel; a counted for loop in sliceLang whose checker gives a budget as a function of the inputs, and a capped form for e max N whose budget is a constant; one program with a for loop whose literal RV64 image carries rel and boundR by transfer alone; QEMU's instruction counts within the transformed budget on every input tried
kill: if boundR's transfer needs a proof about a pass, or about a certificate, stop and report. If the checker's budget cannot be computed by kernel evaluation at the sizes VS-2 used, stop and report
status: in-progress
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

- 2026-11-06, **step 1, the kernel: done, and not committed until the user has read the diff** (the user's word: "start, check before"). Branch `bound/boundr`.
  - **`Kernel/Cert.lean`:** `Cert.boundR`, with the budget chosen before the fuel; `Cert.bound_iff_boundR`; `Cert.boundR_unbounded`; `Lang.Lawful.boundR_finishes`. The header now says seven shapes.
  - **`Kernel/Pass.lean`:** `PassCert.liftR`, `PassCert.boundR_transfer` and `PassCert.liftR_const`. The transfer is three lines and mirrors `bound_transfer`. It uses `cover` and `cost_sim` only, so no proof is about a pass or a certificate, and the kill rule does not fire.
  - **Witnesses** (`LCore/Witnesses.lean`, not Ring 0). `toy`'s program `true` costs its secret word: it has the budget `k = i.2` and no constant budget at all (`toy_no_constant_bound`). `toySpin` has no budget under any relation. `boundR_late_vacuous`. Through `padPass`, the budget arrives as one more, and on `(0, 7)` it is exactly 8 (`padPass_budget_exact`).
  - **Frozen statements, 39 to 42:** `Frozen.boundR_transfer`, `Frozen.bound_iff_boundR`, `Frozen.boundR_finishes`, in `workspace/Statements.lean`, `StatementsProof.lean` and `comparator.json`.
  - **`ring0.lock`, the whole diff:** the hashes of `Statements.lean` and `comparator.json`; the frozen-statement count, 39 to 42; and two new entries, `LCore.Cert.boundR` and `LCore.PassCert.liftR`. **No existing definition's hash changed**, and `checkers.lock` is unchanged.
  - **Mutants: 5 of 5 killed** (`research/2026-11/boundr_mut.py`, receipt `bound01-mutants`). The fourth, a lifting that forgets which input a budget came from, **survived at first**. No witness checked that a target budget is that input's own, so the lifted budget could be any input's, the smallest included. `padPass_budget_exact` now kills it. Its first version was killed by name resolution, not by a witness, and was rewritten so that it tested the meaning.
  - **A count I had wrong:** VS-2's account and research called `boundR` the sixth shape. It is the seventh, since `relView` is the sixth. Corrected of record in both, and in `BoundRSketch.lean`.
  - **Docs:** `PLAN-2026-10.md` §1 says 7 shapes. `README.md` says the lock holds 524 definitions, after its guard fired at 522. `CHANGELOG.md` has entries for this and for VS-2, which had none.
- 2026-11-06, step 1's CI (`bound01-ci`) failed only on guard-selftest's time budget, 52 s against 49 s. Committed as `2468c5e` with that stated. The cause was this machine's process-creation speed, not the change. `CC-01` cut `check-claims`'s processes, and the self-test now takes 34 s.
- 2026-11-06, **step 2's design, settled before code: sugar, as planned.** `slotPass` stays lockstep, and the lowering is VS-2's, unchanged.
  - `forN c e b` is `c := e; loop c (b; c := c + -1)`.
  - `forMax c d N e b` is `c := N; d := e; loop c ((if d then (b; d := d + -1) else skip); c := c + -1)`. The language has no `min`, so it always
    runs `N` rounds, and the body runs while `d`, started at `e`, is not 0. Its running time does not depend on `e`, only on which rounds ran the body.
    The constant budget is therefore `N` rounds of the dearer arm. **The cap is on the count, not on the time per round.**
  - The names `c` and `d` are the writer's. The checker's job in step 3 is to bound loops of exactly these shapes, where `b` does not assign `c`
    or `d`, and to refuse a budget otherwise. A writer who builds the same shape by hand gets the same budget, which is right, since it means the same.
- 2026-11-06, **step 2 done: the counted loops, as sugar** (`l-core/LCore/Slice2/For.lean`). VS-2's checker, passes and bytes are unchanged.
  - **Accepted:** `countUp`, counted by a public input, and `capped`, by the same input with a cap of 4. **Refused:** `countSecret`, counted by the secret.
  - **They mean what they say, in the source.** `forN` runs its body `n` times. `forMax` runs it `min n 4` times: twice for 2, four times for 10.
  - **Why the cap** (`why_the_cap`): counted by a public input of `2^63`, `forN` has not finished after 400 steps, and would not for `2^63` rounds. `forMax` with the same input has finished. `capped_steps_constant_past_the_cap`: past the cap, the step count does not depend on the input, at 4, 10 and `2^63`.
  - **They compile, and run on the machine as in the source** (`capped_on_machine`, `countUp_on_machine`).
  - **Mutants: 36 of 36 killed** (receipt `bound01-step2-mutants`): 4 new on the loops, and the earlier 32 rerun through this module.
  - **Not here yet:** any budget. That is step 3, the checker's.
  - **CI** (`bound01-step2-ci`): every check passes, and `lake check` is over its time budget, 109 s against 104 s. Alone it takes 99 to 101 s. In the last six CI runs it went 87, 98, 91, 86, 101, 109 s. This is real growth: `lake check` replays every proof through the kernel, and each slice adds kernel-evaluated witnesses, `For.lean` about 2 to 3 s. Unlike guard-selftest, there is no overhead to cut without removing witnesses. The budget is the user's decision.
- 2026-11-06, **`lake check`'s budget raised from 104 to 130 s, on the user's word** ("a"), in `tools/ci-budget/Paolo.tsv`. It is real growth: every kernel-evaluated witness adds to what route 1 replays. 130 s leaves about 25% over the 99 to 109 s measured.
- 2026-11-06, **step 3's design, before code: a potential, as in amortised analysis** (Hoffmann's AARA, Carbonneaux's quantitative logic; `VS-2-RESEARCH` §2).
  - **The shapes the checker accepts.** The body is a `seq` tree of three kinds of command:
    - *plain*: loop-free, assigning no counter and no stable variable;
    - *init*: `c := e` for a counter `c`, where `e` reads only stable variables;
    - *counted loop*: `loop (var c) (seq B (c := c + -1))`, with `B` plain.
  - **Counters and stable variables.** The counters are the loop guards. The stable variables are inputs that nothing assigns. Loops are not nested, and no loop sits inside an `ite`. `forN` and `forMax` are both of this form. In `forMax`, `d` is a plain variable, and the loop's body is an `ite`, which is plain.
  - **The potential.** `pot` over frames and a store.
    - A plain frame costs `costOf`.
    - An init frame costs 1, plus the rest at the store with `c` updated.
    - A loop frame costs `(s c) * (costOf B + 2) + 1`.
    - The decrement inside a body costs 1, plus the rest at `c - 1`.
  - **Two lemmas.**
    - `pot` depends only on the counters and the stable variables, which plain frames do not touch.
    - On the frames after a loop, which hold no decrement, `pot` is monotone in each counter.
  - **The key theorem.** The cost at every fuel is at most `pot`, by induction on fuel, case by case on the head frame. The loop case uses monotonicity.
  - **The budget.** `R i k := k = pot (frames of the body) (the initial store)`. It is a function of the input, and `boundR` follows for the source. For `forMax` it does not depend on the input, so `bound` follows too, through `bound_iff_boundR`.
  - **Refused, to the budget, with witnesses:** a while loop that is not counted; a counter assigned from a variable something assigns; a loop nested in a body; and a counter assigned in a body.
- 2026-11-06, **step 3 done: the checker's budget is a certificate on the source** (`l-core/LCore/Slice2/Budget.lean`).
  - **`slice_boundR`:** a program `counted` accepts has `Cert.boundR` on `sliceLang`, with the budget `budget p i`, a function of the input. **`run_pot`:** at every fuel, a run costs at most the potential. The proof is by induction on fuel, with one lemma per kind of head frame. `pot_agree`: the potential reads only the counters and the inputs. `pot_mono`: on the frames after a loop, a smaller counter costs no more.
  - **Tight on these programs.** `countUp`'s budget is `4n + 2`: 14 for 3 and 42 for 10, and the runs cost exactly that. `capped`'s budget is 23 for every input (`capped_budget_const`, proved for all inputs, not evaluated), and the run costs 23 at the cap and 19 when the body never runs. **`capped_bound`:** a constant budget, plain `Cert.bound`, through `bound_iff_boundR`.
  - **Refused by the budget rule:** `spin`, whose guard is a literal; a counter reset in its body; a counter set from a variable the program assigns; a loop nested in a body; and a counter that is an input.
  - **Two slips while proving.** A `sorry` placeholder went into `pot_mono` and was taken out before the first check. It marked a real gap: an expression that reads only inputs is unchanged by a write to a counter, which `eval_upd_out` now proves. The first budget witnesses had guessed numbers, and `decide` refused them. They now use the computed values.
  - **Mutants: 42 of 42 killed** (receipt `bound01-step3-mutants`), 6 new. Four are killed by a witness or the main proof: a loop round charged one less, a counter's setting not followed, a decrement by two counted as one, and a wrong budget. Two are killed by a proof that no longer fits the changed definition: a loop body that need not be plain, and a counter that may be an input. The property they protect then cannot be proved, so they count.
  - **Next, step 4:** the budget through both passes to a literal image, with `boundR_transfer`, and `enc` injective for each pass.
  - CI green (receipt `bound01-step3-ci`). Steps 1 and 2 are on `master`, through PR #20 (`ec1cf21`), merged on the user's word with the gate's `ring0` check failing by design.
- 2026-11-06, **step 4's plan, before code** (the milestone a review of the repo named: `boundR` over loops reaching the bytes, which closes VS-2's recorded gap).
  - **`countUp`, to its literal image.** `rel`, by `slice_carries`. `boundR`, by `(pipeline sec0).boundR_transfer` applied to `slice_boundR`. Then a reader's form, on the bytes alone: for every admissible input and environment, and every fuel, the machine runs at most `L * (4n + 2) + L` instructions, where `n` is the input word read back from the bytes (`wordAt`) and `L` is the code's length. That needs `budget countUp i = 4 * (i 1) + 2` for every `i`, proved and not evaluated, and `wordAt_enc`, which is also why `slotPass`'s `enc` is injective.
  - **`capped`, to its literal image:** a constant budget on the bytes, plain `Cert.bound`, by `bound_transfer` applied to `capped_bound`.
  - **Not vacuous:** a concrete machine run within the budget, and how close.
- 2026-11-06, **step 4 done: a budget over loops on literal RV64 bytes, by transfer alone** (`l-core/LCore/Slice2/BoundBytes.lean`). This closes VS-2's recorded gap that over loops only `rel` reached the bytes.
  - **`countUp_bytes_budget`.** For every admissible input and environment, at every fuel, the 104-byte image runs at most `26 * (4n + 2) + 26` instructions, where `n` is the public input word as the bytes hold it (`wordAt`). It is derived from `countUp_boundR_bytes`, which is `boundR_transfer` through VS-2's pipeline, with `budget_countUp` (the source budget is `4n + 2` for every input, proved) and `wordAt_enc`. `countUp_rel_bytes` too.
  - **`capped_bound_bytes`:** plain `Cert.bound`, 672 instructions, for every input however large.
  - **Sound and loose, stated in the module.** The machine runs 66 at `n = 3` and 199 at `n = 10`, against 390 and 1118. `capped` runs 83 at the cap, against 672. The source budget is exact. The looseness is `rvPass`'s transformer, `L * c + L`, which charges every source step the whole code's length. Tightening it is a change to `rvPass`'s `Xform`, not to the kernel, and is not done here.
  - **Mutants: 46 of 46 killed** (receipt `bound01-step4-mutants`), 4 new on the bytes' budgets.
  - **Next, step 5:** QEMU, where the instruction count on every input tried is at most the budget, and a budget one too small is seen to fail.

