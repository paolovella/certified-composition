---
id: S-KERNEL
title: Spike: kernel decide time for bcheck on 12 corpus programs and sketch compile
ring: 3
tier: G-P
deps: []
closes: ['kernel-evaluated compilation feasibility']
acceptance: bench/kernel.tsv with times
kill: more than 60 s per 200-node pass: per-function granularity from day one
status: done
---

## Plan

Question: can the Lean kernel itself evaluate the checker (and later the compiler) on real
programs fast enough that "accepted" and "compiled" can be theorems proved by `decide`, rather
than outputs of a compiled binary we trust?

1. `bench/kernel/gen.py` writes one Lean file per case under a scratch build dir (not
   committed); each file imports ConfTyping and proves exactly one equation by kernel
   evaluation. Two modes per case: `by decide` (elaborator evaluates the instance first, then
   the kernel re-checks) and `by decide +kernel` (kernel only). Neither adds an axiom; the
   bench asserts that with `#print axioms`.
2. Cases:
   - corpus: the 12 `corpus/ext/b*.uc` and 25 `corpus/p/*.uc` programs, from the source
     string: parse only, and parse + `bcheck` (the T1 statement "this text is accepted");
   - scaling: synthetic programs of N copies of the handler body, N chosen so the UCmd has
     about 50, 100, 200, 400, 800 nodes: parse + bcheck;
   - compiler: the P1 sketch's `compile` (names to slots) on the same scaled programs, the
     equation being `tsize (compile T c) = n`.
3. Time each file with `/usr/bin/time` minus the time of an import-only baseline file.
   Results go to `bench/kernel.tsv` (case, nodes, mode, seconds, verdict).
4. Decision rule from the plan: more than 60 s per 200-node pass means per-function
   granularity from day one. Record the decision in Log.

## Log

Plan deviations: the equation compared for `compile` is `tdig` (a digest that forces every slot
number), not `tsize`; times are wall clock from Python, not `/usr/bin/time`; a `run` column was
added to `bench/kernel.tsv` because four runs are recorded.

- 2026-10-23, run 1 (`skernel-kernel`, kernel mode, string tasks): corpus programs (1-27 nodes)
  take 0.03-1.0 s each for parse and for parse + bcheck. The scaled programs grow superlinearly:
  43 nodes about 4.6 s, 73 nodes about 20 s, 133 nodes about 70 s, and parse alone costs as much as
  parse + bcheck or parse + compile. The sweep was stopped by hand (I-0002).
- 2026-10-23, run 2 (`skernel2-kernel`): the same small cases were 1000x slower (`ext_b02`
  parse 697.90 s vs 0.71 s; `ext_b01` timed out at 1800 s vs 1.04 s). The run overlapped the
  2-hour `s435-fix-build` job. Cause not established. Excluded from the decision and kept in
  the tsv, marked.
- 2026-10-24, run 3 (`skernel3-repro`): run 1 reproduces (`ext_b02` 0.71 s, `ext_b04` 0.03 s,
  `scale002` 4.48 s), so run 2 is the outlier.
- 2026-10-24, run 4 (`skernel4-term`): the passes from an elaborated `UCmd` term, with no text
  parsing. `bcheckT` is roughly linear: 0.06 s at 133 nodes, 0.12 s at 253, 1.11 s at 1933.
  `compileT` (P1 sketch) is roughly quadratic, probably from the linear `slotOf` lookup: 0.23 s
  at 253 nodes, 2.74 s at 973, 11.47 s at 1933. The axioms printed are `[propext]` for elabT and
  bcheckT and none for compileT. All three appear on the string tasks, so `Classical.choice`
  enters through `parseSource` (not checked further here).

**Decision.** The kill rule does **not** fire for the passes: at 253 nodes `bcheck` takes 0.12 s
and P1 0.23 s against a 60 s budget, so whole-program kernel evaluation is feasible for both, at
least to about 2k nodes. It fires for the **text parser** (about 70 s at 133 nodes), so no
kernel-evaluated statement may start from source text. That matches the plan's choice of
`Wire` over a text grammar in the TCB. Follow-ups, not in scope here: time the `Wire` decoder in
the kernel once it exists (PH1/PH3), and make P1's slot lookup sublinear before it becomes the
cost (CMP-P1). Not measured: the elaborator `decide` mode (only run 2 has rows for it).

Status: done. Acceptance `bench/kernel.tsv` holds 111 rows from 4 runs.
