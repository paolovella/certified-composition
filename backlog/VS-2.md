---
id: VS-2
title: "The second slice: loops and addresses that depend on public input, down to RV64 bytes"
ring: 0
tier: G-0
deps: [VS-1]
closes: ['VS-1: no kernel change was shown only for programs with no loops and constant addresses']
acceptance: for one program with a loop that reads an array at a public index, a theorem that its literal RV64 image carries rel by transfer alone, with t.fuel not a constant; a program that may never finish is covered at every fuel; the image runs under an emulator and its result, cost, PC trace and addresses match the prediction; a program indexing by a secret is refused, and its binary is seen to leak addresses; every kernel change it forces is listed for the user before any lock
kill: if a pass needs a proof about a certificate, PLAN-2026-10 section 6's central claim fails, so stop and report. If kernel evaluation of a literal image cannot pass all six kernels at the sizes step 1 measures, stop and report, since that puts compile-by-kernel-evaluation in doubt. If det or the fuel alignment needs a kernel change, that is not a failure: stop and propose it, since finding that before the lock is why this item exists
status: planned
---

## Plan

Written on the user's word of 2026-11-03, as a plan only. **No code until the user has read
[`VS-1-ACCOUNT`](../research/2026-11/VS-1-ACCOUNT.md) and said to start.** Whether F6 waits for this item is the user's open decision.

**The question.** VS-1 avoided two things on purpose. This slice has both:
- **Loops.** VS-1's `t.fuel` is a constant, the fuel at which the source has finished. A run that may never finish has no such fuel.
- **Addresses that depend on input.** All of VS-1's are constants, which makes `det` as easy as it gets.

**A correction to the account's wording.** It calls fuel alignment "untested". `Split.lean` proves it for a pass over loops, with `behind`,
`ahead` and `det_split`. What is untested is doing it **down to a machine**, where one step becomes several kinds of instruction and
back-edges exist. Those three theorems are this plan's template.

**The slice.** The same language, extended. Nothing else from L's list comes in.
- **`loop e body`:** a real `while`, which may never finish.
- **`x := a[e]` and `a[e] := y`:** one array, whose first words are the positional inputs. The index is masked to its 64 words, so it cannot go out of
  bounds. **That avoids the source-level abort path, on purpose,** and is a limit to state.
- **The source must leak the address.** `Lk.addr` of the masked index joins the source's leakage, or `det` cannot follow on the target. This is
  the first time the source's observation has to anticipate the machine's.
- **Certificate:** `rel`, at every fuel. `bound` stays for loop-free programs only: a `while` has no budget. A counted-loop budget is out of scope.
- **Checker:** a loop guard and an index must be low. One label for the whole array, high if any input position is secret, since a public index into
  a mixed array would otherwise need per-cell labels. That is coarse, and it refuses programs that are safe.
- **Machine:** `andi` joins `rvLang`, and indexing doubles with `add`, with no shift instruction. `beq` offsets become negative, which S-SAIL's
  proved `beq` covers, and `Good` needs the signed case.
- **Out:** heap, strings, functions, mediation, speculation, I/O, residue, optimisation, a source-level abort.

**Steps, riskiest first.** Each ends with a report to the user.
1. **Measure kernel evaluation, before anything depends on it.** Time-boxed. VS-1's budgets bit twice, and three hypotheses failed on one of those.
   Run the six kernels on literal images of about 76 bytes, 760 bytes and 7.6 KB, and try again to explain why `decide` on the compiled `secretBranch`'s leakage
   exhausts three kernels while `tampered_leaks` does not. Output: a table in the log, and a decision on whether step 7's literal theorem is viable. **If
   only 76 bytes pass, stop here.**
2. **On paper: fuel and `det`.** Write what `t.fuel`, `behind`, `ahead` and `det` must say when one source step becomes several instructions, and with
   back-edges. Write how the source's `Lk.addr` fixes the target's. Say what fuel the target needs for a source step that loads through the array. Propose any kernel change.
3. **The machine.** `andi` and negative `beq` in `rvLang`, compared with QEMU. **`rv_diff.py` learns to derive addresses,** as `image_diff.py` does, which closes
   VS-1's standing blind spot for every case. Mutants extended.
4. **The source:** lawful with real divergence (`diverge` is no longer trivial), the checker with accepted and refused witnesses per rule, `rel`, and hand-run
   mutants, unless the user has extended `tools/mutants.py` to `l-core` by then.
5. **`slotPass` extended.** Should stay lockstep. If it does not, that is a finding.
6. **`rvPass` over loops.** **The hard step, and where the kill rule is judged.** `run_eq`'s finite list of micro-steps cannot hold a run that does not finish, so
   VS-1's `walk` does not carry over. Most of `Lower.lean`'s simulation is expected to be rewritten, to the shape of `behind`, `ahead` and `det_split`.
   `compiled_ignores_env` must still hold, at every fuel.
7. **A literal image**, if step 1 allows it: a loop over the array at a public index. `rel` on the literal. The checks on `decode`, compression and the one exit, repeated.
8. **Differential.** Under QEMU: inputs where the public index really moves the addresses, so the traces differ on public inputs and are identical on secret ones.
   A program that does not finish, run to a fixed instruction count, compared as a prefix.
9. **Teeth.** A secret index and a secret loop guard are refused, and their binaries are seen to leak. The second leaks through whether and when it finishes.
10. **The account.** Did the kernel need changing? A recommendation on F6, and whatever this changes about `sliceLang` as a seed of L's core.

**What this will not show**, whatever happens:
- That L compiles. `UCmd` still does not. Connecting it, or its replacement, stays separate work.
- Anything about hardware, timing, caches, or speculation. The machine stays a model tested against QEMU.
- Heap addresses, which are what real input-dependent addresses mostly are. A masked index into one fixed array is the smallest form of the question.

## Log
- 2026-11-03, the user said to start, and that F6 waits for this item. Step 1 next.
