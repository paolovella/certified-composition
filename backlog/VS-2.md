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
- 2026-11-03, **step 1, partial: the measurement was stopped by Claude Code for low system memory, and is not finished.** Harness `bench/vs2/kernel_scale.py`, partial data
  `bench/vs2-kernel.tsv`, receipt `vs2-step1-kernel-scale2`. An earlier run, `vs2-step1-kernel-scale`, measured nothing: no case built, and its exit 0 meant nothing.
  - **The compiler's output equals a literal, at every size tried:** 88, 776 and 7,624 bytes pass all six kernels, within noise of the baseline. So the compile half of T2 is not
    the worry at these sizes.
  - **The machine run on a literal:** 88 bytes pass all six. **776 and 7,624 bytes did not elaborate**: Lean's `decide` hit its heartbeat limit, so no kernel saw them. This is the open
    question, and it is unanswered.
  - **The unexplained failure reproduces alone:** `branch-differs-f4` on 44 bytes: Lean, the paranoid checker and nanoda accept; lean4lean, con-leche and con-ron refuse. Its variants, which
    could explain it, did not run.
- 2026-11-04, **incident: this measurement caused out-of-memory kills in other projects on this machine.** Receipt `vs2-step1-kernel-rest`.
  - **What happened.** The 7.6 KB machine run on `decide +kernel` took over 21 GB and hit the harness's 15-minute cap. `subprocess.run`'s timeout killed `lake` and not its `lean` child, which
    kept running for about 1 h 44 min with memory and swap full. The job's receipt says exit 0 because the harness then saw 0.0 GB available and stopped cleanly.
  - **What it did.** The kernel log shows the OOM killer, 23:07 to 00:30: `postgres` 9 times, `local-path-prov` 4, `coredns` 4, `tigerbeetle` 2, `hv-ledger` 2, `hv-core` 2, `hv-core-go`, `pg_isready`, `tini`.
    These belong to other work: the `hv-dev-control-plane` kind cluster and its pods. `kube-apiserver` and `etcd` restarted. The `web-*` containers stayed up. Whether anything lost data is not checked.
  - **The fix.** The harness now runs each child in its own process group, kills the group on timeout, and caps it at 12 GB (`run_capped`). The orphan was killed by hand when it was found. `tools/run-job.sh`
    reported nothing, since the job itself had ended. An earlier stop for low memory, on `vs2-step1-kernel-scale2`, is not explained by this: no timeout had fired.
- 2026-11-04, **step 1, results so far** (`bench/vs2-kernel.tsv`, `bench/vs2-kernel-2.tsv`; times within noise of the baseline except where given):
  - **Compile equals a literal:** 88, 776 and 7,624 bytes: all six kernels accept. `image_carries`-style theorems need only this and the transfers, so **the compile half of T2 is not refuted at these sizes**, though `okP` caps code at 3 KB today.
  - **Machine run on a literal:** 88 bytes pass. 776 bytes pass on `decide +kernel`, 16.5 s to elaborate, and each kernel 10 to 20 s over the baseline. **7,624 bytes: over 15 minutes and over 21 GB, no verdict.** Ten times the size cost over fifty times the time. So running a machine in the kernel does
    not scale as written, and is useful only for small witnesses. The cause is not established, though a list lookup per fetch and memory as nested closures are the obvious suspects.
  - **`secretBranch`'s leakage on 44 bytes** still splits the kernels, and its five variants have not run.
- 2026-11-04, **step 1 done.** Harness `bench/vs2/kernel_scale.py`; data `bench/vs2-kernel.tsv` and `-2` to `-6`; receipts `vs2-step1-*`. Its stop rule does not fire.
  - **The unexplained failure is explained:** the derived `DecidableEq` on `Lk`, over values not yet evaluated. `branch-differs-f4` refused by three kernels, 31 s to elaborate; the same comparison through a map to `Nat`, accepted by all six, 0.3 s
    (`vs2-kernel-5.tsv`). Literal `Lk` values are cheap. Three earlier hypotheses were wrong: the compile, the fuel, an integer power. `secretBranch_compiled_leaks` is restored. **For step 7 and later: never `decide` on `Lk` or `Beh` over unevaluated values.**
  - **Compile equals a literal:** all six kernels at 88, 776 and 7,624 bytes, and a theorem like `image_carries` needs only this and the transfers. So step 7's literal theorem is viable.
  - **A machine run:** all six at 88 and 776 bytes, on a plain number too (`vs2-kernel-6.tsv`), with 20 s to elaborate at 776, against under a second at 88. At 7,624 bytes, the elaborator's `decide` hits its heartbeat limit, and `decide +kernel` reached over 15 minutes and 21 GB, with no verdict.
    So this cost is separate from `Lk`'s and grows faster than linearly. Machine runs in the kernel are for small witnesses, and larger programs get their evidence from QEMU.
  - **A false lead, corrected:** `con-leche`'s rejections in `vs2-kernel-3.tsv`, even on the baseline, came from the harness's address-space cap, which stops it creating threads. It now runs with the group kill and no cap.
- 2026-11-04, **step 2 done, on paper: no kernel change expected, and three corrections to this plan** ([`VS-2-FUEL`](../research/2026-11/VS-2-FUEL.md)). Nothing proved. The array gets its own region, since its first words being the inputs would alias
  the input variables on the machine and not in the source. Its label is one flow-sensitive bit. The loop rule needs a fixed point. `run_eq` is replaced by an intermediate machine, `runX`. Waiting on the user before any code.
- 2026-11-04, the user accepted step 2's three corrections and said to start on the code. Step 3 now: `andi` in `rvLang`, and `rv_diff.py` derives addresses from QEMU's registers and its own decoding, so leaked addresses are compared on every case, and the two
  broken models it was blind to must now be caught. New `andi` cases cover a mask, a sign-extended immediate, and a value near the wrap. Signed `beq` is already in the decoder; a backward branch is already a case. VS-1's proofs and `image_diff.py` re-run on the changed model.
- 2026-11-04, **step 3 done.** `andi` in `rvLang`. `rv_diff.py` derives each access's address from QEMU's registers and its own decoder, so **VS-1's address blind spot is closed for every case in that suite**: 29 cases, 205 steps, every PC, register, address, outcome and cost equal.
  21 broken models are all caught, including the two it was blind to, a wrong address, and a faulting load that leaks none. `image_diff.py` and `refused_diff.py` still pass on the changed model. Receipt `vs2-step3-rvdiff`; the first attempt stopped on my missing `open`. Still not in CI: the runners have no QEMU.
- 2026-11-04, step 3's CI failed twice on the time ratchet alone. The user raised both budgets and asked for a real fix; none was found. The numbers are in `backlog/F1.md`.
- 2026-11-05, step 3's CI is green, on an idle machine (`vs2-idle-1`, `vs2-idle-2`). See `backlog/F1.md`.
