---
id: VS-1
title: "The vertical slice: one tiny program, certified, down to RV64 bytes that run, through a pass that changes the input"
ring: 0
tier: G-0
deps: [F2, F4]
closes: ['F3 kill rule: a lowering whose target input differs', 'nothing certified reaches anything that runs']
acceptance: for one program, a theorem that its literal RV64 image carries rel and bound on an RV Lang by transfer alone; the image runs under an emulator and its observed result, cost and PC trace match the prediction; a refused program whose binary is observed to leak; the trust base listed; the kernel changes it forced listed for the user's review
kill: if no lowering with a different target input can meet cover and low_cover, stop and write up the obstruction, which amends PLAN-2026-10 section 2. If certificate-specific pass proofs are needed, the central claim of section 6 fails, so stop and report
status: in-progress
---

## Plan

The user's decision of 2026-11-03. Why, and what it holds:
[`FOUNDATION-2026-11-03`](../research/2026-11/FOUNDATION-2026-11-03.md). Branch `vs/slice`, from `f5/map`.

**The question it answers:** does the kernel survive contact with a real machine? Each step is built to
expose a kernel gap while fixing it is still cheap.

**The slice.**
- **Source:** a new small language, with `W64` values, named variables, `add`, `seq` and `ite`, and a result.
  Not `UCmd`, whose unbounded `Int`s have no machine meaning.
- **Certificates:** `rel`, because leakage must reach a program counter trace, and `bound`, because cost must
  reach instructions retired. A small checker, with an accepted and a refused witness per rule.
- **Target:** an RV64 subset as a lawful `Lang`, as few instructions as the slice needs, including `addi`,
  `beq`, `ld` and `sd`. Input: registers and a data segment, really different from a named store. Leakage:
  PC and addresses. Cost: instructions retired.
- **Passes:** at least two, chained by `PassCert.seq`: variables to stack slots, whose input changes, then
  instruction selection, where one source step becomes many.
- **Out of the slice:** loops, heap, strings, functions, mediation, speculation, residue, optimisation.

**Steps.** Each ends with a report to the user.
1. **Walking skeleton, no proofs.** A Lean function produces RV64 bytes and a static ELF for a fixed program
   that returns a number. It runs under QEMU. First data on how far the bottom is.
   **Needs the user:** emulators are absent, and installing needs a password:
   `! sudo apt install -y qemu-user binutils-riscv64-linux-gnu`. Whether QEMU gives a good enough PC and address
   trace, or Spike is needed, is decided here.
2. **On paper: `enc`, `ret`, `W64`.** For the two passes, write what `enc`, `cover` and `low_cover` must say,
   and whether `enc` must take the program. Propose kernel changes. Nothing merges: Ring 0 is the user's key.
3. **`Word`, the source `Lang`, the checker, the certificates**, on a kernel branch with whatever step 2 proposes.
4. **The RV `Lang`, proved lawful**, and tested instruction by instruction against the emulator.
5. **The first pass, slots, where the input changes.** This is the F3 kill rule's test.
6. **The second pass, and `seq`.** Guard (m)'s rule applies: no certificate-specific pass proof.
7. **Bytes as a theorem.** Compile by kernel evaluation (`decide`), with the image a literal, and an encoder
   proved against a decoder. The carried theorem is about that literal.
8. **Differential.** Run the literal under the emulator on chosen inputs. Result, cost and PC trace must equal
   the prediction. Two inputs differing only in the secret must give equal traces.
9. **Teeth.** A program the checker refuses compiles anyway through an uncertified path, and its binary's trace
   is observed to differ on the secret. A pass that misses an input is refused.
10. **The account.** What the kernel had to change, what stays wrong, the trust base, and a recommendation on
    what F6 should lock.

**The trust base it will state.** The kernels; Lean; the RV `Lang`, which is not yet linked to Sail, so step 4
and 8's emulator runs are ledgered test evidence. S-SAIL's proof route, with its conditions, is the later link:
it proved `addi` and `beq` and stated `ld`. The Linux loader and the emulator. Hardware is not reached: running
under an emulator says nothing about a real core's timing.

**A check on honesty.** Only a statement about the literal bytes counts as reaching the bottom. A theorem about
a compiler function, with the bytes produced by running it outside the kernel, does not.

## Log
- 2026-11-03, branch `vs/slice`, **step 1 done: the walking skeleton runs.** `l-core/LCore/Slice/Skeleton.lean`
  writes static RV64 ELFs from Lean. No proofs, and not imported by `LCore`, so CI does not build it yet.
  - `objdump` decodes the encoder's `addi`, `add`, `ld`, `sd`, `beq` and `ecall` as written, and `readelf` accepts
    the header. Under QEMU 8.2.2 user mode, `ret42` exits 42, `viamem 7` exits 42 and `viamem 0` exits 0.
  - **The trace question is answered: QEMU is enough for now, and Spike is not needed yet.**
    `-one-insn-per-tb -d exec,nochain,cpu` logs each instruction's PC and all registers before it. So cost is the
    count of lines (9 and 8 on the two runs), and an address is a register plus an immediate. No plugins ship
    with the package. Spike remains the later check on QEMU.
  - **The trace shows the leak.** `viamem 7` and `viamem 0` differ in exactly one PC, `0x1008c`, the skipped
    instruction. This is the channel `rel` must speak about, seen on a real binary.
  - **Finding for step 2: the stack pointer is an input, chosen from outside.** It repeats across identical runs,
    and changes with the environment and with `argv` (`0x2aaaab2aa890`, `...abe10`, `...a870`). So the RV `Lang`'s
    input must contain it, and it is attacker-influenced. The source language has no stack pointer, so `cover`
    needs every value to be the encoding of some source input. This is F3's kill rule in concrete form.
  - **Finding for step 2: the exit status is not the result.** `a0 = 300` exits 44: the status keeps 8 bits. The
    log shows the full `a0`. So `ret` is `a0` at the exit `ecall`, and the differential reads it from the log.
  - **Finding for step 2: a fault has an outcome.** A load from address 0 exits 139 with no exit `ecall`. The RV
    `Lang` must call this an abort that the OS reports, and the trust base must say so.
- 2026-11-03, **step 2 done, on paper: the slice forces no kernel change**
  ([`VS-1-KERNEL`](../research/2026-11/VS-1-KERNEL.md)). Tested by one probe binary, and proved by nothing yet.
  - **Correction to step 1's finding.** It said the RV `Lang`'s input must contain the loader's `sp` as something
    the program uses. An unused `sp` in the source input makes `det` false if addresses depend on it, since `det`
    covers any two inputs. So the entry stub sets `sp` itself, and from the second instruction on, the probe's trace
    is identical across environments and `argv`.
  - The design: a passive environment `E` in every language's input, whose independence is `det`'s real content;
    positional inputs in a data segment, so `enc` needs no program; the result as `Ev.ext "ret"`, so `progress` and
    `reflect` give result correctness; `W64` in the slice. PLAN-2026-10 §2's `ret` field is not needed here.
  - **F3's kill rule is still unjudged.** Step 5 judges it. Constant addresses make `det` at its easiest here, so a
    later slice must try input-dependent addresses.
- 2026-11-03, **step 3 done: the source language, its checker, and `rel` and `bound` on it**, in
  `l-core/LCore/Slice/Word.lean` and `Source.lean`, on the design in step 2. No kernel change.
  - `sliceLang E P` is lawful. Its input is positional words and a passive `E`; its words wrap (`wraps_in_source`); its
    result is the event `Ev.ext "ret"`. `sliceCheck_rel` and `sliceCheck_bound`: what `sliceCheck` accepts shows the
    same at every fuel on inputs agreeing at public positions, whatever the environment, within the checker's budget.
  - Accepted: `clean`, where `clean_runs` shows it finishes with the right result and depends on its public input.
    Refused, each with its leak proved: `secretBranch`, `secretRet`, `laundered`, `oneArm`, `shadowed`.
  - **Rule mutants by hand:** 11 mutants of the checker and the budget, all killed (`research/2026-11/slice_mut.py`,
    run from `l-core/` with a scratch directory as argument).
  - **Tooling gap, for the user:** `tools/mutants.py` and the witness registry scan only `conf-typing`, so `sliceCheck`
    is outside both. So is everything in `LCore.Slice`. They are Ring 0, so this is a proposal: extend both to `l-core`
    before F6. Nothing checks these 11 stay killed until then.
- 2026-11-03, **step 4 plan: the RV `Lang`, lawful and tested against QEMU.**
  - **Model:** `rvLang`, in `l-core/LCore/Slice/Rv.lean`. Program: code bytes at a fixed address, fetched and decoded,
    so the statement is about bytes. Memory is byte-addressed. Instructions: `lui`, `addi`, `add`, `ld`, `sd`, `beq`,
    `ecall`. Input: the data segment's bytes and the environment `Env` (initial registers, what the loader mapped).
  - **Observation:** `Lk.step [pc]` per instruction, `Lk.addr` per access including a faulting one, cost as instructions
    retired, `Ev.ext "ret"` and `done` at exit, `abort` on a fault.
  - **The test:** for each case, the model predicts every step's PC and registers, and the outcome. A driver writes the
    ELF and the prediction, and a script compares them with QEMU's log, instruction by instruction. It covers
    immediates' edges, sign extension, wrapping, unaligned and overlapping accesses, branches both ways, `x0`, and faults.
  - **Where the model is known to be wrong**, tested as expected deviations: it aborts on instructions it does not
    model, while the real machine runs them (a compressed instruction, and an unknown syscall). The compiled program
    must not use them. Step 7's theorem is about a literal, so that can be checked.
  - **Done as planned**, in `l-core/LCore/Slice/Rv.lean`, with `test/RvCases.lean` and `test/rv_diff.py`. No kernel change.
    `rvLang_lawful`. `probe_runs` and `probe_leaks`: the model sees a secret branch, so `rel` on it is not vacuous.
  - **The comparison** (receipt `vs1-step4-rvdiff2`, QEMU 8.2.2 user mode): 25 cases, 170 steps, every PC and register
    `x1` to `x31` equal, and every outcome, cost and exit status. The first step's `sp` is the loader's and is not compared.
  - **The harness can find a wrong model:** 17 broken models, 15 caught. The other two are its stated blind spot: it
    cannot see leaked addresses, because they come from the same registers. `probe_leaks_address` states that in Lean, on
    one program only. So addresses are the least tested part of the model.
  - **The mutants found two things.** My script read exit codes 254 and 255 as signals, which the first run showed
    (`vs1-step4-rvdiff` is the failing receipt, before the fixes). `fault_store_code` wrote to the ELF header and not to
    the code, so "code is not writable" was untested until a broken model survived it. Both are fixed.
  - **Expected deviations, both tested:** a compressed instruction runs on QEMU and aborts in the model, and so does an
    unknown syscall. So `rvLang` says nothing about a program using them, and step 7 must show the image uses neither.
  - **Not in CI.** QEMU is on this box and not on the GitHub runners, and `tools/ci.sh` is Ring 0. Proposal for the user:
    run it on the heavy runner, once P0-06 provides one. Until then a model change is not re-tested automatically.
- 2026-11-03, **step 5 plan: variables to slots, where the input changes.**
  - **Target:** `slotLang E P`: numbered slots in place of names, and an input of the data segment's **bytes** and `E`.
    The source's input is words by position, so this is a real change of representation. `cover` and `low_cover` have
    to be proved by decoding bytes, including inputs that differ inside one word.
  - **Layout:** input `k` lives at slot `k`, in place, and locals from slot 64. So `enc` needs no program, and no table
    is hidden in the target. `comp` refuses what does not fit: over 64 inputs, or over 512 slots.
  - **No stack.** With no calls, every slot is a constant in the data segment. Step 2's self-set stack is not needed:
    the compiled program never reads `sp`, set or not. Step 6 will show that on the machine.
  - **Not `PassCert.ofSim`:** its equation holds for every input, and locals start at zero only on admissible inputs.
    So the obligations are proved from an equation that assumes `Adm`.
  - **What this judges:** the half of F3's kill rule about a changed input. `E` stays passive here, since this language
    does not read it. Step 6 judges the other half, on the machine, where `E` is real.
  - **Done as planned**, in `l-core/LCore/Slice/Slots.lean`. No kernel change, and `PassCert` needed nothing new.
  - **F3's kill rule, first half: it holds.** A pass whose target input really differs meets `cover` and `low_cover`.
    `enc_wordAt` is what makes that true: encoding a decoding gives back every byte pattern. `carried_inside_a_word` uses
    it: two inputs differing in one byte inside a secret word are covered by the certificate.
  - **Carried by transfer alone:** `clean_carried` takes `rel` and `bound` through the kernel's transfers, with no proof
    about either certificate in this file. `compile_sim` is the pass's one equation; every obligation comes from it.
  - **Why this half is the easier one.** It is lockstep, and its target language does not read `E`. So the second half
    of the kill rule, that a compiled program's view does not depend on the machine's environment, is untested. So is one
    step becoming many. Step 6 has both.
- 2026-11-03, **step 6 plan: slots to machine bytes, where one step becomes many and `E` is real.**
  - **The pass:** `rvPass`, `slotLang Env P` to `rvLang P`, in `l-core/LCore/Slice/Lower.lean`, chained to `slotPass` by
    `seq`. Input is unchanged here (`enc` is the identity), since `slotLang` already takes the data segment's bytes.
  - **Code:** the base in `x7`; an expression on registers from `x8` up; `ld` and `sd` at constant offsets; `beq` over the
    arms, with a jump at the end of the first; a no-op for `skip`; at the end, the result in `a0` and the exit `ecall`.
  - **`comp` refuses** literals of 2048 or more, slots of 256 or more, expressions needing over 24 registers, and code over
    3 KB. The first is a real limit: there is no shift instruction to build a large constant.
  - **The proof:** one equation for a run: at every fuel, the machine shows a list of micro-steps, each a PC and its
    addresses, played up to that fuel, then the exit. That list is computed from the slots alone, so the environment
    cannot appear in it, which is `det`'s real content. Two runs with equal source leakage have equal lists.
  - **A simplification to record:** `t.fuel` is a constant, the fuel at which the source has finished. That is sound for
    these obligations because the slice has no loops, and it avoids aligning fuel inside a statement. **A language with
    loops cannot do this**, so this step does not test that alignment. F4's `splitPass` does, in a lockstep setting.
  - **Budget:** `t.cost c = L * c + L`, with `L` the code's instruction count. So the budget is really transformed.
  - **Done as planned**, in `l-core/LCore/Slice/Lower.lean`, about 1,500 lines, and no kernel change.
  - **F3's kill rule, second half: it holds, for this slice.** `run_eq` is the plan's one equation. `compiled_ignores_env`
    follows from it: on the machine model, a compiled program's whole observation is the same in every environment.
  - **`PassCert.seq` chains the two passes** (`pipeline`). `slice_carries`: what `sliceCheck` accepts, compiled, has `rel` and a
    transformed budget on `rvLang`, through the kernel's transfers. `grep` finds no `Cert.` in `slotPass` or `rvPass`, so
    PLAN-2026-10 §6's claim holds on this path. Guard (m) does not cover these files, so nothing keeps that true yet.
  - **Run for real:** `test/CleanRun.lean` writes the compiled `clean` as ELFs. Under QEMU, on five inputs, exit status and
    instruction count match the model's prediction (18, 18, 18, 14, 18). PC traces are identical across secrets 5, 6 and 250,
    and across a changed environment and `argv`, and differ on the public input, as they should. Five runs by hand. The
    systematic version is step 8.
  - **Accepted and refused:** `clean_on_machine`, `clean_runs_on_machine`, `clean_ignores_busy_env`; `large_literal_refused`,
    `high_slot_refused`; `secretRet_machine_leaks` shows `rel` on the machine is not vacuous.
  - **Still only for this slice, as the plan said.** The constant `t.fuel` cannot work for loops, and every address is a
    constant. F6 records the proposed condition. `clean_on_machine` is about the term `code (genP (compile clean))`; a literal
    image is step 7.
  - **The kernels found a real cost.** `vs1-step6-ci-full` failed (exit 1): `lean4lean` hit a deterministic timeout on `run_eq`,
    while the five others and the axiom check accepted (`vs1-step6-export`). It is a resource limit, not a rejection, and it
    still fails the gate, so the gate was left alone and `run_eq` was split into `entry_exec`, `exit_exec`, `laid` and
    `run_eq_laid`. All six then accept (`vs1-step6-export2`). **`lean4lean`'s per-theorem limit is now a design constraint**, and
    step 7's compile by kernel evaluation will press on it. CI's step also hides which kernel failed: a proposal for the user,
    since `tools/ci.sh` is Ring 0.
