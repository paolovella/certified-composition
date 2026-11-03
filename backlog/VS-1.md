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
