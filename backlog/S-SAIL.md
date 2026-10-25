---
id: S-SAIL
title: Spike: does sail-riscv's Lean output build under 4.35, and can ADDI/LD/BEQ refinement be proved
ring: 3
tier: G-P
deps: [S-435]
closes: ['model gap at the target']
acceptance: decision recorded: proof route or co-simulation route
kill: -
status: done
---

## Plan

From PLAN-2026-10 §4 (T3) and §12. The question is whether the RISC-V model the compiler targets can be
*linked* to the official Sail model by proof, or only by co-simulation. Work happens in a scratch
copy outside the repo. Only `bench/sail.tsv`, `bench/sail/` and this item are committed.

Candidate (2026-10-25): `opencompl/sail-riscv-lean`, generated daily from `riscv/sail-riscv`.
Last output `51c635c460` (2026-08-20), `lean-toolchain` v4.29.0, requires
`rems-project/lean-sail` `v5` (`0794631345`). Its README says the output "is neither executable
nor polished". The repo has no LICENSE file, so its licence is recorded before anything leaves
the scratch copy.

1. **Fetch and pin.** Clone both at those commits into the scratchpad. Record size, module count
   and licences.
2. **Baseline build** at the pinned v4.29.0, through `tools/run-job.sh`. If it doesn't build at
   its own pin, the bump question is moot; record that and go to step 4.
3. **Build under v4.35.0.** Count errors per module (the S-435 method) and the time taken.
4. **Inspect ADDI, LD, BEQ**: the `execute` clauses, the monad, and how memory and registers are
   reached. Check for `partial`, well-founded or `opaque` definitions on their path; those
   block kernel reduction and proofs by unfolding.
5. **Refinement attempt.** In a scratch module importing the model, define a minimal RV64 state
   and step for the three instructions. Try to prove that each agrees with Sail's `execute` under
   a state correspondence. Time box: one session.
6. **Decision.**
   - **Proof route** if the model builds under 4.35 with at most a handful of fixes, and ADDI and
     BEQ are proved with a credible statement for LD.
   - **Co-simulation route** otherwise: Sail's C emulator or Spike, with the results recorded as
     test evidence. The record says which step failed and how.
   - Either way the axiom footprint of anything proved is recorded, with no `sorry`.

## Log

- 2026-10-25, branch `spike/sail`. Numbers in `bench/sail.tsv`, scripts and proofs in
  `bench/sail/`, receipts `ssail-*`. The scratch copies are not kept.
  - **Step 1.** The model is 160 modules and 173,614 lines. It declares **75 axioms**, all in
    `RiscvExtras.lean`: softfloat, terminal I/O, LR/SC reservations, random bits and config flags
    such as `sys_enable_experimental_extensions`. Licences: `riscv/sail-riscv` is BSD-2-Clause.
    The generated `opencompl/sail-riscv-lean` and `rems-project/lean-sail` have no licence file.
    That has to be settled before any of it is vendored.
  - **Step 2.** It builds at its own pin, v4.29.0, in 436 s with 0 errors (`ssail-build-429`).
  - **Step 3.** It does **not** build under v4.35.0 as published (`ssail-build-435b`). Two
    causes, both mechanical:
    (a) `instruction` has 353 constructors. 4.35 refuses to generate code for a constructor with
    fields whose tag is over the runtime limit (`LCNF/Basic.lean`, `CtorInfo.checkValid`). The
    two inductives that contain `instruction` then fail too. This affects code generation only;
    the kernel still checks the declarations.
    (b) 1257 calls `assert c "msg"` no longer elaborate ("Function expected"). `lean-sail`
    `01bb54c7c8` (2026-10-14, five commits after v5, all additions) provides `sail_assert` for
    this, but the model has not been regenerated since 2026-08-20.
    `bench/sail/apply-435.sh` makes those changes. It also has `--opaque`, which turns the 75
    axioms into `opaque` constants, so the model assumes nothing. In total 1342 lines change. A
    fresh clone patched by the script is identical to the tree that was built. A clean 4.35
    build takes 2011 s (`ssail-opaque-435`). **`RvfiDii` alone takes 1794 s, against 5.6 s at
    4.29**; every other module over 2 s is within 8%. `RvfiDii` is outside the 110-module
    import closure of `InstsEnd`, where `execute` lives. Importing only that should avoid the
    regression, but that is untested. A false start (`ssail-build-435`, an invalid `-k` flag)
    built nothing.
  - **Step 4.** `SailM` is `EStateM` over a state whose registers are a
    `Std.ExtDHashMap Register RegisterType` and whose memory is a `Std.ExtHashMap Nat (BitVec 8)`.
    ADDI reaches `rX`/`wX` only; the register-name callback in `wX` always succeeds and only
    logs. BEQ reaches `jump_to`, which calls `currentlyEnabled Ext_Zca`, hence `Ext_C`, hence a
    read of `misa`. `currentlyEnabled` and `hartSupports` are defined by well-founded recursion,
    so kernel `decide`/`rfl` cannot evaluate them, but `simp` unfolds them through their equation
    lemmas. LD reaches `vmem_read`: `translateAddr` (well-founded page walk), `pmpCheck`, the PMA
    match against the `pma_regions` register, then `read_ram`. A rough token-reference count
    reaches about 1800 definitions from `execute_LOAD`, against about 90 from `execute_BTYPE`.
    The count overestimates, but the gap is real.
  - **Step 5.** `bench/sail/SSailRefine.lean` (565 lines, 130 s to check at 4.35; 26 s at 4.29)
    proves, against the patched model:
    `xget`/`xset` (the x-register file as Sail stores it), `rX_run` and `wX_run` (Sail's read and
    write equal them, for all 32 registers), `xget_xset` (read after write, all 1024 pairs),
    **`addi_run`** (every `imm`, `rs1`, `rd`: retires, `x[rd] := x[rs1] + sext imm`, `x0`
    dropped, nothing else touched) and **`beq_run`** (every `imm`, `rs1`, `rs2`, for a 4-byte
    aligned target with `misa` present: retires, sets `nextPC` iff equal, nothing else touched).
    With `--opaque`, all of them depend on `propext`, `Classical.choice` and `Quot.sound` only
    (`ssail-refine-check`). With the model's axioms kept, `beq_run` also depends on
    `sys_enable_experimental_extensions`; the opaque change is not cosmetic. The proofs are
    `simp` with a 32-way case split per register: slow to check, but they did not need ingenuity.
    Under 4.35 one name changed (`assert` to `sail_assert`).
    **LD is stated, not proved.** For `execute_LOAD imm rs1 rd false 8` in a state with
    `cur_privilege = Machine`, `mstatus.MPRV = 0`, every `pmpcfg_n` entry OFF, a `pma_regions`
    entry covering `[a, a+8)` that is readable with no misaligned exception, and
    `a = x[rs1] + sext imm` 8-byte aligned: it retires, and `x[rd]` becomes the little-endian
    word of `σ.mem` at `a`. The proof goes through translation, PMP and PMA. Judging by step 4,
    that is several sessions, past this spike's time box.
  - **Decision (step 6): proof route, with conditions.** The rule asked for "a handful of
    fixes". There are three kinds, all mechanical and scripted, though they touch 1342 lines;
    the reader can weigh that. ADDI and BEQ are proved, and LD is stated. The conditions:
    1. The model is pinned (commit + `apply-435.sh` + `lean-sail` commit) in the trust-base
       record. The script is dropped when upstream regenerates for 4.35.
    2. The 75 externs are `opaque`, never `axiom`; the project's no-new-axioms rule requires it.
    3. Loads and stores are the main proof cost. Until they are proved (PH5), they are covered
       by co-simulation against Spike, recorded as test evidence. The model cannot run in Lean
       under 4.35, because of (a), so co-simulation means Sail's C emulator or Spike, never the
       Lean model.
    4. Before PH5: import `InstsEnd`, not all of `LeanRV64D`, and time it. Report the `RvfiDii`
       regression upstream with the module and the two timings.

