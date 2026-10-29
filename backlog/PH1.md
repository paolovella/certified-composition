---
id: PH1
title: Phase 1 spine: Obs, Lang, Cert shapes, PassCert, transfer + composition; UCmd as first Lang; sketch as P1
ring: 0
tier: G-0
deps: [P0-03]
closes: ['certificates proved per pass']
acceptance: ucmd_p1_carries with zero certificate-specific pass proofs
kill: S-OBS fails: public-only allocator
status: in-progress
---

## Plan

PLAN-2026-10 §2 (Ring 0 artifacts), §4 (P1), §12 (Phase 1). S-OBS (done 2026-10-28) settled the
kill rule: addresses can join the leakage, so no fallback allocator is needed.

**Where.** A new Lake package `l-core/` (mathlib-free, Lean v4.35.0, `LCore/Kernel/`), added
to the root workspace. Everything under `LCore/Kernel/` is Ring 0: proposed on this branch,
merged only with the user's key. The UCmd adapter and P1 live outside the kernel.

1. **`Obs.lean`.** One observation for every language:
   `Beh := {ev : List Ev, lk : List Lk, cost : Nat, out : Outcome}`, with
   `Outcome := done | abort | fuel` (`fuel` means the run is a prefix). `Ev` covers the events
   certificates talk about (check, read, emit, alloc/free). `Lk` covers leakage: branch bits
   and addresses. Internal state is not observed.
2. **`Lang.lean`.** `structure Lang` with `Prog`, `In`, `lowIn : In → In → Prop` and
   `run : Nat → Prog → In → Beh`, plus the fuel laws certificates need: `stable` (a `done`
   result does not change with more fuel) and `prefix` (more fuel only extends `ev` and `lk`).
3. **`Cert.lean`.** Three certificate shapes, each with its meaning defined once:
   - `trace Φ`: every run's events satisfy a prefix-closed `Φ` (mediation, memory safety);
   - `rel`: Low-equal inputs give equal `lk`, `cost`, `out` and Low events (fuel-TSNI,
     PLAN-2026-10 §2);
   - `bound k`: every run costs at most `k`.
4. **`Pass.lean`.** `PassCert S T`:
   - `comp : S.Prog → Except Diag T.Prog`;
   - an input encoding `enc` that preserves `lowIn`;
   - leakage and cost transformers `lkT`, `costT` that depend only on the program and the
     source leakage;
   - `sim`: a target run's `Beh` is the source run's, with `lk` and `cost` transformed.

   Proved once: `trace_transfer`, `rel_transfer` (needs `lkT` to depend only on the program
   and the source `lk`), `bound_transfer` (needs `costT` monotone), and `PassCert.comp`
   (transformers compose). No certificate is ever proved per pass.
5. **P1, names to slots** (outside the kernel, CMP-P1 rebuilt, I-0003):
   - the target language `TCmd` with slot indices;
   - `compile` as in `bench/kernel/gen.py`, returning `Except Diag`, refusing when two
     variables collide;
   - the `PassCert` with `lkT = id` and `costT = id`;
   - the frame theorem (no write outside the slot table);
   - `colliding_slots_leak` as P1's refused witness.
6. **UCmd as the first `Lang`.** Adapter `ucmdLang` over `uexec`, with `Beh` from the final
   state and the branch trace, and addresses from `uaddrs` (S-OBS). Adequacy for the budget
   (`bound`), mediation (`trace`) and NI (`rel`): the existing UCmd theorems imply the shapes.
7. **Exit:** `ucmd_p1_carries`. A UCmd program's budget, mediation and NI certificates hold
   for its P1 output, by the transfer theorems alone. A guard enforces zero certificate-specific
   pass lemmas (PLAN-2026-10 §14: grep-guarded).

Order: 1–4 first, as one PR for the user's key, with each shape inhabited and refuted by a
toy `Lang`. Then 6, 5, 7. Each step builds and runs CI before the next.

## Log
- 2026-10-28, branch `ph1/spine`: **steps 1–4, the kernel** (`l-core/LCore/Kernel/`, Ring 0).
  - `Obs` (`Beh` = events, leakage, cost, outcome), `Lang`, the three certificate shapes
    (`Cert.trace`, `Cert.rel`, `Cert.bound`) and `PassCert`, with `trace_transfer`,
    `rel_transfer`, `bound_transfer` and `PassCert.seq`. The transfer theorems and the
    composition use no axioms.
  - Design: `Beh` is all observable, so `rel` is one equation. `PassCert.sim` is an equation
    at a program-dependent fuel. That fits lockstep passes like P1; the prefix and stability
    laws wait for the first pass that needs them, as the kernel's docstring says.
  - Witnesses (`LCore/Witnesses.lean`, not Ring 0): each shape is inhabited and refuted on a
    toy language. A padding pass carries all three certificates, with the budget transformed
    (3 → 4), and keeps a real leak distinguishable. Composition is exercised too.
  - Wiring:
    - `conf-typing` requires `l-core`; the axiom manifest audits `LCore`; the root workspace
      imports it, so `lake check` and the six-kernel export see it;
    - CI step "l-core builds";
    - CLAUDE.md names `l-core/LCore/Kernel/` as Ring 0, and so does the gate;
    - gate witnesses: a kernel edit is flagged as Ring 0, an edit outside the kernel is not
      (23 quick cases);
    - the toolchain guard covers `l-core/lean-toolchain`.
  - CI: the first two full runs failed. Run 1: every tool that copies `conf-typing` to build mutants or witnesses (`mutants.py`, the registry, mutant, gate, comparator, lock and warden witnesses) did not copy `l-core`, which `conf-typing` now requires. Fixed in all of them, plus the CI caches. Run 2: the axiom manifest was generated before the composition witness was added. Run 3 green (`ph1-ci-full3`, 1037 s).
- 2026-10-28, branch `ph1/ucmd-lang` (stacked on `ph1/spine`): **step 6, UCmd as the first
  `Lang`** (`conf-typing/ConfTyping/LAdapter.lean`, not Ring 0).
  - `ucmdLang P π`: the input is the initial store, Low-equality is `lowEq P`, and the
    observation is built from `uexec` and `uaddrs`:
    - events: reads, then emits;
    - leakage: the branch trace, then the address trace;
    - outcome: abort if dead, done otherwise, and `fuel` with an empty record when the fuel
      runs out.
  - **Adequacy** (`bcheck_lcore`): a program `bcheck` accepts carries `Cert.bound k`,
    `Cert.trace (mediated π)` and `Cert.rel` on `ucmdLang`, from `bcheck_sound`,
    `jsecTy_sound` and S-OBS's `jsecTy_addrs`.
  - Witnesses: `loopHandler_lcore` (the loop handler, budget 40, all three shapes);
    `secretBranch_not_rel` (a secret branch is not `rel`, decided).
  - Limits, stated: v1 events record reads and emits in two lists, not interleaved, and a
    fuel-exhausted run records nothing (`uexec` gives no prefix).
  - Full CI green (`ph1-ucmd-ci-full`, 1018 s).
- 2026-10-28, same branch: **step 5, P1 (names to slots), and step 7, the exit.**
  (`conf-typing/ConfTyping/P1.lean`, not Ring 0; CMP-P1 rebuilt after I-0003.)
  - The slot machine (`SlotState`, `texec`) mirrors `uexec` with a `Nat`-indexed integer
    store. `compile T` maps each variable `x` to slot `slotOf T x`. `slotLang` is the slot
    machine as an L `Lang`; a program carries its table, so `PassCert.enc` is the identity.
    That is a design point the plan's sketch did not have: `enc` cannot depend on the program,
    but the table does.
  - `texec_compile` (the simulation): with a table that lists each variable once and covers
    the program, the compiled run is the source run, with the slot store read through the
    table. `taddrs_compile`: same addresses.
  - `p1Pass : PassCert (ucmdLang P π) (slotLang P π)`, with **identity** leakage and cost
    transformers: a compiled program's observation equals its source's.
  - **`ucmd_p1_carries`, the Phase 1 exit**: a `bcheck`-accepted program keeps its budget,
    mediation and noninterference (addresses in the leakage) after P1, by the kernel's
    `bound_transfer`, `trace_transfer` and `rel_transfer` alone. Guard (m) enforces it: in
    `P1.lean`, only `ucmd_p1_carries` may mention a certificate, and its proof may use only
    the three transfer theorems and `bcheck_lcore`. Self-test 78; two cases fire it.
  - `texec_frame`: compiled code never writes a slot outside its table.
  - Witnesses:
    - `p1Demo_runs`: decided; the compiled program reads `db` as its source does;
    - `collide_breaks_simulation`: decided; with a table that does not cover the program,
      two variables share a slot and the observation changes.
  - Deviation from the plan, stated: `colliding_slots_leak` (NI broken by a collision) cannot
    arise from this compiler. `slotOf` is injective on the table, and only names outside the
    table can collide, which is a coverage failure. The collision witness is therefore about
    the simulation, not about NI.
- **Phase 1's exit is met** (PLAN-2026-10 §12: `ucmd_p1_carries` with zero certificate-specific
  pass proofs). PH1 stays in progress until the kernel (PR #14, Ring 0) and this branch merge
  with the user's key.
  - Full CI green (`ph1-p1-ci-full`, 954 s).
- 2026-10-29, branch `ph1/spine`: **plan, `seq` compiles once.** The user's review: later
  passes get slower. In 30f0720, `PassCert.seq` computes `lkT`, `costT` and `fuelT` by
  running the earlier stages' compiler again, so evaluating one transformer of an n-pass
  left-nested pipeline compiles about n²/2 times. PH5 evaluates the pipeline in the kernel.
  Fix: `comp` returns the compiled program *with* its transformers (`Xform`: `lk`, `cost`,
  `fuel`, `costMono`), and `seq` composes the two `Xform`s it already has (`Xform.then`), so
  each stage compiles once. The transformers still never see the input: they are produced by
  compiling the program. Witnesses move to the new shape; a three-pass pipeline's budget is
  computed by `decide` (`seq3_budget`).
  - Done. `PassCert.comp` returns `(T.Prog × Xform)`; `PassCert.seq` composes the `Xform`s it
    already holds (`Xform.then`), so each stage compiles once. `seq` and the three transfer
    theorems still use no axioms (`tools/axioms.expected`). Witnesses: `seq3_budget` (the
    kernel computes a three-pass pipeline's budget, 3 → 5, by `rfl`), `seq3_carries_bound`
    (the same budget through `bound_transfer`), and `seq_refusal_propagates` (a refusing
    stage refuses the pipeline). A first proof of `seq` used `simp`'s injectivity lemmas and
    picked up `propext`; the axiom manifest showed it, and the proof was rewritten with
    `rw`/`cases`. Full CI green (`ph1-seq-ci-full`, 962 s).
