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

