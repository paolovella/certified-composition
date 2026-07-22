/-
  The seam over loops — brick 8: certified looping components compose.

  Brick 7 gave termination-sensitive soundness for the looping language, but the
  composition machinery — the program's differentiator — still lived only on
  loop-free `Cmd` (bricks 2, 4). This module ports the seam to `WCmd`: two
  components each certified for the *whole fuelled outcome* (store, cost, trace,
  **and termination**) compose into a certified pipeline, with the halting
  guarantee threading through the boundary.

  The boundary certificate is `WOutNI c P` — at every fuel, Low-equal runs are
  `optLowEq` (halt together, agree on Low store / running time / trace). It is
  exactly what `wsecTy_sound` produces, so a `wcheck`-passing component earns it
  by `decide`. The seam theorem `WOutNI_seq` composes them, and its content is
  the brick-2 seam plus one new clause the loop-free version never had: if `c₁`
  diverges, so does the composite, *in lockstep* — divergence composes, and the
  termination channel stays closed across the seam.

  Teeth: `wleak_poisons_seam` — a divergence-leaking upstream (`Wleak`) wired
  into a certified downstream makes the composite leak too; the seam's `c₁`
  hypothesis is load-bearing, just as in the loop-free case.
-/
import ConfTyping.WhileImp

namespace ConfTyping

/-! ## The looping boundary certificate -/

/-- Full-outcome, termination-sensitive boundary certificate: at every fuel,
    Low-equal runs of `c` are `optLowEq` — they halt together and agree on Low
    store, running time, and trace. -/
def WOutNI (c : WCmd) (P : Partition) : Prop :=
  ∀ n σ σ', lowEq P σ σ' → optLowEq P (wexec n c σ) (wexec n c σ')

/-- Soundness (brick 7) restated as a boundary certificate: a well-typed
    looping component carries `WOutNI`. -/
theorem wsecTy_WOutNI {P : Partition} {c : WCmd} (h : WSecTy P c) :
    WOutNI c P :=
  fun n σ σ' hle => wsecTy_sound n c h σ σ' hle

/-- And the checker manufactures it, by `decide`. -/
theorem WOutNI_of_wcheck {P : Partition} {c : WCmd} (h : wcheck P c = true) :
    WOutNI c P :=
  wsecTy_WOutNI (wcheck_sound h)

/-! ## The seam: certified looping components compose -/

/-- **The seam over loops.** Two components carrying the full-outcome
    termination-sensitive certificate compose into one. The proof threads
    `optLowEq` through the fuelled `seq` via the brick-7 plumbing
    (`optLowEq_bind`/`optLowEq_map`): if both halt, Low store / cost / trace
    compose; **if `c₁` diverges the composite diverges in lockstep** — the
    clause the loop-free seam never had, keeping the termination channel closed
    across the boundary. -/
theorem WOutNI_seq {c₁ c₂ : WCmd} {P : Partition}
    (h₁ : WOutNI c₁ P) (h₂ : WOutNI c₂ P) :
    WOutNI (.seq c₁ c₂) P := by
  intro n σ σ' hle
  cases n with
  | zero => exact True.intro
  | succ m =>
      rw [wexec_seq_eq, wexec_seq_eq]
      refine optLowEq_bind (h₁ m σ σ' hle) ?_
      intro r₁ r₁' hs₁ hcost₁ htr₁
      refine optLowEq_map (h₂ m r₁.1 r₁'.1 hs₁) ?_
      intro r₂ r₂' hs₂ hcost₂ htr₂
      exact ⟨hs₂, by rw [hcost₁, hcost₂], by rw [htr₁, htr₂]⟩

/-- **Certificates by `decide`, composed.** Two `wcheck`-passing looping
    components form a certified pipeline with no per-composite reasoning. -/
theorem WOutNI_seq_of_check {c₁ c₂ : WCmd} {P : Partition}
    (h₁ : wcheck P c₁ = true) (h₂ : wcheck P c₂ = true) :
    WOutNI (.seq c₁ c₂) P :=
  WOutNI_seq (WOutNI_of_wcheck h₁) (WOutNI_of_wcheck h₂)

/-- The seam also holds directly at the typing level (the composition rule of
    `WSecTy` is already there; this records that it *is* the seam). -/
theorem wsecTy_seq_WOutNI {c₁ c₂ : WCmd} {P : Partition}
    (h₁ : WSecTy P c₁) (h₂ : WSecTy P c₂) :
    WOutNI (.seq c₁ c₂) P :=
  WOutNI_seq (wsecTy_WOutNI h₁) (wsecTy_WOutNI h₂)

/-! ## A certified looping pipeline -/

/-- Two Low-guarded loops in sequence — certified as a pipeline from two
    `decide`s, termination included. -/
theorem wok_pipeline_certified : WOutNI (.seq Wok Wok) Phigh :=
  WOutNI_seq_of_check (by decide) (by decide)

/-! ## Teeth: divergence-leak poisons the seam -/

/-- At fuel 2 the composite still spins on a nonzero secret: the upstream
    `Wleak` diverges, so the whole pipeline does. -/
theorem wleak_seq_spin (σ : Store) (h : σ "b" ≠ 0) :
    wexec 2 (.seq Wleak .skip) σ = none := by
  simp [wexec_seq_eq, wexec, Wleak, evalE, h]

/-- At fuel 2 a secret-zero run halts (upstream loop exits, downstream `skip`
    runs). -/
theorem wleak_seq_halt (σ : Store) (h : σ "b" = 0) :
    wexec 2 (.seq Wleak .skip) σ = some (σ, 2, [false]) := by
  simp [wexec_seq_eq, wexec, Wleak, evalE, h]

/-- `skip` is a perfectly certified downstream. -/
theorem skip_WOutNI : WOutNI .skip Phigh :=
  WOutNI_of_wcheck (by decide)

/-- **A divergence-leaking upstream poisons the seam.** `skip` is certified
    (`skip_WOutNI`), but `Wleak; skip` is not `WOutNI`: at fuel 2 a
    secret-nonzero run diverges while a secret-zero run halts — the composite
    leaks termination. The seam's upstream hypothesis is load-bearing over
    loops, exactly as in the loop-free seam's `broken_seam`. -/
theorem wleak_poisons_seam :
    ¬ (∀ n σ σ', lowEq Phigh σ σ' →
        optLowEq Phigh (wexec n (.seq Wleak .skip) σ)
                       (wexec n (.seq Wleak .skip) σ')) := by
  intro h
  have key := h 2 σ0 σ1 lowEq_σ
  rw [wleak_seq_spin σ0 (by simp [σ0, upd]),
      wleak_seq_halt σ1 (by simp [σ1])] at key
  exact key

end ConfTyping
