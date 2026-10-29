/-
  **The vacuity finding, as theorems** (F2's refused witness; FOUNDATION-2026-10-29, A1).
  Not Ring 0.

  `bcheck` certifies `vacProg`: emit to `out`, then a counted loop whose body checks `db`.
  Under a policy that refuses `db`, the first check kills the run. A dead state is frozen, so
  the counter never moves, and the loop never returns (`uexec_dead_loop_diverges`). `uexec`
  then returns nothing at every fuel, and `ucmdLang` reports the empty record. So the three
  certificate shapes say nothing about this run. The program did emit (`vacProg_emits_first`),
  yet it carries both "emits nothing" and "costs 0" (`vacProg_vacuous`).

  F2 must make `vacProg_vacuous` false: a lawful language reports the emit in every prefix past
  the first step, and its cost grows without bound. When F2 lands, this file's statement is
  inverted, and the two theorems become the before and after of the fix.
-/
import ConfTyping.BudgetT

namespace ConfTyping.Vacuity

/-- Emit to `out`, then count down from 3 with a `check "db"` in the body. -/
def vacProg : UCmd :=
  .seq (.sop .emit "out" (.lit [.ord])) (forU "n" 3 (.check "db"))

/-- It is certified, with budget 12. -/
theorem vacProg_checks : bcheck Psec [] [] vacProg = some ([], [], 12) := by decide

def refuseAll : MedPolicy := fun _ => false

/-- The emit happens: the first command finishes and puts `("out", [ord])` on the sink. -/
theorem vacProg_emits_first (σ : Store) :
    (uexec 1 (.sop .emit "out" (.lit [.ord])) refuseAll (initU σ)).map (·.1.sink)
      = some [("out", [.ord])] := rfl

/-- The loop body, from a live state, ends dead with the store unchanged (or runs out). -/
theorem body_kills (m : Nat) (s : UState) (hs : s.dead = false)
    (r : UState × Nat × List Bool)
    (h : uexec m (.seq (.check "db") (decOne "n")) refuseAll s = some r) :
    r.1.dead = true ∧ r.1.store = s.store := by
  rcases m with _ | m
  · simp [uexec] at h
  rw [uexec_seq_eq] at h
  rcases e₁ : uexec m (.check "db") refuseAll s with _ | r₁
  · rw [e₁] at h; simp at h
  rcases m with _ | m
  · simp [uexec] at e₁
  have hr₁ : r₁.1 = { s with dead := true } := by
    simp only [uexec, hs, refuseAll] at e₁
    simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at e₁
    rw [← e₁]
  rw [e₁, Option.bind_some] at h
  rcases e₂ : uexec (m + 1) (decOne "n") refuseAll r₁.1 with _ | r₂
  · rw [e₂] at h; simp at h
  rw [e₂, Option.map_some, Option.some.injEq] at h
  have hd : r₁.1.dead = true := by rw [hr₁]
  have h₂ := uexec_dead_unchanged _ _ _ _ _ hd e₂
  rw [← h]
  refine ⟨?_, ?_⟩
  · show r₂.1.dead = true; rw [h₂]; exact hd
  · show r₂.1.store = s.store; rw [h₂, hr₁]

/-- From a live state whose counter is nonzero, the loop never returns. -/
theorem loop_diverges (k : Nat) (s : UState) (hs : s.dead = false) (hn : s.store "n" ≠ 0) :
    uexec k (countU "n" (.check "db")) refuseAll s = none := by
  rcases k with _ | k
  · rfl
  unfold countU
  rw [uexec_loop_eq]
  have hg : evalE (.var "n") s.store ≠ 0 := hn
  rw [ite_eq_left hg]
  rcases e₁ : uexec k (.seq (.check "db") (decOne "n")) refuseAll s with _ | r₁
  · simp
  obtain ⟨hd, hst⟩ := body_kills k s hs r₁ e₁
  have hg' : evalE (.var "n") r₁.1.store ≠ 0 := by rw [hst]; exact hg
  rw [Option.bind_some, uexec_dead_loop_diverges k _ _ _ _ hd hg']
  simp

/-- **`vacProg` never returns under `refuseAll`, at any fuel.** -/
theorem vacProg_diverges (n : Nat) (σ : Store) : uexec n vacProg refuseAll (initU σ) = none := by
  rcases n with _ | n
  · rfl
  unfold vacProg
  rw [uexec_seq_eq]
  rcases e₁ : uexec n (.sop .emit "out" (.lit [.ord])) refuseAll (initU σ) with _ | r₁
  · simp
  rw [Option.bind_some]
  rcases n with _ | n
  · simp [uexec] at e₁
  have hr₁ : r₁.1.dead = false := by
    simp only [uexec, initU, Option.some.injEq] at e₁; rw [← e₁]; rfl
  unfold forU
  rw [uexec_seq_eq]
  rcases e₂ : uexec n (.assign "n" (.num ((3 : Nat) : Int))) refuseAll r₁.1 with _ | r₂
  · simp
  rcases n with _ | n
  · simp [uexec] at e₂
  simp only [uexec, hr₁, Bool.false_eq_true, ite_false, Option.some.injEq] at e₂
  subst e₂
  rw [Option.bind_some, loop_diverges]
  · simp
  · exact hr₁ ▸ rfl
  · simp [upd, evalE]

/-- **The finding.** The certified program `vacProg`, which emits, carries both "emits nothing"
    and "costs 0" on `ucmdLang` under `refuseAll`: every run is the empty record. -/
theorem vacProg_vacuous :
    LCore.Cert.trace (ucmdLang Psec refuseAll) (fun evs => evs = []) vacProg
  ∧ LCore.Cert.bound (ucmdLang Psec refuseAll) 0 vacProg := by
  refine ⟨fun n (σ : Store) => ?_, fun n (σ : Store) => ?_⟩
  · show (uBeh _ _).ev = []
    rw [vacProg_diverges]; rfl
  · show (uBeh _ _).cost ≤ 0
    rw [vacProg_diverges]; exact Nat.le_refl 0

/-! ## After F2: on the lawful `ucmdLangT` (halting abort, one trace) -/

/-- On `ucmdLangT` the same run shows what happened: the emit, then the refused check, and
    then it halts with `abort`. -/
theorem vacProg_halts :
    (ucmdLangT Psec refuseAll).run 10 vacProg (fun _ => 0)
      = { ev := [.emit "out" [0], .check "db"], lk := [.branch true], cost := 4,
          out := .abort } := by decide

/-- **The finding, inverted.** Neither "emits nothing" nor "costs 0" holds of `vacProg` on
    `ucmdLangT`. -/
theorem vacProg_not_vacuous :
    ¬ LCore.Cert.trace (ucmdLangT Psec refuseAll) (fun evs => evs = []) vacProg
  ∧ ¬ LCore.Cert.bound (ucmdLangT Psec refuseAll) 0 vacProg := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h 10 (fun _ => 0); rw [vacProg_halts] at this; cases this
  · have := h 10 (fun _ => 0); rw [vacProg_halts] at this; cases this

/-- **The budget is carried, and it is not trivial.** On `ucmdLangT`, `bcheck`'s budget 12
    holds of `vacProg` on every run (`bcheck_boundT`), and a budget of 3 does not: the run
    costs 4 before it halts. -/
theorem vacProg_budgetT :
    LCore.Cert.bound (ucmdLangT Psec refuseAll) 12 vacProg
  ∧ ¬ LCore.Cert.bound (ucmdLangT Psec refuseAll) 3 vacProg := by
  refine ⟨bcheck_boundT vacProg_checks refuseAll, fun h => ?_⟩
  have := h 10 (fun _ => 0); rw [vacProg_halts] at this
  exact absurd this (by decide)

/-- The repo's loop handler keeps its budget of 40 on every run of the lawful language. -/
theorem loopHandler_boundT (π : MedPolicy) : LCore.Cert.bound (ucmdLangT Psec π) 40 loopHandler :=
  bcheck_boundT loopHandler_checks π

end ConfTyping.Vacuity
