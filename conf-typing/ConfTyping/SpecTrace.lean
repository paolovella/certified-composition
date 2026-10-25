/-
  The composable core, stage 2f: attacking the trace conjecture, and what it cost.

  Stage 2e reduced speculation on this core to one question. Four of the five
  certificates are immune because rollback is complete; the fifth is bounded; the only
  thing left is the address trace, and stage 2d stated the conjecture:

      for every program `xcheck` accepts, the speculative trace is a function of the Low
      part of the initial state, under every window.

  Attacking it did two things, and the first is a correction.

  **The conjecture was false, and not because of speculation.** `deadS` — a program that
  fails a mediation `check`, then allocates a secret pointer and dereferences it —
  **passes `xcheck`**, all five certificates, and its trace at window **zero** was `[11]`
  against `[77]` for two low-equivalent initial stores. No misprediction involved.

  The mechanism is a defect in stage 2d's trace, not in the certificates. A failed
  `check` sets `dead`, `uexec` then makes every subsequent command a no-op — so `allocS`
  never runs and `secret` keeps its *initial* value — and stage 2d's `touched` recorded
  an address anyway. A command that does not execute does not issue a memory operation.
  `touched` is now conditioned on `dead`, exactly as stage 1q had to condition `TaintInv`
  and for the same reason, and `touchedRaw` is kept so the defect can still be pointed
  at rather than quietly disappearing. `halted_machine_leaks_in_the_raw_model` and
  `the_fix_closes_it` are the two halves on record.

  Everything stages 2d and 2e proved survives the fix unchanged: none of their witness
  states is ever halted. That is luck rather than design, and it is why the witness is
  worth keeping.

  **The invariant the repaired conjecture needs.** With the trace fixed, the question
  becomes: do two low-equivalent runs touch the same addresses? Every traced address is
  `s.store x` for a *tracked* pointer `x`, so what is needed is

      `PtrLow V s s'` — every tracked pointer holds the same address in both runs.

  This is **not** implied by `uLowEqA`, and `ptrLow_is_not_implied_by_uLowEqA` proves it:
  `allcheck`'s `allocS` rule *requires* `P x = true`, so a secret-named variable can be a
  tracked pointer, and low-equivalence says nothing about its contents. The invariant
  holds anyway, for a different reason — the allocator is driven by `fresh` and `freed`,
  both of which `uLowEqA` does synchronise — and that is exactly the kind of fact that
  has to be carried rather than derived.

  `ptrLow_step` proves it inductive over every atomic command, and `touched_agrees`
  cashes it: two runs satisfying the invariant touch the same addresses. Those are the
  two halves of the step case for stage 2g, which is the whole-program induction plus
  the transient window.
-/
import ConfTyping.SpecBudget

namespace ConfTyping

/-! ## The correction: a halted machine does not touch memory -/

/-- Fails its mediation check, then allocates a secret pointer and dereferences it.
    `xcheck` accepts it: the `check` is present, `allocS` wants a secret-named target,
    and `deref` wants that target tracked. -/
def deadS : UCmd :=
  .seq (.check "db") (.seq (.memop .allocS "secret") (.memop .deref "secret"))

/-- The prefix, run to the point where the dereference is about to happen. -/
def deadPrefix : UCmd := .seq (.check "db") (.memop .allocS "secret")

def σlo : Store := fun x => if x = "secret" then 11 else 0
def σhi : Store := fun x => if x = "secret" then 77 else 0

theorem deadS_is_certified :
    xcheck Psec [] [] [] deadS = some ([], ["db"], ["secret"], 3, []) := by decide

/-- The two initial stores differ only in a secret. -/
theorem σlo_lowEq_σhi : lowEq Psec σlo σhi := by
  intro x hx
  have : ¬ (x = "secret") := by
    intro h; rw [h] at hx; exact absurd hx (by decide)
  simp only [σlo, σhi, ite_eq_right this]

/-- **The defect, on record.** After a failed `check` the machine is halted and the
    secret pointer still holds its *initial* value, so stage 2d's `touchedRaw` reports an
    address that differs between two low-equivalent runs — on a program carrying all five
    certificates, at window zero. Speculation had nothing to do with it. -/
theorem halted_machine_leaks_in_the_raw_model :
    ((uexec 12 deadPrefix (fun _ => false) (initU σlo)).map
       (fun r => (r.1.dead, touchedRaw (.memop .deref "secret") r.1))) = some (true, [11])
  ∧ ((uexec 12 deadPrefix (fun _ => false) (initU σhi)).map
       (fun r => (r.1.dead, touchedRaw (.memop .deref "secret") r.1))) = some (true, [77]) := by
  decide

/-- **And the fix closes it.** With `touched` conditioned on `dead`, the same program
    gives the same trace in both runs — empty, because a halted machine issues nothing.
    Under every window, since a halted machine speculates nothing either. -/
theorem the_fix_closes_it :
    straceU 12 0 deadS (fun _ => false) (initU σlo) = some []
  ∧ straceU 12 0 deadS (fun _ => false) (initU σhi) = some []
  ∧ straceU 12 3 deadS (fun _ => false) (initU σlo)
      = straceU 12 3 deadS (fun _ => false) (initU σhi) := by decide

/-- And the live run of the same program was never the problem: both traces agree there
    too, because the address comes from the allocator rather than from the store. -/
theorem the_live_run_was_always_fine :
    straceU 12 0 deadS (fun _ => true) (initU σlo)
      = straceU 12 0 deadS (fun _ => true) (initU σhi) := by decide

/-! ## The invariant: tracked pointers agree -/

/-- **Every tracked pointer holds the same address in both runs.** Conditioned on the
    machine being live, for the reason the section above exists. -/
def PtrLow (V : List String) (s s' : UState) : Prop :=
  s.dead = false → ∀ x ∈ V, s.store x = s'.store x

/-- It holds at the start, where nothing is tracked. -/
theorem ptrLow_initial (σ σ' : Store) : PtrLow [] (initU σ) (initU σ') := by
  intro _ x hx; cases hx

/-- **And it is not implied by low-equivalence.** `allcheck`'s `allocS` rule *requires*
    `P x = true`, so a secret-named variable is a legitimate tracked pointer, and
    `uLowEqA` constrains only the Low ones. The invariant holds anyway, for a different
    reason — the allocator is driven by `fresh` and `freed`, which `uLowEqA` does
    synchronise — which is precisely why it has to be carried rather than derived. -/
theorem ptrLow_is_not_implied_by_uLowEqA :
    ∃ (s s' : UState), uLowEqA Psec s s' ∧ ¬ PtrLow ["secret"] s s' := by
  refine ⟨initU σlo, initU σhi, ⟨σlo_lowEq_σhi, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl,
      rfl, fun _ _ => rfl⟩, ?_⟩
  intro h
  have := h rfl "secret" (List.mem_cons_self ..)
  simp only [initU, σlo, σhi] at this
  exact absurd this (by decide)

/-- The rule that makes a secret-named pointer legitimate, so the previous theorem is
    about the checker this repo has rather than a hypothetical one. -/
theorem allocS_wants_a_secret_name :
    allcheck Psec [] [] (.memop .allocS "secret") = some ([], ["secret"], 1)
  ∧ allcheck Psec [] [] (.memop .allocS "p") = none
  ∧ allcheck Psec [] [] (.memop .alloc "secret") = none := by decide

/-! ## The invariant is inductive, and it determines the trace -/

/-- Two shims, so proofs work with `touchedRaw` and the `dead` guard separately. -/
theorem touched_live {c : UCmd} {s : UState} (h : s.dead = false) :
    touched c s = touchedRaw c s := by simp [touched, h]

theorem touched_dead {c : UCmd} {s : UState} (h : s.dead = true) :
    touched c s = [] := by simp [touched, h]

/-- **What the invariant buys.** Two runs satisfying it touch the same addresses, because
    every traced address is a tracked pointer's and `jcheck` will not certify a
    dereference of anything else. -/
theorem touched_agrees {P : Partition} {V V' : List String} {c : UCmd} {s s' : UState}
    (hc : jcheck P V c = some V') (hd : s.dead = s'.dead) (hp : PtrLow V s s') :
    touched c s = touched c s' := by
  by_cases hdd : s.dead = true
  · have hdd' : s'.dead = true := by rw [← hd]; exact hdd
    rw [touched_dead hdd, touched_dead hdd']
  · simp only [Bool.not_eq_true] at hdd
    have hdd' : s'.dead = false := by rw [← hd]; exact hdd
    rw [touched_live hdd, touched_live hdd']
    cases c with
    | memop op y =>
        cases op with
        | deref =>
            by_cases hy : memStr y V = true
            · show [s.store y] = [s'.store y]
              rw [hp hdd y (memStr_mem hy)]
            · simp [jcheck, hy] at hc
        | alloc => rfl
        | allocS => rfl
        | free => rfl
    | hop op y z =>
        cases op with
        | load =>
            by_cases hz : memStr z V = true
            · show [s.store z] = [s'.store z]
              rw [hp hdd z (memStr_mem hz)]
            · simp [jcheck, hz] at hc
        | store =>
            by_cases hy : memStr y V = true
            · show [s.store y] = [s'.store y]
              rw [hp hdd y (memStr_mem hy)]
            · simp [jcheck, hy] at hc
    | _ => rfl

/-- Death is permanent: once `dead` is set, every command is a no-op. -/
theorem uexec_keeps_dead {c : UCmd} {π : MedPolicy} {s : UState}
    {r : UState × Nat × List Bool} (h : uexec 1 c π s = some r) (hd : s.dead = true) :
    r.1 = s := by
  cases c
  case loop e c₀ =>
    rw [uexec_loop_eq] at h
    by_cases hg : evalE e s.store ≠ 0
    · rw [ite_eq_left hg] at h; simp [uexec] at h
    · rw [ite_eq_right hg] at h; simp only [Option.some.injEq] at h; rw [← h]
  all_goals first
    | (simp [uexec] at h; done)
    | (simp only [uexec, Option.some.injEq] at h; subst h; simp [hd])

/-- **The invariant is inductive over every atomic command.** The two allocator cases are
    where the content is: the address handed out is `pickAddr s.freed s.fresh`, and
    `uLowEqA` synchronises both components, so even the *secret-named* pointer that
    `allocS` creates holds the same address in both runs. Everywhere else the invariant
    survives because the tracked set shrinks exactly where the store changes. -/
theorem ptrLow_step {P : Partition} {V V' : List String} {c : UCmd} {π : MedPolicy}
    {s s' : UState} {r r' : UState × Nat × List Bool}
    (hc : jcheck P V c = some V') (hlow : uLowEqA P s s') (hp : PtrLow V s s')
    (hr : uexec 1 c π s = some r) (hr' : uexec 1 c π s' = some r') :
    PtrLow V' r.1 r'.1 := by
  intro hdead x hx
  have hd0 : s.dead = false := by
    by_cases h : s.dead = true
    · exfalso; rw [uexec_keeps_dead hr h, h] at hdead; exact absurd hdead (by decide)
    · simpa using h
  have hd0' : s'.dead = false := by rw [← hlow.2.2.1]; exact hd0
  have hstore : ∀ y ∈ V, s.store y = s'.store y := hp hd0
  have hfresh : s.fresh = s'.fresh := hlow.2.2.2.1
  have hfreed : s.freed = s'.freed := hlow.2.2.2.2.2.2.1
  cases c with
  | seq _ _ => simp [uexec] at hr
  | ite _ _ _ => simp [uexec] at hr
  | loop e c₀ =>
      have hrr : r.1 = s := by
        rw [uexec_loop_eq] at hr
        by_cases hg : evalE e s.store ≠ 0
        · rw [ite_eq_left hg] at hr; simp [uexec] at hr
        · rw [ite_eq_right hg] at hr; simp only [Option.some.injEq] at hr; rw [← hr]
      have hrr' : r'.1 = s' := by
        rw [uexec_loop_eq] at hr'
        by_cases hg : evalE e s'.store ≠ 0
        · rw [ite_eq_left hg] at hr'; simp [uexec] at hr'
        · rw [ite_eq_right hg] at hr'; simp only [Option.some.injEq] at hr'; rw [← hr']
      simp only [jcheck] at hc
      split at hc
      · simp only [Option.some.injEq] at hc; subst hc
        rw [hrr, hrr']; exact hstore x hx
      · cases hc
  | skip =>
      simp only [uexec, Option.some.injEq] at hr hr'
      simp only [jcheck, Option.some.injEq] at hc
      rw [← hr, ← hr']; subst hc; exact hstore x hx
  | check q =>
      simp only [uexec, Option.some.injEq] at hr hr'
      simp only [jcheck, Option.some.injEq] at hc
      rw [← hr, ← hr']; subst hc
      rw [hd0, hd0']
      by_cases hq : π q = true
      · rw [ite_eq_left hq, ite_eq_left hq]; exact hstore x hx
      · rw [ite_eq_right hq, ite_eq_right hq]; exact hstore x hx
  | access q =>
      simp only [uexec, Option.some.injEq] at hr hr'
      simp only [jcheck, Option.some.injEq] at hc
      rw [← hr, ← hr']; subst hc; rw [hd0, hd0']; exact hstore x hx
  | assign y e =>
      simp only [uexec, Option.some.injEq] at hr hr'
      simp only [jcheck] at hc
      split at hc
      · simp only [Option.some.injEq] at hc; subst hc
        rw [← hr, ← hr', hd0, hd0']
        show upd s.store y (evalE e s.store) x = upd s'.store y (evalE e s'.store) x
        rw [upd, upd, ite_eq_right (dropStr_ne hx), ite_eq_right (dropStr_ne hx)]
        exact hstore x (dropStr_mem hx)
      · cases hc
  | sop op y e =>
      cases op <;>
        · simp only [uexec, Option.some.injEq] at hr hr'
          simp only [jcheck] at hc
          split at hc
          · simp only [Option.some.injEq] at hc; subst hc
            rw [← hr, ← hr', hd0, hd0']; exact hstore x hx
          · cases hc
  | memop op y =>
      cases op with
      | alloc =>
          simp only [uexec, Option.some.injEq] at hr hr'
          simp only [jcheck] at hc
          split at hc
          · cases hc
          · simp only [Option.some.injEq] at hc; subst hc
            have e1 : r.1.store = upd s.store y (pickAddr s.freed s.fresh) := by
              rw [← hr, hd0]; rfl
            have e1' : r'.1.store = upd s'.store y (pickAddr s'.freed s'.fresh) := by
              rw [← hr', hd0']; rfl
            rw [e1, e1', upd, upd, hfresh, hfreed]
            by_cases hxy : x = y
            · rw [ite_eq_left hxy, ite_eq_left hxy]
            · rw [ite_eq_right hxy, ite_eq_right hxy]
              exact hstore x ((List.mem_cons.mp hx).resolve_left hxy)
      | allocS =>
          simp only [uexec, Option.some.injEq] at hr hr'
          simp only [jcheck] at hc
          split at hc
          · simp only [Option.some.injEq] at hc; subst hc
            have e1 : r.1.store = upd s.store y (pickAddr s.freed s.fresh) := by
              rw [← hr, hd0]; rfl
            have e1' : r'.1.store = upd s'.store y (pickAddr s'.freed s'.fresh) := by
              rw [← hr', hd0']; rfl
            rw [e1, e1', upd, upd, hfresh, hfreed]
            by_cases hxy : x = y
            · rw [ite_eq_left hxy, ite_eq_left hxy]
            · rw [ite_eq_right hxy, ite_eq_right hxy]
              exact hstore x ((List.mem_cons.mp hx).resolve_left hxy)
          · cases hc
      | deref =>
          simp only [uexec, Option.some.injEq] at hr hr'
          simp only [jcheck] at hc
          split at hc
          · simp only [Option.some.injEq] at hc; subst hc
            have e1 : r.1.store = s.store := by
              rw [← hr, hd0]; split <;> (first | rfl | (split <;> rfl))
            have e1' : r'.1.store = s'.store := by
              rw [← hr', hd0']; split <;> (first | rfl | (split <;> rfl))
            rw [e1, e1']; exact hstore x hx
          · cases hc
      | free =>
          simp only [uexec, Option.some.injEq] at hr hr'
          simp only [jcheck] at hc
          split at hc
          · simp only [Option.some.injEq] at hc; subst hc
            have e1 : r.1.store = s.store := by
              rw [← hr, hd0]; split <;> (first | rfl | (split <;> rfl))
            have e1' : r'.1.store = s'.store := by
              rw [← hr', hd0']; split <;> (first | rfl | (split <;> rfl))
            rw [e1, e1']; exact hstore x (dropStr_mem hx)
          · cases hc
  | hop op y z =>
      cases op with
      | load =>
          simp only [uexec, Option.some.injEq] at hr hr'
          simp only [jcheck] at hc
          split at hc
          · simp only [Option.some.injEq] at hc; subst hc
            have hne : ¬ (x = y) := dropStr_ne hx
            have e1 : r.1.store x = s.store x := by
              rw [← hr, hd0]
              by_cases hl : memInt (s.store z) s.live = true <;> simp [hl, upd, hne]
            have e1' : r'.1.store x = s'.store x := by
              rw [← hr', hd0']
              by_cases hl : memInt (s'.store z) s'.live = true <;> simp [hl, upd, hne]
            rw [e1, e1']; exact hstore x (dropStr_mem hx)
          · cases hc
      | store =>
          simp only [uexec, Option.some.injEq] at hr hr'
          simp only [jcheck] at hc
          split at hc
          · simp only [Option.some.injEq] at hc; subst hc
            have e1 : r.1.store = s.store := by
              rw [← hr, hd0]; split <;> (first | rfl | (split <;> rfl))
            have e1' : r'.1.store = s'.store := by
              rw [← hr', hd0']; split <;> (first | rfl | (split <;> rfl))
            rw [e1, e1']; exact hstore x hx
          · cases hc

/-! ## What stage 2g needs

    Two things, and they are separable.

    * The **whole-program induction**: lift `ptrLow_step` and `touched_agrees` from a
      command to `uexecS`, carrying `uLowEqA` alongside — which stage 1x's
      `jsecTy_sound` already establishes for `uexec`, and `rollback_is_complete` transfers
      to `uexecS` for free.
    * The **transient window**: `transRun w (flatten c) π s` must agree between the two
      runs. `flatten` distributes over `seq` and `jcheck` threads the tracked set through
      it, so the same two lemmas apply, but the window runs the *untaken* branch and
      `jcheck`'s `ite` rule certifies both branches from the same `V` — which is why this
      is a lemma rather than an obstruction.

    What this stage deliberately does not do is guess at the outcome. The conjecture has
    already been false once, on a program the core certifies, and the reason was a defect
    that four sections of prose had walked past. -/

end ConfTyping
