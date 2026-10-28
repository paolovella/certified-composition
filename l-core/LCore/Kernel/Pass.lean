/-
  A certified pass, and why certificates never need per-pass proofs (PLAN-2026-10 §2,
  `Pass.lean`). Ring 0.

  A `PassCert S T` is a compiler from `S` to `T` and one simulation fact: a run of the compiled
  program on an encoded input *is* a run of the source program, with only the leakage and the
  cost rewritten, and rewritten by transformers that look at the program and the source
  leakage, never at the input. From that one fact every certificate shape transfers
  (`trace_transfer`, `rel_transfer`, `bound_transfer`), and passes compose
  (`PassCert.comp`). So a new pass costs one simulation proof and no certificate proofs, and a
  new certificate costs nothing per pass (PLAN-2026-10 §6).

  This form needs the target run to correspond to a source run at a fuel that depends only on
  the program (`fuelT`). That fits lockstep passes such as P1. Passes that change the fuel unit
  will need the prefix and stability laws of PLAN-2026-10 §2, and they will be added when a pass
  needs them.
-/
import LCore.Kernel.Cert

namespace LCore

structure PassCert (S T : Lang) where
  /-- The compiler. A refusal carries a diagnostic, which is untrusted text. -/
  comp  : S.Prog → Except String T.Prog
  /-- How a source input is presented to the compiled program. -/
  enc   : S.In → T.In
  /-- The leakage transformer: it depends on the program and the source leakage only. -/
  lkT   : S.Prog → List Lk → List Lk
  /-- The cost transformer, monotone so budgets carry over. -/
  costT : S.Prog → Nat → Nat
  /-- Which source fuel a target fuel corresponds to; it depends on the program only. -/
  fuelT : S.Prog → Nat → Nat
  costMono : ∀ (p : S.Prog) (a b : Nat), a ≤ b → costT p a ≤ costT p b
  /-- **The simulation.** The compiled run is the source run, with leakage and cost
      transformed. -/
  sim : ∀ (p : S.Prog) (p' : T.Prog), comp p = .ok p' → ∀ (m : Nat) (i : S.In),
    T.run m p' (enc i) =
      { (S.run (fuelT p m) p i) with
          lk   := lkT p (S.run (fuelT p m) p i).lk,
          cost := costT p (S.run (fuelT p m) p i).cost }

namespace PassCert

variable {S T : Lang} (pc : PassCert S T) {p : S.Prog} {p' : T.Prog}

/-- Events pass through unchanged, so every `trace` certificate transfers. -/
theorem trace_transfer (h : pc.comp p = .ok p') {Φ : List Ev → Prop}
    (hc : Cert.trace S Φ p) : ∀ (m : Nat) (i : S.In), Φ (T.run m p' (pc.enc i)).ev := by
  intro m i
  rw [pc.sim p p' h m i]
  exact hc (pc.fuelT p m) i

/-- The compiled observation is a function of the source observation and the program, so
    indistinguishable source runs stay indistinguishable. -/
theorem rel_transfer (h : pc.comp p = .ok p') (hc : Cert.rel S p) :
    ∀ (m : Nat) (i i' : S.In), S.lowIn i i' →
      T.run m p' (pc.enc i) = T.run m p' (pc.enc i') := by
  intro m i i' hl
  rw [pc.sim p p' h m i, pc.sim p p' h m i', hc (pc.fuelT p m) i i' hl]

/-- A budget transfers through the (monotone) cost transformer. -/
theorem bound_transfer (h : pc.comp p = .ok p') {k : Nat} (hc : Cert.bound S k p) :
    ∀ (m : Nat) (i : S.In), (T.run m p' (pc.enc i)).cost ≤ pc.costT p k := by
  intro m i
  rw [pc.sim p p' h m i]
  exact pc.costMono p _ _ (hc (pc.fuelT p m) i)

end PassCert

/-- **Passes compose.** The transformers compose, the fuel maps compose, and the simulation
    is the two simulations chained. A pipeline of certified passes is a certified pass. -/
def PassCert.seq {S T U : Lang} (pc : PassCert S T) (qc : PassCert T U) : PassCert S U where
  comp p := (pc.comp p).bind qc.comp
  enc i := qc.enc (pc.enc i)
  lkT p l := match pc.comp p with
    | .ok p' => qc.lkT p' (pc.lkT p l)
    | .error _ => l
  costT p c := match pc.comp p with
    | .ok p' => qc.costT p' (pc.costT p c)
    | .error _ => c
  fuelT p m := match pc.comp p with
    | .ok p' => pc.fuelT p (qc.fuelT p' m)
    | .error _ => m
  costMono p a b hab := by
    cases hp : pc.comp p with
    | ok p' => exact qc.costMono p' _ _ (pc.costMono p a b hab)
    | error _ => exact hab
  sim p p'' h m i := by
    cases hp : pc.comp p with
    | error e => rw [hp] at h; cases h
    | ok p' =>
        rw [hp] at h
        have hq : qc.comp p' = .ok p'' := h
        rw [qc.sim p' p'' hq m (pc.enc i), pc.sim p p' hp (qc.fuelT p' m) i]

end LCore
