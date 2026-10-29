/-
  A certified pass, and why certificates never need per-pass proofs (PLAN-2026-10 §2,
  `Pass.lean`). Ring 0.

  A `PassCert S T` is a compiler from `S` to `T` and one simulation fact: a run of the compiled
  program on an encoded input *is* a run of the source program, with only the leakage and the
  cost rewritten. The compiler returns, with each compiled program, the transformers (`Xform`)
  that rewrite them. The transformers are produced from the program alone, so they never see
  the input. From that one fact every certificate shape transfers (`trace_transfer`,
  `rel_transfer`, `bound_transfer`), and passes compose (`PassCert.seq`). So a new pass costs
  one simulation proof and no certificate proofs, and a new certificate costs nothing per pass
  (PLAN-2026-10 §6).

  The transformers travel with the compiled program so that composing passes compiles each
  stage once: `seq` composes the two `Xform`s it already holds and never re-runs an earlier
  stage. (A first version, 30f0720, recomputed them by recompiling, which made an n-pass
  pipeline compile about n²/2 times.)

  This form needs the target run to correspond to a source run at a fuel that depends only on
  the program (`Xform.fuel`). That fits lockstep passes such as P1. Passes that change the fuel
  unit will need the prefix and stability laws of PLAN-2026-10 §2, and they will be added when a
  pass needs them.
-/
import LCore.Kernel.Cert

namespace LCore

/-- How one compiled program's observation relates to its source's: the leakage transformer,
    the cost transformer (monotone, so budgets carry over), and which source fuel a target fuel
    corresponds to. -/
structure Xform where
  lk    : List Lk → List Lk
  cost  : Nat → Nat
  fuel  : Nat → Nat
  costMono : ∀ (a b : Nat), a ≤ b → cost a ≤ cost b

/-- Nothing rewritten. -/
def Xform.id : Xform where
  lk l := l
  cost c := c
  fuel m := m
  costMono _ _ h := h

/-- `t` then `u`: leakage and cost go through `t` first; a target fuel goes back through `u`
    first. -/
def Xform.then (t u : Xform) : Xform where
  lk l := u.lk (t.lk l)
  cost c := u.cost (t.cost c)
  fuel m := t.fuel (u.fuel m)
  costMono a b h := u.costMono _ _ (t.costMono a b h)

structure PassCert (S T : Lang) where
  /-- The compiler, returning the compiled program and its transformers. A refusal carries a
      diagnostic, which is untrusted text. -/
  comp  : S.Prog → Except String (T.Prog × Xform)
  /-- How a source input is presented to the compiled program. -/
  enc   : S.In → T.In
  /-- **The simulation.** The compiled run is the source run, with leakage and cost
      transformed. -/
  sim : ∀ (p : S.Prog) (p' : T.Prog) (t : Xform), comp p = .ok (p', t) →
    ∀ (m : Nat) (i : S.In),
    T.run m p' (enc i) =
      { (S.run (t.fuel m) p i) with
          lk   := t.lk (S.run (t.fuel m) p i).lk,
          cost := t.cost (S.run (t.fuel m) p i).cost }

namespace PassCert

variable {S T : Lang} (pc : PassCert S T) {p : S.Prog} {p' : T.Prog} {t : Xform}

/-- Events pass through unchanged, so every `trace` certificate transfers. -/
theorem trace_transfer (h : pc.comp p = .ok (p', t)) {Φ : List Ev → Prop}
    (hc : Cert.trace S Φ p) : ∀ (m : Nat) (i : S.In), Φ (T.run m p' (pc.enc i)).ev := by
  intro m i
  rw [pc.sim p p' t h m i]
  exact hc (t.fuel m) i

/-- The compiled observation is a function of the source observation and the program, so
    indistinguishable source runs stay indistinguishable. -/
theorem rel_transfer (h : pc.comp p = .ok (p', t)) (hc : Cert.rel S p) :
    ∀ (m : Nat) (i i' : S.In), S.lowIn i i' →
      T.run m p' (pc.enc i) = T.run m p' (pc.enc i') := by
  intro m i i' hl
  rw [pc.sim p p' t h m i, pc.sim p p' t h m i', hc (t.fuel m) i i' hl]

/-- A budget transfers through the (monotone) cost transformer. -/
theorem bound_transfer (h : pc.comp p = .ok (p', t)) {k : Nat} (hc : Cert.bound S k p) :
    ∀ (m : Nat) (i : S.In), (T.run m p' (pc.enc i)).cost ≤ t.cost k := by
  intro m i
  rw [pc.sim p p' t h m i]
  exact t.costMono _ _ (hc (t.fuel m) i)

end PassCert

/-- **Passes compose.** Each stage compiles once; the transformers compose (`Xform.then`) and
    the simulation is the two simulations chained. A pipeline of certified passes is a
    certified pass. -/
def PassCert.seq {S T U : Lang} (pc : PassCert S T) (qc : PassCert T U) : PassCert S U where
  comp p := match pc.comp p with
    | .error e => .error e
    | .ok (p', t) => match qc.comp p' with
      | .error e => .error e
      | .ok (p'', u) => .ok (p'', t.then u)
  enc i := qc.enc (pc.enc i)
  sim p p'' tu h m i := by
    cases hp : pc.comp p with
    | error e => rw [hp] at h; cases h
    | ok r =>
      obtain ⟨p', t⟩ := r
      cases hq : qc.comp p' with
      | error e => rw [hp] at h; dsimp only at h; rw [hq] at h; cases h
      | ok r' =>
        obtain ⟨p''', u⟩ := r'
        rw [hp] at h; dsimp only at h; rw [hq] at h; cases h
        rw [qc.sim p' _ u hq m (pc.enc i), pc.sim p p' t hp (u.fuel m) i]
        rfl

end LCore
