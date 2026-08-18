/-
  The reception's ledger has no teeth, and why — plus the constructor that gives it some.

  Stage B receives CN's ownership clause and carries a trusted base alongside it.
  `CNTrust.needs` computes that base from the proof's own features, and
  `cn_base_strictly_smaller` exhibits a world where the solver is unsound and the frame
  certificate stands anyway. Both are real. What connects them is nothing:

  * `Bridge.ofCN f F Γ h` accepts **any** `Γ` whatsoever. Its `contracts` field never
    mentions `Γ`, and no hypothesis constrains it. Pass `[]`, pass `[False]` — the same
    Bridge is built either way.
  * `CNTrust.needs` has **no call sites**. The one place a CN Bridge is actually
    constructed (`HeteroCompose.clear5CN`) takes an arbitrary ledger parameter.

  So the computed base and the carried base are two pieces of working machinery joined
  by a docstring. This module states that as a theorem rather than a complaint, and then
  closes it.

  ── The diagnosis, as a theorem ──
  `ofCN_ledger_inert_for_its_own_guarantee`: for a received CN certificate, **no entry
  of any ledger bears weight for the guarantee the Bridge asserts**. The reason is
  structural — `Bridge.ofCN` takes `ModifiesOnly f F` *unconditionally*, so `Frame f F`
  holds in every world and there is none left in which to fail. This is the CN analogue
  of `pureProg_admits_no_other_minimal`, and it says the ledger `ofCN` carries is
  decoration with respect to its own contraction.

  That is not an argument against carrying it. The ledger is a claim about whether CN's
  word should have been taken at all, which is a different proposition from the
  contraction — and the fix is to make the reception depend on it.

  ── The fix ──
  `Bridge.ofReleaseL` is the one constructor in this repo whose ledger already has
  teeth: it takes a *conditional* certificate and demands `Sat Γ`, so the base cannot be
  minted without being discharged. `Bridge.ofCNComputed` is that shape for CN, with the
  base **computed** rather than declared: the reception hypothesis is
  `CondModifiesOnly f F (T.needs pf)`, and `T.needs pf` is what the resulting Bridge
  carries, by construction rather than by convention.

  ── The payoff ──
  `cn_computed_reception_exists_where_fixed_does_not` upgrades
  `cn_base_strictly_smaller` from a statement about `Sat` to a statement about
  *artifacts*: there is a world in which the computed reception can be built and a
  fixed-base one cannot. The reduction from three entries to two is the difference
  between having a certificate and not having one.

  ── Scope, stated before the theorems ──
  Whether CN's *own* base is minimal — whether `cerberus` and `vcgen` both bear weight
  for `ModifiesOnly` — is **not** provable here and deliberately so. It would require
  formalizing CN's type system, which is CN's soundness theorem and not ours to restate;
  `CNReceive.lean` draws exactly this line and this module stays on the same side of it.
  What is proved here is that the *mechanism* now carries the computed base, and that a
  reception which ignores it cannot have a minimal one.
-/
import ConfTyping.CNReceive
import ConfTyping.LoadBearing

namespace ConfTyping

open TransportCalculus

/-! ## The diagnosis: an unconditional reception cannot have a minimal base -/

/-- **No entry of any ledger bears weight for a received CN certificate's own
    guarantee.** `Bridge.ofCN` takes `ModifiesOnly` outright, so `Frame` holds in every
    world; `no_entry_bears_of_unconditional` does the rest. -/
theorem ofCN_ledger_inert_for_its_own_guarantee
    {f : CStore → CStore} {F : Footprint} (h : ModifiesOnly f F)
    (mkΓ : CNTrust → Ledger) (i : Nat) :
    ¬ LoadBearingAt mkΓ (fun _ => Frame f F) i :=
  no_entry_bears_of_unconditional (fun _ => cn_frame_rule h) mkΓ i

/-- So no nonempty base attached to such a reception is minimal — the CN analogue of
    `pureProg_admits_no_other_minimal`, and the precise sense in which the ledger
    `Bridge.ofCN` carries is decoration. -/
theorem ofCN_admits_no_minimal_nonempty_base
    {f : CStore → CStore} {F : Footprint} (h : ModifiesOnly f F)
    (mkΓ : CNTrust → Ledger) (n : Nat) (hn : 0 < n) :
    ¬ Minimal mkΓ (fun _ => Frame f F) n :=
  fun hm => ofCN_ledger_inert_for_its_own_guarantee h mkΓ 0 (hm.2 0 hn)

/-- And the cause, spelled out: the ledger is not read when the Bridge is built. Two
    receptions of the same artifact with *different* bases are the same certified map,
    so nothing about the guarantee distinguishes an honest ledger from an empty one. -/
theorem ofCN_ignores_its_ledger
    (f : CStore → CStore) (F : Footprint) (Γ₁ Γ₂ : Ledger) (h : ModifiesOnly f F) :
    (Bridge.ofCN f F Γ₁ h).map = (Bridge.ofCN f F Γ₂ h).map
  ∧ (Bridge.ofCN f F Γ₁ h).cert.1 = (Bridge.ofCN f F Γ₂ h).cert.1 :=
  ⟨rfl, rfl⟩

/-! ## The fix: a conditional reception whose base is computed -/

/-- CN's ownership clause **relative to a trusted base** — `CondBoundary`'s shape,
    applied to the reception rather than to a program of ours. -/
def CondModifiesOnly (f : CStore → CStore) (F : Footprint) (Γ : Ledger) : Prop :=
  Sat Γ → ModifiesOnly f F

/-- **The reception with teeth.** The base is `T.needs pf` — computed from the proof's
    own features, not supplied — and the Bridge cannot be minted without discharging it.
    `Bridge.ofReleaseL` is the same discipline for a component of ours. -/
def Bridge.ofCNComputed (T : CNTrust) (pf : CNProof)
    (f : CStore → CStore) (F : Footprint)
    (h : CondModifiesOnly f F (T.needs pf)) (hsat : Sat (T.needs pf)) :
    Bridge CStore (Footprint × Ledger) Footprint cnGA cdist :=
  Bridge.ofCN f F (T.needs pf) (h hsat)

/-- **The carried base is the computed base, by construction.** This is the equation
    that did not exist: `CNTrust.needs` now has a call site, and it is the one that
    matters. -/
theorem ofCNComputed_carries_needs (T : CNTrust) (pf : CNProof)
    (f : CStore → CStore) (F : Footprint)
    (h : CondModifiesOnly f F (T.needs pf)) (hsat : Sat (T.needs pf)) :
    (Bridge.ofCNComputed T pf f F h hsat).cert.2 = T.needs pf := rfl

/-- And the footprint half is untouched, so this is the same reception with the ledger
    tied down rather than a different one. -/
theorem ofCNComputed_same_footprint (T : CNTrust) (pf : CNProof)
    (f : CStore → CStore) (F : Footprint)
    (h : CondModifiesOnly f F (T.needs pf)) (hsat : Sat (T.needs pf)) :
    (Bridge.ofCNComputed T pf f F h hsat).cert.1 = F
  ∧ (Bridge.ofCNComputed T pf f F h hsat).map = f := ⟨rfl, rfl⟩

/-- **Composition accumulates computed bases.** `cn_comp_ledger` said the composite's
    ledger is the append; now both sides of that append are things a tool computed
    rather than things a caller asserted. -/
theorem ofCNComputed_comp_ledger (T : CNTrust) (pf₁ pf₂ : CNProof)
    (f g : CStore → CStore) (F G : Footprint)
    (h₁ : CondModifiesOnly f F (T.needs pf₁)) (hs₁ : Sat (T.needs pf₁))
    (h₂ : CondModifiesOnly g G (T.needs pf₂)) (hs₂ : Sat (T.needs pf₂)) :
    ((Bridge.ofCNComputed T pf₂ g G h₂ hs₂).comp
      (Bridge.ofCNComputed T pf₁ f F h₁ hs₁)).cert.2 = T.needs pf₂ ++ T.needs pf₁ := rfl

/-! ## The payoff: the reduction is the difference between having a certificate and not

`cn_base_strictly_smaller` exhibits a world where the computed base holds and the fixed
one does not. With the reception tied to its base, that becomes a statement about
whether the artifact exists. -/

/-- The world from `cn_base_strictly_smaller`: an unsound solver, everything else fine. -/
def unsoundSolver : CNTrust :=
  { cerberus := True, vcgen := True, smt := False, trusted := fun _ => True }

theorem unsoundSolver_satisfies_computed : Sat (unsoundSolver.needs frameOnlyProof) := by
  simp [CNTrust.needs, frameOnlyProof, Sat, unsoundSolver]

theorem unsoundSolver_fails_fixed : ¬ Sat unsoundSolver.fixedBase := by
  rintro ⟨-, -, h, -⟩
  exact h

/-- **A CN reception really can be built where a fixed-base one cannot.** The frame-only
    proof never called the solver, so its computed base is satisfied in a world where the
    solver is unsound — and the Bridge exists there, carrying that base and certifying a
    concrete artifact. A reception demanding `fixedBase` could not be minted at all,
    because `Sat unsoundSolver.fixedBase` is false.

    That is `cn_base_strictly_smaller` promoted from a fact about lists of propositions
    to a fact about certified morphisms. -/
theorem cn_computed_reception_exists_where_fixed_does_not :
    (∃ b : Bridge CStore (Footprint × Ledger) Footprint cnGA cdist,
        b.cert.2 = unsoundSolver.needs frameOnlyProof
      ∧ b.cert.1 = (fun l => l = 1)
      ∧ b.map = incrAt 1)
  ∧ ¬ Sat unsoundSolver.fixedBase :=
  ⟨⟨Bridge.ofCNComputed unsoundSolver frameOnlyProof (incrAt 1) (fun l => l = 1)
      (fun _ => incrAt_modifies 1) unsoundSolver_satisfies_computed,
    rfl, rfl, rfl⟩,
   unsoundSolver_fails_fixed⟩

/-- Non-vacuity, in the shape `cn_arith_charges_smt` already uses: a proof that *did*
    call the solver is charged for it, so the world above stops being available and the
    saving is a property of the proof rather than of the accounting. -/
theorem arith_proof_is_not_mintable_here :
    ¬ Sat (unsoundSolver.needs { usesArith := true, trustedSpecs := [] }) := by
  rintro ⟨-, -, h, -⟩
  exact h

/-! ## What this closes, and what it does not

    **Closes.** `CNTrust.needs` has a call site, and it is the reception itself. The base
    a CN Bridge carries is now computed from the proof rather than passed in, cannot be
    minted without discharge, and accumulates under `Bridge.comp` as before
    (`ofCNComputed_comp_ledger`). The three-to-two reduction is a statement about which
    certified morphisms exist.

    **Does not close.** Whether `[cerberus, vcgen]` is *minimal* for `ModifiesOnly` is
    not proved and cannot be from inside this repo — it is a question about CN's own
    soundness theorem, and `CNReceive.lean`'s division of labour puts it on CN's side.
    `ofCN_ledger_inert_for_its_own_guarantee` shows the *unconditional* reception can
    never have a minimal base; the conditional one at least *can*, and demonstrating
    that it does would need a reception whose hypothesis genuinely fails when an entry
    is dropped — which is CN's soundness, stated the other way round.

    **Not retrofitted.** `Bridge.ofCN` is left in place and `HeteroCompose.clear5CN`
    still uses it. Stage C's results rest on the unconditional form and rewriting them
    would hide that the gap was found rather than designed around — the same reason
    `HeteroCompose` keeps `sctGA` after `JasminSCT` superseded it. -/

end ConfTyping
