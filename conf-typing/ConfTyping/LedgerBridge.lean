/-
  The ledger rides the interface — brick 4, session 2.

  The trusted base of session 1 accumulates by the *same* composition law as
  every other certificate in the repo. `ledgerGA` is the flow `GradedAction`
  with a **phantom ledger grade**: the certificate is `(Mono QD qle × Ledger)`,
  `mul` composes the flow transform *and appends the ledgers*, and `act`
  ignores the ledger (`ledger_act_phantom`) — so the flow behaviour is exactly
  `flowGA`'s while `Bridge.comp` threads the trusted base for free
  (`ledgerBridge_comp_ledger`, `rfl`).

  A component becomes a ledger-Bridge two ways: exactly (`Bridge.ofComponentL`)
  or via a *discharged* conditional certificate (`Bridge.ofReleaseL`, which
  demands `Sat Γ` — you cannot mint the Bridge without discharging the base you
  carry). Composing them yields the supply-chain audit trail: the composite's
  ledger is the union of the parts' (`ledger_supply_chain_ledger`), its map is
  the composite boundary (`ledger_supply_chain_map`), and its flow certificate
  is dominated by the brick-2 seam certificate (`ledger_supply_chain_bound`) —
  provenance and guarantee composed by one law. The SBOM as a theorem.
-/
import ConfTyping.Ledger

namespace ConfTyping

open TransportCalculus

/-! ## The phantom-ledger graded action -/

/-- The flow interface with a phantom ledger grade: certificates are
    `(flow transform, trusted base)`; `mul` composes the transform and
    **appends** the base; `act` ignores the base (it is provenance, not a
    contraction). A valid `GradedAction` — `act_mul` is `rfl` (the ledger
    is inert in the action, the flow part is `Mono.comp`). -/
def ledgerGA : GradedAction (Mono QD qle × Ledger) QD where
  mul      := fun a b => (a.1.comp b.1, a.2 ++ b.2)
  le       := qle
  act      := fun a d => a.1.toFun d
  le_trans := qleT
  act_mul  := fun _ _ _ => rfl
  act_mono := fun a {_ _} h => a.1.mono h

/-- **The ledger is phantom in the action.** Flow behaviour is exactly
    `flowGA`'s; the ledger rides alongside as provenance. -/
theorem ledger_act_phantom (m : Mono QD qle) (Γ : Ledger) (d : QD) :
    ledgerGA.act (m, Γ) d = flowGA.act m d := rfl

/-- **`Bridge.comp` appends the trusted base** — assumptions accumulate by the
    same law that composes the flow certificate (and Lipschitz constants, and
    Dobrushin coefficients). -/
theorem ledgerBridge_comp_ledger
    (g f : Bridge Store (Mono QD qle × Ledger) QD ledgerGA qd) :
    (g.comp f).cert.2 = g.cert.2 ++ f.cert.2 := rfl

/-- And the flow part composes as before. -/
theorem ledgerBridge_comp_flow
    (g f : Bridge Store (Mono QD qle × Ledger) QD ledgerGA qd) :
    (g.comp f).cert.1 = g.cert.1.comp f.cert.1 := rfl

/-! ## Components as ledger-Bridges -/

/-- The exact ledger-Bridge: the component's pull-back transform, carrying a
    declared trusted base `Γ`. -/
def Bridge.ofComponentL (c : Cmd) (Γ : Ledger) :
    Bridge Store (Mono QD qle × Ledger) QD ledgerGA qd where
  map       := evalStore c
  cert      := (pull (evalStore c), Γ)
  contracts := fun _ _ _ hq => hq

/-- **A discharged conditional certificate is a ledger-Bridge.** Building it
    *requires* `Sat Γ` — you cannot mint a certified Bridge for a component
    without discharging the trusted base it carries — and the ledger `Γ` rides
    along as the audit trail of what was assumed. -/
def Bridge.ofReleaseL {c : Cmd} {P : Partition} {φ : Release} {Γ : Ledger}
    (h : CondReleases c P Γ φ) (hsat : Sat Γ) :
    Bridge Store (Mono QD qle × Ledger) QD ledgerGA qd where
  map       := evalStore c
  cert      := (leakBound P φ, Γ)
  contracts := fun σ σ' => (bridge_iff_releases c P φ).mpr (h hsat) σ σ'

/-! ## The supply-chain composition: provenance accumulates with the guarantee -/

/-- **The composite's trusted base is the union.** Composing a downstream
    released component (base `Γ₂`) with an upstream exact component (base `Γ₁`)
    yields a Bridge whose ledger is `Γ₂ ++ Γ₁` — the automatic SBOM, computed
    by `Bridge.comp`. -/
theorem ledger_supply_chain_ledger
    {c₁ c₂ : Cmd} {P : Partition} {φ₂ : Release} {Γ₁ Γ₂ : Ledger}
    (h₂ : CondReleases c₂ P Γ₂ φ₂) (hs₂ : Sat Γ₂) :
    ((Bridge.ofReleaseL h₂ hs₂).comp (Bridge.ofComponentL c₁ Γ₁)).cert.2
      = Γ₂ ++ Γ₁ := rfl

/-- The composite's map is the composite boundary map. -/
theorem ledger_supply_chain_map
    {c₁ c₂ : Cmd} {P : Partition} {φ₂ : Release} {Γ₁ Γ₂ : Ledger}
    (h₂ : CondReleases c₂ P Γ₂ φ₂) (hs₂ : Sat Γ₂) :
    ((Bridge.ofReleaseL h₂ hs₂).comp (Bridge.ofComponentL c₁ Γ₁)).map
      = evalStore (.seq c₁ c₂) := by
  funext σ; rfl

/-- **The composite's flow certificate is the seam certificate.** The ledger
    is phantom in the action, so the flow content is exactly `FlowBridge`'s:
    given `c₁`'s own release certificate, the composite ledger-Bridge's flow
    transform is dominated on every realized distance by the brick-2 seam
    certificate. Provenance (the ledger) and guarantee (the seam bound) are
    composed by one law — the audit trail and the security proof are the same
    `Bridge.comp`. -/
theorem ledger_supply_chain_bound
    {c₁ c₂ : Cmd} {P : Partition} {φ₁ φ₂ : Release} {Γ₁ Γ₂ : Ledger}
    (h₁ : BoundaryReleases c₁ P φ₁)
    (h₂ : CondReleases c₂ P Γ₂ φ₂) (hs₂ : Sat Γ₂) :
    ∀ σ σ', qle
      ((((Bridge.ofReleaseL h₂ hs₂).comp
          (Bridge.ofComponentL c₁ Γ₁)).cert.1).toFun (qd σ σ'))
      ((leakBound P (seqRelease c₁ φ₁ φ₂)).toFun (qd σ σ')) :=
  comp_reconstructs_seq_release h₁ (h₂ hs₂)

end ConfTyping
