/-
  The composable core, stage 1e: a fourth component, and the test of whether the
  bundle scales.

  Stages 1a–1d got one program to carry three certificates composing by three laws:
  budgets add, authorization sets thread, noninterference is conjunctive. Three is
  suggestive. The design claim — `Bridge.pair_comp_cert`'s "no interaction term", so
  `n` guarantees cost `n` independent accumulations — is only tested by adding a
  fourth and seeing whether it slots in or forces rework.

  It slots in, and the fourth is not decoration: it is **the trusted base**, brick 4's
  ledger, lifted to the bundle. Accumulation is list append — a fourth genuinely
  different monoid after `+`, Hoare threading and conjunction — and `UCertL.seq` is
  four lines, which is the evidence the mechanism scales.

  The payload is a debt the map has been carrying in prose. Brick 35 split row 7 into
  *mediation* (generated) and *policy correctness* (CARRIED, because
  `policy_correctness_not_witnessed` shows no program can decide it). The bundle's
  mediation certificate says "every read is π-permitted" — which is only a **security**
  statement if π is the policy the specification intended. That gap was a paragraph.
  Here it becomes a typed obligation that composes:

  * `handler_intended_reads` — *given* the ledger entry, the handler reads only what
    the specification intends. The security reading, discharged from an assumption;
  * `handler_needs_the_policy_assumption` — and the entry is load-bearing: drop it and
    the same program, unchanged and still fully certified, reads something unintended.

  So the CARRIED half of row 7 is no longer a caveat in prose; it is an entry in a
  ledger that appends under composition and cannot be silently discharged — which is
  the discipline the whole repo is named for, finally applied to its own bundle.
-/
import ConfTyping.UnifiedNI
import ConfTyping.Ledger

namespace ConfTyping

/-! ## The bundle, relative to a trusted base -/

/-- A bundled certificate **relative to a ledger**: the budget, the authorization
    triple and everything else hold *given* the assumptions in `Γ`. Brick 4's
    `CondBoundary` shape, applied to the bundle. -/
def UCertL (Γ : Ledger) (A : List String) (c : UCmd) (A' : List String) (k : Nat) : Prop :=
  Sat Γ → UCert A c A' k

/-- **The fourth accumulation law.** Composing bundles unions their trusted bases:
    budgets add, authorization sets thread, and ledgers **append**. Four laws, one
    composition, and no term in which any two of them interact — the concrete test of
    `Bridge.pair_comp_cert`'s claim that carrying `n` guarantees costs `n`
    independent accumulations. -/
theorem UCertL.seq {Γ₁ Γ₂ : Ledger} {A A₁ A₂ : List String} {c₁ c₂ : UCmd} {k₁ k₂ : Nat}
    (h₁ : UCertL Γ₁ A c₁ A₁ k₁) (h₂ : UCertL Γ₂ A₁ c₂ A₂ k₂) :
    UCertL (Γ₁ ++ Γ₂) A (.seq c₁ c₂) A₂ (costGA.mul k₁ k₂) := by
  intro hsat
  rw [sat_append] at hsat
  exact UCert.seq (h₁ hsat.1) (h₂ hsat.2)

/-- The empty ledger is exactly the unconditional bundle — so every certificate
    proved in stages 1c/1d is a `UCertL` with nothing assumed. -/
theorem UCertL.nil {A A' : List String} {c : UCmd} {k : Nat} :
    UCertL [] A c A' k ↔ UCert A c A' k :=
  ⟨fun h => h trivial, fun h _ => h⟩

/-- Discharge is explicit: to drop the ledger you must prove it. -/
theorem UCertL.discharge {Γ : Ledger} {A A' : List String} {c : UCmd} {k : Nat}
    (h : UCertL Γ A c A' k) (hsat : Sat Γ) : UCert A c A' k := h hsat

/-! ## The debt row 7 was carrying

    The mediation certificate says every read is **π-permitted**. That is a security
    statement only if `π` is the policy the specification intended — and brick 35
    proved no program can witness that. Here the gap is a ledger entry. -/

/-- The external, program-invisible assumption: the deployed policy grants exactly
    what the specification intends. -/
def PolicyIntended (π intended : MedPolicy) : Prop := ∀ r, π r = intended r

/-- **With the assumption, the security reading.** Given the ledger entry, the
    handler reads only what the *specification* intends — not merely what the
    deployed policy happens to permit. -/
theorem handler_intended_reads (π intended : MedPolicy)
    (hsat : Sat [PolicyIntended π intended]) :
    ∀ (n : Nat) (σ : Store) (r : UState × Nat × List Bool),
      uexec n handler π (initU σ) = some r → ∀ x ∈ r.1.reads, intended x = true := by
  intro n σ r hr x hx
  have hpi : PolicyIntended π intended := hsat.1
  have := handler_mediated n π σ r hr x hx
  rw [hpi x] at this
  exact this

/-- **And the assumption is load-bearing.** With a permissive deployed policy and a
    restrictive specification, the very same program — unchanged, still passing every
    check, still carrying all three certificates — reads a resource the specification
    does not intend. So the entry cannot be dropped: the bundle's mediation
    certificate is *not* by itself a statement about the intended policy. -/
theorem handler_needs_the_policy_assumption :
    ¬ PolicyIntended (fun _ => true) (fun _ => false)
  ∧ ((uexec 12 handler (fun _ => true) (initU (fun _ => 0))).map (fun r => r.1.reads))
      = some ["log", "db"]
  ∧ (fun (_ : String) => false) "db" = false := by
  refine ⟨?_, by decide, by decide⟩
  intro h
  exact absurd (h "db") (by decide)

/-- **Row 7's CARRIED half, now typed.** The handler's guarantee is unconditional as
    a statement about `π`, and conditional — on one explicit, appendable,
    non-dischargeable ledger entry — as a statement about the intended policy. That
    is precisely what "CARRIED" was asserting in prose. -/
theorem row7_carried_is_a_ledger_entry :
    (∀ π σ n r, uexec n handler π (initU σ) = some r → ∀ x ∈ r.1.reads, π x = true)
  ∧ (∀ π intended, Sat [PolicyIntended π intended] →
       ∀ n σ r, uexec n handler π (initU σ) = some r →
         ∀ x ∈ r.1.reads, intended x = true)
  ∧ ¬ PolicyIntended (fun _ => true) (fun _ => false) :=
  ⟨fun π σ n r hr x hx => handler_mediated n π σ r hr x hx,
   fun π intended hsat n σ r hr x hx => handler_intended_reads π intended hsat n σ r hr x hx,
   handler_needs_the_policy_assumption.1⟩

/-! ## Four laws, one composition -/

/-- **The scaling test, stated.** One `seq` advances four certificates by four
    different laws — budget by `+`, authorization by threading, ledger by `++`, and
    (from stage 1d, conjunctively) noninterference — with no interaction term
    anywhere. Adding the fourth cost one four-line lemma; that is the evidence the
    bundle mechanism scales rather than merely reaching three. -/
theorem four_laws_one_composition
    {Γ₁ Γ₂ : Ledger} {A A₁ A₂ : List String} {c₁ c₂ : UCmd} {k₁ k₂ : Nat}
    {P : Partition}
    (h₁ : UCertL Γ₁ A c₁ A₁ k₁) (h₂ : UCertL Γ₂ A₁ c₂ A₂ k₂)
    (n₁ : USecTy P c₁) (n₂ : USecTy P c₂) :
    UCertL (Γ₁ ++ Γ₂) A (.seq c₁ c₂) A₂ (k₁ + k₂) ∧ USecTy P (.seq c₁ c₂) :=
  ⟨UCertL.seq h₁ h₂, .seq n₁ n₂⟩

end ConfTyping
