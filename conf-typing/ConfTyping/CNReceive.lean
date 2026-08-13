/-
  Stage B — receiving a *foreign* certificate: CN's ownership footprint.

  Every `Bridge` in this repo so far has certified something this repo also
  *proved*: our `Cmd`, our `evalStore`, our typing judgement. This module does
  the opposite, and that is the whole point of stage B. It takes a guarantee
  produced by **CN** — a real separation-logic refinement-type verifier for real
  C, built on the Cerberus C semantics (Pulte, Makwana, Sewell, Memarian,
  Sewell, Krishnaswami, POPL 2023) — and *receives* it, exactly as
  `Bridge.ofKernel` receives a Dobrushin coefficient and `Bridge.ofPTPChannel`
  receives a quantum channel's contractivity. Nothing here re-verifies any C.

  ── What CN asserts, and which part of it we take ──
  A CN function spec names the memory the function owns:

      void incr_first (unsigned int *p, unsigned int *q)
      /*@ requires take pv = RW<unsigned int>(p);
          ensures take pv_ = RW<unsigned int>(p);
                  pv_ == pv + 1u32;
      @*/

  Two different things are asserted, and they have different characters:

  * the **functional** part (`pv_ == pv + 1u32`) — what the value becomes;
  * the **ownership** part (`take pv = RW<unsigned int>(p)`, and *only* `p`) —
    which memory may be touched at all.

  The ownership part is the one that composes, and it is the one modelled here.
  Its observable content is a **modifies clause**: a function that owns only `p`
  leaves everything else exactly as it found it. That is not our reading imposed
  on CN — it is a rule CN itself applies, and the tutorial has it as a worked
  example (`bcp_framerule.c`, transcribed in `corpus/cn/SOURCES.md`):

      void incr_first_frame (unsigned int *p, unsigned int *q)
      /*@ requires take pv = RW<unsigned int>(p);
                   take qv = RW<unsigned int>(q);
          ensures  ... qv_ == qv; @*/
      { incr_first(p, q); }

  `qv_ == qv` is *derived by the frame rule*, not proved in the body. `Frame`
  below is that conclusion, `ModifiesOnly` is the hypothesis it comes from, and
  `cn_frame_rule` is the implication — the frame rule, at our altitude.

  ── The honest statement of what is and is not machine-checked ──
  **The encoding step is by hand and is not checked against CN's implementation.**
  We do not parse CN's output, and we do not prove that `take RW<unsigned int>(p)`
  *implies* `ModifiesOnly f {p}` — that would require formalizing CN's type
  system, which is CN's own soundness theorem and not ours to restate. What is
  machine-checked is everything downstream of the reception: that the guarantee,
  once stated, is an instance of the interface (`cnGA`), that composing two
  receptions accumulates footprints by union and trusted bases by append with no
  interaction term, and that the composite's frame conclusion follows. This is
  the same division of labour as `Bridge.ofKernel`, which takes its Dobrushin
  coefficient as a hypothesis rather than deriving it.

  ── The trusted base is *computed*, not fixed ──
  Every CN result rests on Cerberus's C semantics, CN's refinement type system,
  and an SMT backend — a fixed three-entry base (`CNTrust.fixedBase`). But not
  every CN result rests on all three: CN's type system is engineered so that its
  obligations land in a decidable SMT fragment, and a function whose obligations
  are *purely structural* — ownership moved around, nothing arithmetic asserted —
  never asks the solver anything. `CNTrust.needs` reads the base off the proof's
  own features, and `cn_base_strictly_smaller` exhibits a world where the solver
  is unsound and the frame certificate stands anyway. That is stage 2c's `needs`
  argument, carried across to a foreign tool.
-/
import ConfTyping.Ledger
import TransportCalculus

namespace ConfTyping

open TransportCalculus

/-! ## The C state, abstracted to what a modifies clause can see -/

/-- A location. Deliberately abstract: the footprint algebra never inspects it,
    and nothing below depends on `Nat`'s structure. -/
abbrev CLoc := Nat

/-- A C store, abstracted to a total map. This is *not* a C memory model — it is
    the coarsest thing on which "this function did not touch that location" is
    even statable, which is all the ownership certificate needs. The gap between
    this and Cerberus's actual memory object model is a reception assumption,
    named in the module header. -/
abbrev CStore := CLoc → Nat

/-- A **footprint**: the set of locations a CN spec gives the function ownership
    of. A predicate rather than a list, so that union is disjunction and no
    finiteness or decidability sneaks in. -/
abbrev Footprint := CLoc → Prop

/-! ## What CN's ownership clause asserts

The two forms, and the frame rule between them. -/

/-- **The modifies clause.** The function writes nothing outside `F`. This is
    the direct reading of `take pv = RW<unsigned int>(p)` naming `p` and nothing
    else, and it is what we receive from CN. -/
def ModifiesOnly (f : CStore → CStore) (F : Footprint) : Prop :=
  ∀ (σ : CStore) (l : CLoc), ¬ F l → f σ l = σ l

/-- **The frame conclusion**, in the relational form the interface needs: two
    runs that agree outside `F` still agree outside `F` afterwards. -/
def Frame (f : CStore → CStore) (F : Footprint) : Prop :=
  ∀ (σ τ : CStore) (l : CLoc), ¬ F l → σ l = τ l → f σ l = f τ l

/-- **The frame rule.** Owning only `F` implies framing off `F`. `incr_first`
    owns only `p`, so `incr_first_frame` gets `qv_ == qv` for free — the C
    example in the header is this implication, applied once. -/
theorem cn_frame_rule {f : CStore → CStore} {F : Footprint}
    (h : ModifiesOnly f F) : Frame f F := by
  intro σ τ l hF hστ
  rw [h σ l hF, h τ l hF, hστ]

/-! ## The graded action: footprints accumulate by union, the ledger rides along

The grade is a **pair** — the footprint and the trusted base — in exactly the
shape `ledgerGA` established: `mul` composes both components, and `act` ignores
the ledger, so provenance accumulates by the same law as the guarantee without
perturbing it (`cn_act_phantom`). -/

/-- The distance: the set of locations at which two stores differ. -/
def cdist (σ τ : CStore) : Footprint := fun l => σ l ≠ τ l

/-- Footprint containment, the order on distances. -/
def fsub (d d' : Footprint) : Prop := ∀ l, d l → d' l

/-- **The CN graded action.** Grades are `(footprint, trusted base)`; grade
    composition is `(union, append)`; the action of a grade on a difference set
    adds the footprint to it. `act_mul` is associativity of `∨`, which is the
    entire reason footprints compose without an interaction term. -/
def cnGA : GradedAction (Footprint × Ledger) Footprint where
  mul      := fun a b => (fun l => a.1 l ∨ b.1 l, a.2 ++ b.2)
  le       := fsub
  act      := fun a d => fun l => a.1 l ∨ d l
  le_trans := fun h₁ h₂ l ha => h₂ l (h₁ l ha)
  act_mul  := fun _ _ _ => by funext l; exact propext or_assoc
  act_mono := by
    intro m d d' h l hl
    rcases hl with hF | hd
    · exact Or.inl hF
    · exact Or.inr (h l hd)

/-- The ledger is inert in the action: it is provenance, not a guarantee. -/
theorem cn_act_phantom (F : Footprint) (Γ : Ledger) (d : Footprint) :
    cnGA.act (F, Γ) d = fun l => F l ∨ d l := rfl

/-! ## The reception -/

/-- **Receiving a CN certificate.** Given CN's ownership clause for `f` — as a
    hypothesis, not as something proved here — and the trusted base that
    verification rested on, `f` becomes a certified bridge whose grade is
    `(footprint, base)`.

    The hypothesis `h` is the reception point, and it is where CN's word is
    taken. Everything after this line is checked. -/
def Bridge.ofCN (f : CStore → CStore) (F : Footprint) (Γ : Ledger)
    (h : ModifiesOnly f F) :
    Bridge CStore (Footprint × Ledger) Footprint cnGA cdist where
  map       := f
  cert      := (F, Γ)
  contracts := fun σ τ l hne => by
    by_cases hF : F l
    · exact Or.inl hF
    · exact Or.inr fun hστ => hne (cn_frame_rule h σ τ l hF hστ)

/-! ## The milestone: two receptions compose, componentwise

`CN certifies f, CN certifies g, therefore the composite carries both
guarantees with trusted base = ledger(f) ∪ ledger(g)`. Both halves are `rfl`:
the accumulation is `Bridge.comp`'s, not a new proof. -/

/-- **The footprint of the composite is the union of the footprints.** -/
theorem cn_comp_footprint
    (f g : CStore → CStore) (F G : Footprint) (Γf Γg : Ledger)
    (hf : ModifiesOnly f F) (hg : ModifiesOnly g G) :
    ((Bridge.ofCN g G Γg hg).comp (Bridge.ofCN f F Γf hf)).cert.1
      = fun l => G l ∨ F l := rfl

/-- **The trusted base of the composite is the union of the trusted bases.**
    This is the stage-B milestone sentence, machine-checked. -/
theorem cn_comp_ledger
    (f g : CStore → CStore) (F G : Footprint) (Γf Γg : Ledger)
    (hf : ModifiesOnly f F) (hg : ModifiesOnly g G) :
    ((Bridge.ofCN g G Γg hg).comp (Bridge.ofCN f F Γf hf)).cert.2 = Γg ++ Γf := rfl

/-- The composite's map is the composite function — the guarantee is about the
    artifact one actually gets by calling `f` then `g`. -/
theorem cn_comp_map
    (f g : CStore → CStore) (F G : Footprint) (Γf Γg : Ledger)
    (hf : ModifiesOnly f F) (hg : ModifiesOnly g G) :
    ((Bridge.ofCN g G Γg hg).comp (Bridge.ofCN f F Γf hf)).map = g ∘ f := rfl

/-- **The algebra computes the semantically right footprint.** `Bridge.comp`
    said the composite's grade is the union; here is the independent proof that
    the union really is a modifies clause for `g ∘ f`. The two agree, so the
    grade is not bookkeeping — it is the property. -/
theorem modifiesOnly_comp {f g : CStore → CStore} {F G : Footprint}
    (hf : ModifiesOnly f F) (hg : ModifiesOnly g G) :
    ModifiesOnly (g ∘ f) (fun l => G l ∨ F l) := by
  intro σ l hl
  have hG : ¬ G l := fun h => hl (Or.inl h)
  have hF : ¬ F l := fun h => hl (Or.inr h)
  show g (f σ) l = σ l
  rw [hg (f σ) l hG, hf σ l hF]

/-! ## Non-vacuity I: the composite footprint is *strictly* smaller than "everything"

A modifies clause that admits every location is free and says nothing. The
content of the reception is the locations it *excludes* — which is exactly what
`incr_first_frame` uses. -/

/-- The C example, modelled: increment through a pointer, owning that location
    and nothing else. -/
def incrAt (a : CLoc) : CStore → CStore :=
  fun σ l => if l = a then σ a + 1 else σ l

theorem incrAt_modifies (a : CLoc) : ModifiesOnly (incrAt a) (fun l => l = a) := by
  intro σ l hl
  simp only [incrAt, if_neg hl]

/-- **`qv_ == qv`, derived.** Composing the receptions of `incr_first(p,·)` and
    an increment through `q`, every location outside `{p, q}` is left exactly as
    it was — and the proof is the composed certificate, not a fresh argument
    about the bodies. This is the frame rule of `bcp_framerule.c`, obtained from
    the algebra. -/
theorem cn_untouched_outside (p q : CLoc) (σ : CStore) (l : CLoc)
    (hp : l ≠ p) (hq : l ≠ q) :
    (incrAt q ∘ incrAt p) σ l = σ l :=
  modifiesOnly_comp (incrAt_modifies p) (incrAt_modifies q) σ l
    (fun h => h.elim hq hp)

/-- And the exclusion is real: the composite footprint is *not* everything. -/
theorem cn_footprint_not_total :
    ¬ (∀ l : CLoc, (fun l => l = 1 ∨ l = 0) l) := by
  intro h
  rcases h 2 with h' | h' <;> exact absurd h' (by decide)

/-! ## Non-vacuity II: the trusted base is computed, and comes out strictly smaller

The three things every CN result rests on, and the observation that a given
result need not rest on all three. -/

/-- CN's trust assumptions, as propositions supplied from outside. They are
    parameters rather than axioms on purpose: this module asserts none of them,
    it only tracks which ones a certificate needs. -/
structure CNTrust where
  /-- Cerberus's C semantics models the C that the compiler actually implements. -/
  cerberus : Prop
  /-- CN's separation-logic refinement type system is sound. -/
  vcgen    : Prop
  /-- The SMT backend is sound on the decidable fragment CN targets. -/
  smt      : Prop
  /-- A spec CN was instructed to trust rather than check. -/
  trusted  : String → Prop

/-- What a particular CN run actually used. -/
structure CNProof where
  /-- Did any obligation go to the solver? Purely structural ownership
      reasoning — moving `take` resources around — does not. -/
  usesArith    : Bool
  /-- Specs assumed rather than verified. -/
  trustedSpecs : List String

/-- The base you must assume if you do *not* look at the proof: all three. -/
def CNTrust.fixedBase (T : CNTrust) : Ledger := [T.cerberus, T.vcgen, T.smt]

/-- **The base read off the proof.** Cerberus and the type system are
    unavoidable; the solver is charged only if the solver was asked; trusted
    specs are charged by name. -/
def CNTrust.needs (T : CNTrust) (pf : CNProof) : Ledger :=
  [T.cerberus, T.vcgen]
    ++ (if pf.usesArith then [T.smt] else [])
    ++ pf.trustedSpecs.map T.trusted

/-- The ownership half of `incr_first` — a modifies clause, discharged
    structurally. No arithmetic obligation, no trusted spec. -/
def frameOnlyProof : CNProof := { usesArith := false, trustedSpecs := [] }

/-- **The computed base is strictly smaller than the fixed one.** Witnessed in a
    world where the SMT backend is *unsound*: the frame certificate's computed
    base is still satisfied, while the fixed three-entry base is not. So the
    omission is earned rather than assumed — charging the solver to a proof that
    never called it would be a strictly weaker theorem. -/
theorem cn_base_strictly_smaller :
    ∃ T : CNTrust, Sat (T.needs frameOnlyProof) ∧ ¬ Sat T.fixedBase := by
  refine ⟨{ cerberus := True, vcgen := True, smt := False, trusted := fun _ => True }, ?_, ?_⟩
  · simp [CNTrust.needs, frameOnlyProof, Sat]
  · rintro ⟨-, -, h, -⟩
    exact h

/-- **And it survives composition.** Two frame-only CN results compose to a
    trusted base that still does not contain the solver — the union of two
    computed bases is not the fixed base. -/
theorem cn_comp_base_strictly_smaller :
    ∃ T : CNTrust,
      Sat (T.needs frameOnlyProof ++ T.needs frameOnlyProof) ∧ ¬ Sat T.fixedBase := by
  refine ⟨{ cerberus := True, vcgen := True, smt := False, trusted := fun _ => True }, ?_, ?_⟩
  · simp [CNTrust.needs, frameOnlyProof, Sat]
  · rintro ⟨-, -, h, -⟩
    exact h

/-- A run that *did* ask the solver is charged for it: the computed base then
    contains every entry of the fixed base. Nothing is being hidden — the
    saving in `cn_base_strictly_smaller` is a property of the proof, not of the
    accounting. -/
theorem cn_arith_charges_smt (T : CNTrust) (pf : CNProof) (h : pf.usesArith = true) :
    T.smt ∈ T.needs pf := by
  simp [CNTrust.needs, h]

/-! ## Teeth: a certificate that is not earned cannot be received

`Bridge.ofCN` demands `ModifiesOnly`. A function that writes outside its
declared footprint cannot produce that hypothesis, so no bridge exists for it —
the reception is not a formality. -/

/-- Increments through `q` while claiming to own only `p`. There is no
    reception for this: the declared footprint is a lie, and the hypothesis
    `Bridge.ofCN` requires is false. -/
theorem cn_false_footprint_unreceivable (p q : CLoc) (hpq : p ≠ q) :
    ¬ ModifiesOnly (incrAt q) (fun l => l = p) := by
  intro h
  have := h (fun _ => 0) q (fun hq => hpq hq.symm)
  simp [incrAt] at this

end ConfTyping
