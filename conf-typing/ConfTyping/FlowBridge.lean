/-
  The flow Bridge — brick 2, session 2: security composition received into the
  transport interface.

  The reception puts certified components into the *same* `GradedAction`
  interface that hosts Lipschitz maps, Hölder maps, Markov kernels, and
  quantum channels (`transport-calculus` / `transport-kernel`):

  * distance   = `qd`, the **query distance**: the set of observations
                 (`Query := Store → Val`) separating two stores — a
                 distinguishability "metric" valued in the lattice
                 `QD := Query → Prop` under pointwise implication;
  * map        = the component's boundary map `evalStore c`;
  * certificate = a monotone self-map of `QD` (the `universalGA` pattern —
                 the repo's Cayley form): either the **exact transform**
                 `pull (evalStore c)` (query precomposition — composes
                 definitionally), or the **leak bound** `leakBound P φ` —
                 "an output query separates only if it is non-Low, or a Low
                 input atom or the declared release already separated the
                 inputs."

  The reception is an equivalence (`bridge_iff_releases`): a component
  carries a `leakBound P φ`-certified Bridge **iff** `BoundaryReleases c P φ`
  — the security certificate and the transport certificate are the same
  thing. And the interface's generic composition reconstructs the seam
  theorem (`comp_reconstructs_seq_release`): composing the exact bridge of
  `c₁` with the certified bridge of `c₂` yields a certificate dominated by
  `leakBound P (seqRelease c₁ φ₁ φ₂)` — the composed release of
  `Compose.lean`, computed by `Bridge.comp`.

  A lossiness fact worth recording (prose, deliberate): composing two
  *abstraction* bridges (`leakBound φ₂ ∘ leakBound φ₁`) is sound but
  trivial — the second bound cannot know that `φ₂` is evaluated at the
  boundary. The informative composition threads the first component's *map*
  (`pull`), exactly as `seqRelease` threads `c₁` — the supply-chain moral:
  ship the boundary abstraction, not just the budget.
-/
import TransportCalculus
import ConfTyping.Compose

namespace ConfTyping

open TransportCalculus

/-! ## The query distance -/

/-- A query: any total observation of a store. (Typewise identical to
    `Release` — a release *is* a query one permits.) -/
abbrev Query := Store → Val

/-- The distance carrier: sets of queries, ordered by pointwise implication. -/
abbrev QD := Query → Prop

def qle (A B : QD) : Prop := ∀ q, A q → B q

/-- Transitivity, packaged with the implicit-binder shape `universalGA` and
    `Bridge.ofModulus` expect — defined once so every use is the same term. -/
def qleT : ∀ {a b c : QD}, qle a b → qle b c → qle a c :=
  fun h₁ h₂ q hq => h₂ q (h₁ q hq)

/-- **The query distance**: which queries separate two stores. -/
def qd (σ σ' : Store) : QD := fun q => q σ ≠ q σ'

/-- The flow instance of the transport interface: `universalGA` over the
    query-distance lattice. -/
def flowGA : GradedAction (Mono QD qle) QD := universalGA qle qleT

/-! ## The exact certificate: query precomposition -/

/-- The exact transform of a store map: pull queries back along it.
    Precomposition composes definitionally — this is the Cayley certificate. -/
def pull (v : Store → Store) : Mono QD qle where
  toFun := fun A q => A (fun σ => q (v σ))
  mono  := fun h _ hq => h _ hq

/-- **Any component is a Bridge, exactly.** The boundary map with its own
    pull-back transform: `contracts` holds definitionally (the queries
    separating the boundary are exactly the pulled-back queries separating
    the inputs). This is a `Bridge.ofModulus` instance written as a literal
    so the certificate projection is definitional. -/
def Bridge.ofComponent (c : Cmd) :
    Bridge Store (Mono QD qle) QD flowGA qd where
  map       := evalStore c
  cert      := pull (evalStore c)
  contracts := fun _ _ _ hq => hq

theorem ofComponent_cert (c : Cmd) :
    (Bridge.ofComponent c).cert = pull (evalStore c) := rfl

/-! ## The security certificate: the leak bound -/

/-- A Low query: a function of the Low part of the store alone. -/
def LowQuery (P : Partition) (q : Query) : Prop :=
  ∀ σ σ', lowEq P σ σ' → q σ = q σ'

/-- The atomic query reading one variable. -/
def atomQ (x : String) : Query := fun σ => .int (σ x)

theorem atomQ_low {P : Partition} {x : String} (hx : P x = false) :
    LowQuery P (atomQ x) :=
  fun _ _ h => congrArg Val.int (h x hx)

/-- **The leak bound** — the security certificate as a monotone transform of
    the query distance: an output query separates only if it is non-Low
    (unconstrained), or some Low input atom or the declared release `φ`
    already separated the inputs. -/
def leakBound (P : Partition) (φ : Release) : Mono QD qle where
  toFun := fun A q =>
    LowQuery P q → (∃ x, P x = false ∧ A (atomQ x)) ∨ A φ
  mono  := fun h _ hq hlow =>
    (hq hlow).imp (fun ⟨x, hx, ha⟩ => ⟨x, hx, h _ ha⟩) (h φ)

/-- If no Low atom separates two stores, they are Low-equivalent. -/
theorem lowEq_of_no_atom {P : Partition} {σ σ' : Store}
    (h : ¬ ∃ x, P x = false ∧ qd σ σ' (atomQ x)) : lowEq P σ σ' := by
  intro x hx
  by_cases he : σ x = σ' x
  · exact he
  · exact absurd ⟨x, hx, fun e => he (by injection e)⟩ h

/-- **The reception is an equivalence.** A component carries a
    `leakBound P φ`-certified Bridge (the `contracts` inequality at every
    pair) **iff** it satisfies `BoundaryReleases c P φ`: the security
    certificate and the transport certificate are the same datum. -/
theorem bridge_iff_releases (c : Cmd) (P : Partition) (φ : Release) :
    (∀ σ σ', qle (qd (evalStore c σ) (evalStore c σ'))
                 ((leakBound P φ).toFun (qd σ σ')))
      ↔ BoundaryReleases c P φ := by
  constructor
  · intro h σ σ' hle hφ x hx
    by_cases hne : evalStore c σ x = evalStore c σ' x
    · exact hne
    · exfalso
      have hsep : qd (evalStore c σ) (evalStore c σ') (atomQ x) :=
        fun e => hne (by injection e)
      rcases h σ σ' (atomQ x) hsep (atomQ_low hx) with ⟨y, hy, hqd⟩ | hqd
      · exact hqd (congrArg Val.int (hle y hy))
      · exact hqd hφ
  · intro h σ σ' q hq hlow
    by_cases hatom : ∃ x, P x = false ∧ qd σ σ' (atomQ x)
    · exact Or.inl hatom
    · by_cases hrel : qd σ σ' φ
      · exact Or.inr hrel
      · exfalso
        have hle : lowEq P σ σ' := lowEq_of_no_atom hatom
        have hφe : φ σ = φ σ' := by
          by_cases he : φ σ = φ σ'
          · exact he
          · exact absurd he hrel
        exact hq (hlow _ _ (h σ σ' hle hφe))

/-- **A certified component is a certified Bridge.** (Again an `ofModulus`
    instance, written as a literal.) -/
def Bridge.ofRelease {c : Cmd} {P : Partition} {φ : Release}
    (h : BoundaryReleases c P φ) :
    Bridge Store (Mono QD qle) QD flowGA qd where
  map       := evalStore c
  cert      := leakBound P φ
  contracts := fun σ σ' => (bridge_iff_releases c P φ).mpr h σ σ'

theorem ofRelease_cert {c : Cmd} {P : Partition} {φ : Release}
    (h : BoundaryReleases c P φ) :
    (Bridge.ofRelease h).cert = leakBound P φ := rfl

/-! ## The seam, reconstructed by the interface -/

/-- The seam theorem restated at the boundary granularity: the composite of
    two Policy-certified components is Policy-certified with the computed
    release — `releases_seq` through the boundary/channel equivalences. -/
theorem boundaryReleases_seq {c₁ c₂ : Cmd} {P : Partition} {φ₁ φ₂ : Release}
    (h₁ : BoundaryReleases c₁ P φ₁) (h₂ : BoundaryReleases c₂ P φ₂) :
    BoundaryReleases (.seq c₁ c₂) P (seqRelease c₁ φ₁ φ₂) :=
  (boundaryReleases_iff _ _ _).mpr
    (releases_seq h₁ ((boundaryReleases_iff _ _ _).mp h₂))

/-- The generic composition's map is the composite's boundary map. -/
theorem comp_map_is_seq (c₁ c₂ : Cmd) {P : Partition} {φ₂ : Release}
    (h₂ : BoundaryReleases c₂ P φ₂) :
    ((Bridge.ofRelease h₂).comp (Bridge.ofComponent c₁)).map
      = evalStore (.seq c₁ c₂) := by
  funext σ; rfl

/-- **`Bridge.comp` reconstructs the seam theorem.** Compose the exact bridge
    of `c₁` with the certified bridge of `c₂` by the *generic* composition
    law: the resulting certificate — `leakBound P φ₂ ∘ pull (evalStore c₁)`,
    computed by `Bridge.comp` with no security-specific reasoning — is
    dominated, on every realized distance, by the seam certificate
    `leakBound P (seqRelease c₁ φ₁ φ₂)` of `Compose.lean`, given `c₁`'s own
    certificate. Security composition **is** certificate accumulation in the
    same interface as Lipschitz, Dobrushin, and the quantum channels. -/
theorem comp_reconstructs_seq_release {c₁ c₂ : Cmd} {P : Partition}
    {φ₁ φ₂ : Release}
    (h₁ : BoundaryReleases c₁ P φ₁) (h₂ : BoundaryReleases c₂ P φ₂) :
    ∀ σ σ', qle
      ((((Bridge.ofRelease h₂).comp (Bridge.ofComponent c₁)).cert).toFun (qd σ σ'))
      ((leakBound P (seqRelease c₁ φ₁ φ₂)).toFun (qd σ σ')) := by
  intro σ σ' q hq hlow
  -- the composed certificate, computed by `Bridge.comp`, in reduced form:
  -- LowQuery q → (∃ x low, boundary atom of x separates σ,σ')
  --              ∨ (φ₂ ∘ boundary separates σ,σ')
  have hq' : LowQuery P q →
      (∃ x, P x = false ∧ qd σ σ' (fun s => atomQ x (evalStore c₁ s)))
        ∨ qd σ σ' (fun s => φ₂ (evalStore c₁ s)) := hq
  rcases hq' hlow with ⟨x, hx, hsep⟩ | hsep
  · -- a Low atom of the *boundary* separates the inputs: c₁'s certificate
    -- turns that into a Low input atom or a φ₁-separation — either lands in
    -- the seam certificate.
    by_cases hatom : ∃ y, P y = false ∧ qd σ σ' (atomQ y)
    · exact Or.inl hatom
    · refine Or.inr ?_
      have hle : lowEq P σ σ' := lowEq_of_no_atom hatom
      intro e
      simp only [seqRelease] at e
      injection e with e₁ e₂
      -- φ₁ agrees (e₁), so c₁'s certificate makes the boundary Low-equal,
      -- contradicting the separating boundary atom.
      exact hsep (congrArg Val.int (h₁ σ σ' hle e₁ x hx))
  · -- φ₂ at the boundary separates the inputs: that is the second component
    -- of the composed release.
    refine Or.inr ?_
    intro e
    simp only [seqRelease] at e
    injection e with e₁ e₂
    exact hsep e₂

end ConfTyping
