/-
  Stage C, first pass — where the interaction term actually lives.

  `Bridge.pair_comp_cert` says composing a bundle of certificates is
  **componentwise**: no interaction term, no side condition. The secure-compilation
  literature says composing distinct properties gives roughly the *intersection*.
  Stage C exists because both cannot be the whole story, and the plan's instruction
  was to attack the disagreement and find where it lives.

  **It lives in `hmap`.** `Bridge.pair` demands `b₂.map = b₁.map` — the two
  certificates must be about the *same artifact*. For two certificates produced by
  one tool over one semantics, that hypothesis is `rfl` and invisible. For two
  certificates produced by *different tools over different semantics*, it is the
  entire problem, and discharging it is a **semantic reconciliation obligation**
  that the composition law neither performs nor mentions. `pair_comp_cert` is true
  and costs nothing; it is the admission ticket that costs.

  That is the reconciliation of the two stories. Accumulation really is free —
  *downstream of* an obligation the secure-compilation results are, in effect,
  reporting on. Intersections show up there, not in the algebra.

  ── The concrete instance, and why it is not a toy point ──
  CN certifies memory ownership over the **architectural** semantics of C. It says
  nothing whatever about speculation — that is not a gap in CN, it is CN's stated
  scope. A speculative-constant-time certificate is about a machine that
  mispredicts. So the CN footprint received in `CNReceive.lean` is a fact about a
  *different map* from the one an SCT certificate is about, and bundling the two
  requires transferring the first onto the second's semantics.

  `arch_reconciliation_insufficient` shows that transfer is **not automatic, and
  not implied by agreement on the architectural state**: the bounds-check-bypass
  gadget agrees with its architectural counterpart on the store under every
  schedule (rollback is perfect), keeps its CN footprint architecturally, and
  *still* touches memory outside that footprint transiently. Store-level
  reconciliation is a strictly weaker condition than what bundling needs.

  `touchesOnly_of_inert` gives the condition that does suffice — the trace is
  schedule-independent, which is `Speculate.lean`'s `spec_inert` at this altitude —
  and `hetero_bundle_componentwise` then bundles a CN footprint with a
  differently-accumulating second certificate and gets `pair_comp_cert` for free.

  So the stage-C milestone lands in form (i): **conditions under which
  heterogeneous composition is non-lossy, plus a counterexample showing it fails
  without them.**

  ── Scope, stated before the theorems rather than after ──
  * **In this module** the second producer is **modelled, not transcribed.** `sctGA`
    is an SCT-*shaped* certificate — a public set that accumulates by
    **intersection** — chosen because it is a genuinely different monoid from CN's
    union, which is what makes the bundle heterogeneous. Nothing in *this* file is
    transcribed from Jasmin.

    **`JasminSCT.lean` is the second pass and supersedes this choice**, with the
    real level lattice read out of Jasmin's own test corpus
    (`corpus/jasmin/SOURCES.md`). It found that Jasmin already has a name for the
    gap this module constructs a counterexample to expose: `transient`. `sctGA` is
    kept because it is what the first pass actually rested on, and retrofitting it
    would hide that the structure was discovered rather than assumed.
  * The speculative machine here is **one schedule parameter and an address
    trace**, deliberately coarser than `Speculate.lean`'s. It carries exactly the
    asymmetry the argument needs — register effects roll back, touched addresses do
    not — and nothing else.
  * Nothing here re-verifies any C, any assembly, or any compiler.
-/
import ConfTyping.CNReceive

namespace ConfTyping

open TransportCalculus

/-! ## Two semantics for one artifact

The architectural machine, and a machine that mispredicts. -/

/-- A misprediction budget: how long a transient window may run. `0` is the
    architectural machine. A data parameter, exactly as in `Speculate.lean`. -/
abbrev Sched := Nat

/-- What a speculative run leaves behind: the architectural store (register and
    memory effects, after perfect rollback) and the **trace** of addresses
    touched, which does not roll back. That asymmetry is the whole model. -/
structure SpecRun where
  store : CStore
  trace : List CLoc

/-- An artifact under the speculative semantics. -/
abbrev SpecArtifact := Sched → CStore → SpecRun

/-- The store map a schedule induces. -/
def specStore (fs : SpecArtifact) (sch : Sched) : CStore → CStore :=
  fun σ => (fs sch σ).store

/-! ## The two candidate reconciliation conditions -/

/-- **Store-level reconciliation**: under every schedule the architectural state
    is what the architectural semantics said. This is what "rollback is perfect"
    buys, and it is what one is tempted to think suffices. -/
def Reconciles (fs : SpecArtifact) (fa : CStore → CStore) : Prop :=
  ∀ sch σ, (fs sch σ).store = fa σ

/-- **Trace-level reconciliation**: speculation is observationally inert — the
    addresses touched do not depend on the misprediction schedule. This is
    `Speculate.lean`'s `spec_inert` conclusion, stated at this altitude. -/
def TraceInert (fs : SpecArtifact) : Prop :=
  ∀ sch σ, (fs sch σ).trace = (fs 0 σ).trace

/-- CN's footprint, asked of the speculative machine: nothing outside `F` is
    touched, under **any** schedule. -/
def TouchesOnly (fs : SpecArtifact) (F : Footprint) : Prop :=
  ∀ sch σ l, l ∈ (fs sch σ).trace → F l

/-- CN's footprint, asked of the architectural machine only — which is the most
    any CN result can be asked for. -/
def ArchTouchesOnly (fs : SpecArtifact) (F : Footprint) : Prop :=
  ∀ σ l, l ∈ (fs 0 σ).trace → F l

/-! ## The counterexample: store-level reconciliation is not enough

The bounds-check bypass, at the coarsest scale that still carries it. Location `0`
holds the index; the guarded read is in bounds architecturally and out of bounds
transiently. -/

/-- Reads `mem[i]` under a bounds check. Architecturally the read happens only
    when `i < 4`. Under a misprediction the body runs anyway, the register effect
    is discarded — the store is returned untouched either way — and the address
    survives in the trace. -/
def bcbGadget : SpecArtifact := fun sch σ =>
  if σ 0 < 4 then { store := σ, trace := [σ 0] }
  else if sch = 0 then { store := σ, trace := [] }
  else { store := σ, trace := [σ 0] }

/-- The footprint CN would certify for it: the in-bounds region. -/
def bcbFootprint : Footprint := fun l => l < 4

/-- **Rollback is perfect**: the gadget agrees with the identity architectural
    map on the store, under every schedule. The strongest *state*-level
    reconciliation one could ask for holds. -/
theorem bcb_reconciles : Reconciles bcbGadget id := by
  intro sch σ
  show (bcbGadget sch σ).store = σ
  unfold bcbGadget
  split
  · rfl
  · split <;> rfl

/-- **And the CN certificate is honest architecturally**: on the architectural
    machine the gadget touches only what it owns. -/
theorem bcb_arch_touches : ArchTouchesOnly bcbGadget bcbFootprint := by
  intro σ l hl
  unfold bcbGadget at hl
  split at hl
  · rename_i hlt
    simp only [List.mem_singleton] at hl
    exact hl ▸ hlt
  · simp at hl

/-- **Yet the footprint is violated transiently.** With the index out of bounds
    and a window to run in, the gadget touches a location it does not own — and
    the evidence survives in the trace. -/
theorem bcb_not_touches : ¬ TouchesOnly bcbGadget bcbFootprint := by
  intro h
  have h7 : (7 : CLoc) ∈ (bcbGadget 1 (fun _ => 7)).trace := by decide
  have := h 1 (fun _ => 7) 7 h7
  simp [bcbFootprint] at this

/-- **The stage-C counterexample.** There is an artifact that reconciles with its
    architectural semantics on the store under every schedule, carries a CN
    footprint architecturally, and still touches memory outside that footprint.

    So a received CN certificate does **not** transfer to the speculative machine
    merely because the two agree on the architectural state. The obligation
    `Bridge.pair` hides in `hmap` is real, and it is strictly stronger than
    state-level agreement. -/
theorem arch_reconciliation_insufficient :
    ∃ (fs : SpecArtifact) (fa : CStore → CStore) (F : Footprint),
      Reconciles fs fa ∧ ArchTouchesOnly fs F ∧ ¬ TouchesOnly fs F :=
  ⟨bcbGadget, id, bcbFootprint,
   bcb_reconciles, bcb_arch_touches, bcb_not_touches⟩

/-- Which is to say the gadget is not trace-inert — the condition below is exactly
    what it fails. -/
theorem bcb_not_trace_inert : ¬ TraceInert bcbGadget := by
  intro h
  exact bcb_not_touches (fun sch σ l hl => bcb_arch_touches σ l (h sch σ ▸ hl))

/-! ## The condition that does suffice -/

/-- **Transfer.** If speculation is observationally inert, a footprint certified
    on the architectural machine holds on the speculative one verbatim. This is
    the hypothesis under which a CN certificate may be bundled with a certificate
    about a mispredicting machine at all. -/
theorem touchesOnly_of_inert {fs : SpecArtifact} {F : Footprint}
    (hi : TraceInert fs) (ha : ArchTouchesOnly fs F) : TouchesOnly fs F := by
  intro sch σ l hl
  exact ha σ l (hi sch σ ▸ hl)

/-- And store-level reconciliation makes every schedule's store map the *same*
    map — which is what discharges `Bridge.pair`'s `hmap` in the bundle below. -/
theorem specStore_eq_of_reconciles {fs : SpecArtifact} {fa : CStore → CStore}
    (h : Reconciles fs fa) (sch : Sched) : specStore fs sch = fa :=
  funext fun σ => h sch σ

/-- **The reception transfers — the sufficient condition, in one statement.**
    Given both reconciliation conditions, a CN certificate received for the
    architectural map is a certificate for the *speculative* artifact: every
    schedule's store map is the same map, so the `hmap` that `Bridge.pair`
    demands is discharged; and the footprint bounds the trace under every
    schedule, so the guarantee itself survives.

    `arch_reconciliation_insufficient` is precisely the observation that the
    first conjunct does not imply the second. Both are needed, and only the
    first is what "rollback is perfect" gives you. -/
theorem cn_reception_transfers {fs : SpecArtifact} {fa : CStore → CStore}
    {F : Footprint} (hr : Reconciles fs fa) (hi : TraceInert fs)
    (ha : ArchTouchesOnly fs F) (sch : Sched) :
    specStore fs sch = fa ∧ TouchesOnly fs F :=
  ⟨specStore_eq_of_reconciles hr sch, touchesOnly_of_inert hi ha⟩

/-! ## The second certificate: a different monoid on the same carrier

An SCT-shaped guarantee — *modelled, not transcribed*. A **public set**: the
locations at which the artifact is permitted to produce an observable difference.
It accumulates by **intersection**, where CN's footprint accumulates by union.
Two different monoids is what makes the bundle heterogeneous rather than two
copies of one thing. -/

/-- Public sets, ordered and acted on by **intersection**. A legitimate
    `GradedAction`: `act_mul` is associativity of `∧`, where `cnGA`'s is
    associativity of `∨`. -/
def sctGA : GradedAction Footprint Footprint where
  mul      := fun a b => fun l => a l ∧ b l
  le       := fsub
  act      := fun a d => fun l => a l ∧ d l
  le_trans := fun h₁ h₂ l ha => h₂ l (h₁ l ha)
  act_mul  := fun _ _ _ => by funext l; exact propext and_assoc
  act_mono := by
    intro m d d' h l hl
    exact ⟨hl.1, h l hl.2⟩

/-- The two accumulate by genuinely different laws: `cnGA` unions, `sctGA`
    intersects. Both are the *same* `Bridge.comp`. -/
theorem cn_unions_sct_intersects (A B : Footprint) (Γ : Ledger) :
    (cnGA.mul (A, Γ) (B, Γ)).1 = (fun l => A l ∨ B l)
    ∧ sctGA.mul A B = (fun l => A l ∧ B l) := ⟨rfl, rfl⟩

/-! ## The bundle: one artifact, two properties, one composition

A concrete artifact carrying both — clearing a location is a write (so it has a
footprint) and a declassification (so it has a public set). -/

/-- Zero location `5`. Owns `{5}`; may differ from a sibling run anywhere but `5`. -/
def clear5 : CStore → CStore := fun σ l => if l = 5 then 0 else σ l

theorem clear5_modifies : ModifiesOnly clear5 (fun l => l = 5) := by
  intro σ l hl
  simp only [clear5, ite_eq_right hl]

/-- Its CN half. -/
def clear5CN (Γ : Ledger) : Bridge CStore (Footprint × Ledger) Footprint cnGA cdist :=
  Bridge.ofCN clear5 (fun l => l = 5) Γ clear5_modifies

/-- Its SCT half: after the clear, the two runs can only still differ away from
    `5` — location `5` has been made public by construction. -/
def clear5SCT : Bridge CStore Footprint Footprint sctGA cdist where
  map       := clear5
  cert      := fun l => l ≠ 5
  contracts := fun σ τ l hne => by
    by_cases h5 : l = 5
    · exact absurd (by simp [clear5, h5]) hne
    · exact ⟨h5, by simpa only [cdist, clear5, ite_eq_right h5] using hne⟩

/-- **The stage-C milestone, positive direction.** One artifact, two certificates
    from two different accumulation laws, composed once: the footprints union and
    the public sets intersect, componentwise, with no interaction term — and the
    whole content of making this legitimate was discharging `hmap`. -/
theorem hetero_bundle_componentwise (Γ : Ledger) :
    (((clear5CN Γ).pair clear5SCT rfl).comp ((clear5CN Γ).pair clear5SCT rfl)).cert
      = ((((clear5CN Γ).comp (clear5CN Γ)).cert), (((clear5SCT).comp (clear5SCT)).cert)) :=
  Bridge.pair_comp_cert (clear5CN Γ) (clear5CN Γ) clear5SCT clear5SCT rfl rfl

/-- Spelled out: the footprint half unioned, the public half intersected, in one
    `Bridge.comp`. -/
theorem hetero_bundle_laws (Γ : Ledger) :
    (((clear5CN Γ).pair clear5SCT rfl).comp ((clear5CN Γ).pair clear5SCT rfl)).cert.1.1
      = (fun l => (l = 5) ∨ (l = 5))
    ∧ (((clear5CN Γ).pair clear5SCT rfl).comp ((clear5CN Γ).pair clear5SCT rfl)).cert.2
      = (fun l => (l ≠ 5) ∧ (l ≠ 5)) := ⟨rfl, rfl⟩

/-! ## What the stage concluded

Both stories survive, on different sides of one hypothesis:

* **`pair_comp_cert` is exactly right about composition.** Given a bundle, the
  accumulation is componentwise and free, for arbitrarily different monoids
  (`hetero_bundle_laws`: union beside intersection, one `Bridge.comp`).
* **`hmap` is where heterogeneity is paid for.** Forming the bundle requires the
  two certificates to be about one artifact. Across tools that is a semantic
  reconciliation obligation, `arch_reconciliation_insufficient` shows it is
  strictly stronger than agreement on the architectural state, and
  `touchesOnly_of_inert` gives a sufficient condition.

The honest reading of the disagreement the plan set this stage to find: the
literature's intersections are not a defect in the algebra, they are the price of
the admission ticket the algebra takes as a hypothesis. -/

end ConfTyping
