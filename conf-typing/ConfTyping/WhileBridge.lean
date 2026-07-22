/-
  The Bridge reception over loops — brick 10: looping components land in the
  transport interface, with termination as a first-class coordinate of the
  distance.

  This is the last unported piece of the discipline (bricks 8, 9 did the seam
  and ledger over loops). Its design content, absent from the loop-free
  reception (`FlowBridge`): a looping component's boundary is a *partial* map —
  it may diverge — so the transport carrier lifts from `Store` to
  `OStore := Option Store` (`none` = diverged), and the query distance gains a
  **halting query** `haltQ` that observes whether a run terminated. Termination
  is thereby an observable *in the metric*, and a certified looping component is
  a contraction with respect to it.

  * distance   = `wqd`, queries on `OStore` separating two (possibly diverging)
                 boundary outputs — the halting query makes divergence visible;
  * map        = `wmap n c`, the fuelled boundary map on `OStore`;
  * certificate = the exact `wpull` transform (any component is a Bridge,
                 definitionally) or the leak bound `wNIBound`.

  Two receptions, mirroring `FlowBridge`. The **exact** one
  (`Bridge.ofWComponent`) is a full Bridge for any component at any fuel,
  definitionally, and it composes by the generic `Bridge.comp`
  (`ofWComponent_comp_map`/`_cert`). The **security** one is an *equivalence*
  (`wbridge_iff_sound`): on halting inputs the `wNIBound` contraction holds iff
  the component is store-and-halting noninterferent — and the halting query is
  the coordinate that makes "iff" mean *termination-sensitive*. `WOutNI` (brick
  7/8) supplies it at every fuel (`wOutNI_contracts`), so every checked looping
  component contracts in the interface. Termination-sensitive security **is** a
  Bridge contraction, in the same `GradedAction` as Lipschitz, Dobrushin, and
  the quantum channels.

  Honest scope: the security contraction is stated on *halting* input pairs
  (`some σ, some σ'`). The diverged-upstream rows (`none` input) are a distinct
  regime — an already-diverged input is not bounded by the downstream's input
  Low-atoms — so they are not folded into a single leak-bound Bridge; the exact
  Bridge covers all inputs, the leak-bound equivalence covers the halting ones.
-/
import TransportCalculus
import ConfTyping.WhileCompose

namespace ConfTyping

open TransportCalculus

/-! ## The halting-aware carrier and its query distance -/

/-- The boundary carrier: a store, or `none` for a diverged run. -/
abbrev OStore := Option Store

/-- Halting-aware Low-equivalence: agree on *whether* they halt and, if so, on
    Low store. -/
def oLowEq (P : Partition) : OStore → OStore → Prop
  | none,   none   => True
  | some s, some s' => lowEq P s s'
  | _,      _      => False

/-- A query on the halting-aware boundary. -/
abbrev WQuery := OStore → Val

/-- The distance carrier: sets of boundary queries, ordered by implication. -/
abbrev WQD := WQuery → Prop

def wqle (A B : WQD) : Prop := ∀ q, A q → B q

def wqleT : ∀ {a b c : WQD}, wqle a b → wqle b c → wqle a c :=
  fun h₁ h₂ q hq => h₂ q (h₁ q hq)

/-- **The halting-aware query distance.** -/
def wqd (os os' : OStore) : WQD := fun q => q os ≠ q os'

/-- The looping flow instance of the transport interface. -/
def wflowGA : GradedAction (Mono WQD wqle) WQD := universalGA wqle wqleT

/-! ## The termination coordinate: the halting query -/

/-- **The halting query** — the observable that only loops have: does the run
    terminate? This is what puts termination *into the metric*. -/
def haltQ : WQuery := fun os => match os with | some _ => .int 1 | none => .int 0

/-- The atom query reading one variable of the boundary store (`0` if
    diverged). -/
def watomQ (x : String) : WQuery :=
  fun os => match os with | some s => .int (s x) | none => .int 0

/-- A Low boundary query: constant on halting-aware-equivalent outputs. -/
def WLowQuery (P : Partition) (q : WQuery) : Prop :=
  ∀ os os', oLowEq P os os' → q os = q os'

/-- The halting query is Low: halting is preserved by `oLowEq`. -/
theorem haltQ_wlow (P : Partition) : WLowQuery P haltQ := by
  intro os os' h
  cases os with
  | none => cases os' with
    | none => rfl
    | some => exact h.elim
  | some => cases os' with
    | none => exact h.elim
    | some => rfl

/-- A Low-variable atom is a Low boundary query. -/
theorem watomQ_wlow {P : Partition} {x : String} (hx : P x = false) :
    WLowQuery P (watomQ x) := by
  intro os os' h
  cases os with
  | none => cases os' with
    | none => rfl
    | some => exact h.elim
  | some => cases os' with
    | none => exact h.elim
    | some => exact congrArg Val.int (h x hx)

/-! ## The fuelled boundary map and the exact reception -/

/-- The fuelled boundary map on the halting-aware carrier: a diverged input
    stays diverged; otherwise run `c` for `n` steps and keep the boundary store
    (or `none` if it diverges). -/
def wmap (n : Nat) (c : WCmd) : OStore → OStore :=
  fun os => os.bind fun s => (wexec n c s).map Prod.fst

/-- The exact transform: pull queries back along a boundary map. -/
def wpull (v : OStore → OStore) : Mono WQD wqle where
  toFun := fun A q => A (fun os => q (v os))
  mono  := fun h _ hq => h _ hq

/-- **Any looping component is a Bridge, exactly** — at any fuel, definitionally.
    The transport interface receives the looping boundary map with no proof
    obligation beyond the pull-back. -/
def Bridge.ofWComponent (n : Nat) (c : WCmd) :
    Bridge OStore (Mono WQD wqle) WQD wflowGA wqd where
  map       := wmap n c
  cert      := wpull (wmap n c)
  contracts := fun _ _ _ hq => hq

/-! ## The security certificate and the reception equivalence -/

/-- **The leak bound**, halting-aware: a Low boundary query (including the
    halting query) separates the outputs only if some Low input atom already
    separated the inputs. The halting query being covered is exactly what makes
    the certificate termination-sensitive. -/
def wNIBound (P : Partition) : Mono WQD wqle where
  toFun := fun A q => WLowQuery P q → ∃ x, P x = false ∧ A (watomQ x)
  mono  := fun h _ hq hlow => (hq hlow).imp fun x ⟨hx, ha⟩ => ⟨hx, h _ ha⟩

/-- Store-and-halting noninterference at fuel `n`: Low-equal inputs give
    halting-aware-equivalent boundary outputs. -/
def WHaltNI (n : Nat) (c : WCmd) (P : Partition) : Prop :=
  ∀ σ σ', lowEq P σ σ' → oLowEq P (wmap n c (some σ)) (wmap n c (some σ'))

/-- `WOutNI` (brick 7/8, full fuelled outcome) implies store-and-halting NI at
    every fuel — so every checked looping component satisfies the reception's
    security hypothesis. -/
theorem WOutNI_imp_haltNI {c : WCmd} {P : Partition} (h : WOutNI c P) (n : Nat) :
    WHaltNI n c P := by
  intro σ σ' hle
  have key := h n σ σ' hle
  simp only [wmap, Option.bind_some]
  cases hσ : wexec n c σ with
  | none => cases hσ' : wexec n c σ' with
    | none => exact True.intro
    | some r' => rw [hσ, hσ'] at key; exact key.elim
  | some r => cases hσ' : wexec n c σ' with
    | none => rw [hσ, hσ'] at key; exact key.elim
    | some r' => rw [hσ, hσ'] at key; exact key.1

/-- If two boundary outputs are not halting-aware-equivalent, some Low boundary
    query separates them — the halting query if they halt differently, a Low
    atom if their Low stores differ. -/
theorem exists_wlow_separator {P : Partition} {os os' : OStore}
    (h : ¬ oLowEq P os os') :
    ∃ q, WLowQuery P q ∧ wqd os os' q := by
  cases os with
  | none => cases os' with
    | none => exact absurd True.intro h
    | some s' => exact ⟨haltQ, haltQ_wlow P, by simp [wqd, haltQ]⟩
  | some s => cases os' with
    | none => exact ⟨haltQ, haltQ_wlow P, by simp [wqd, haltQ]⟩
    | some s' =>
        simp only [oLowEq] at h
        have hx : ∃ x, P x = false ∧ s x ≠ s' x := by
          rcases Classical.em (∃ x, P x = false ∧ s x ≠ s' x) with h' | h'
          · exact h'
          · exact absurd
              (fun x hxP => Classical.byContradiction fun hne => h' ⟨x, hxP, hne⟩) h
        obtain ⟨x, hxP, hne⟩ := hx
        refine ⟨watomQ x, watomQ_wlow hxP, ?_⟩
        simp only [wqd, watomQ]
        exact fun e => hne (by injection e)

/-- No Low input atom separating `σ, σ'` means they are Low-equal — the
    halting-aware analogue of `FlowBridge`'s `lowEq_of_no_atom`. -/
theorem lowEq_of_no_watom {P : Partition} {σ σ' : Store}
    (h : ¬ ∃ x, P x = false ∧ wqd (some σ) (some σ') (watomQ x)) :
    lowEq P σ σ' := by
  intro x hx
  by_cases he : σ x = σ' x
  · exact he
  · exact absurd ⟨x, hx, by simp only [wqd, watomQ]; exact fun e => he (by injection e)⟩ h

/-- **The reception is an equivalence.** A looping component carries the
    `wNIBound`-certified Bridge (the `contracts` inequality at every input pair,
    at fuel `n`) **iff** it is store-and-halting noninterferent at fuel `n`. The
    halting query being a Low separator is what makes the right-hand side
    termination-sensitive: the transport contraction *sees* divergence. -/
theorem wbridge_iff_sound (n : Nat) (c : WCmd) (P : Partition) :
    (∀ σ σ', wqle (wqd (wmap n c (some σ)) (wmap n c (some σ')))
                  ((wNIBound P).toFun (wqd (some σ) (some σ'))))
      ↔ WHaltNI n c P := by
  constructor
  · intro h σ σ' hle
    rcases Classical.em (oLowEq P (wmap n c (some σ)) (wmap n c (some σ')))
      with hok | hne
    · exact hok
    · exfalso
      obtain ⟨q, hlow, hsep⟩ := exists_wlow_separator hne
      obtain ⟨x, hx, hqd⟩ := h σ σ' q hsep hlow
      simp only [wqd, watomQ] at hqd
      exact hqd (congrArg Val.int (hle x hx))
  · intro hsound σ σ' q hsep hlow
    by_cases hatom : ∃ x, P x = false ∧ wqd (some σ) (some σ') (watomQ x)
    · exact hatom
    · exfalso
      have hle : lowEq P σ σ' := lowEq_of_no_watom hatom
      exact hsep (hlow _ _ (hsound σ σ' hle))

/-- **Termination-sensitive security is a transport contraction.** Given
    `WOutNI` (from the checker), at every fuel the halting-aware leak bound
    holds on halting inputs — the contraction condition of the interface, with
    the halting query as the coordinate that makes it termination-sensitive. -/
theorem wOutNI_contracts {c : WCmd} {P : Partition} (h : WOutNI c P) (n : Nat) :
    ∀ σ σ', wqle (wqd (wmap n c (some σ)) (wmap n c (some σ')))
                 ((wNIBound P).toFun (wqd (some σ) (some σ'))) :=
  (wbridge_iff_sound n c P).mpr (WOutNI_imp_haltNI h n)

/-! ## The exact reception composes -/

/-- The composite of two exact looping Bridges is the exact Bridge of the
    composed boundary maps — `Bridge.comp` threads the looping boundary through
    the interface's generic composition, definitionally. -/
theorem ofWComponent_comp_map (n : Nat) (c₁ c₂ : WCmd) :
    ((Bridge.ofWComponent n c₂).comp (Bridge.ofWComponent n c₁)).map
      = wmap n c₂ ∘ wmap n c₁ := rfl

/-- The composite Bridge's certificate is the composition of the two pull-back
    transforms — accumulation in the interface, definitionally. -/
theorem ofWComponent_comp_cert (n : Nat) (c₁ c₂ : WCmd) :
    ((Bridge.ofWComponent n c₂).comp (Bridge.ofWComponent n c₁)).cert
      = (wpull (wmap n c₂)).comp (wpull (wmap n c₁)) := rfl

end ConfTyping
