/-
  Layer 2: observations, the security parameter J with admissibility,
  the observation language, adversaries, and generation (§§3–5).
-/
import ConfTyping.Imp

namespace ConfTyping

/-! ## §3 Observations as functions of the semantics

An execution outcome is `(σ', t, b)`. Observations are total functions of
the outcome into a universal value domain `Val`, so that heterogeneous
channels (a cost, a trace, a store) share one type and can be *tupled*
(`Val.pair`) and *post-processed* (`Val → Val`) — the closure `Obs*`. -/

abbrev Outcome := Store × Nat × List Bool

inductive Val where
  | int  : Int → Val
  | bits : List Bool → Val
  | st   : (String → Int) → Val
  | pair : Val → Val → Val

/-- A primitive or derived observation: a function of the outcome. -/
abbrev Obs := Outcome → Val

/-- Apply an observation to the execution of `c` on input `σ`: `o⟦c⟧σ`. -/
def obs (o : Obs) (c : Cmd) (σ : Store) : Val := o (eval c σ)

/-- The three primitive observations of §3. `wall` = accumulated cost,
    `branch` = branch trace, `result` = final store restricted to Low. -/
def wall : Obs := fun o => .int (o.2.1 : Int)
def branchO : Obs := fun o => .bits o.2.2
def resultO (P : Partition) : Obs := fun o => .st (fun x => if P x then 0 else o.1 x)

/-- Closure operations on observations (`Obs*`): post-processing and tupling. -/
def post (f : Val → Val) (o : Obs) : Obs := fun out => f (o out)
def tup (o1 o2 : Obs) : Obs := fun out => .pair (o1 out) (o2 out)

/-! ## §3 Low-equivalence -/

/-- `σ ≈_L σ'` : the stores agree on every Low variable. -/
def lowEq (P : Partition) (σ σ' : Store) : Prop :=
  ∀ x, P x = false → σ x = σ' x

/-! ## §4 The security parameter J and admissibility

`J` is a parameter: a predicate on a program, an observation, and the
partition. Paper 1 instantiates it to noninterference `J_NI` or, abstractly,
to ε-leakage; §§5–8 never look inside it. -/

abbrev JTy := Cmd → Obs → Partition → Prop

/-- Noninterference instantiation: the observation is invariant under
    High-substitution (it is a function of Low alone). -/
def J_NI : JTy := fun c o P => ∀ σ σ', lowEq P σ σ' → obs o c σ = obs o c σ'

/-- **(A3) post-processing monotonicity** for `J_NI`: any function of a
    Low-determined observation is itself Low-determined. -/
theorem JNI_postproc (f : Val → Val) (c o P) :
    J_NI c o P → J_NI c (post f o) P := by
  intro h σ σ' hle
  simp only [J_NI, obs, post] at *
  rw [h σ σ' hle]

/-- **Separability** (Def. 5) for `J_NI`: a tuple of Low-determined
    observations is Low-determined. (This is what makes the per-channel
    presentation of Paper 1 legitimate — it is *not* admissibility.) -/
theorem JNI_separable (c o1 o2 P) :
    J_NI c o1 P → J_NI c o2 P → J_NI c (tup o1 o2) P := by
  intro h1 h2 σ σ' hle
  simp only [J_NI, obs, tup] at *
  rw [h1 σ σ' hle, h2 σ σ' hle]

/-! ## §5 Delimited release: bounding what a channel may reveal

The bulletproofed Policy stratum (framework §5, checklist item 3): a policy
discharge is a *declared* release `φ` **plus** a proof that the channel
reveals at most `φ`. There is no unbounded permit. -/

/-- A declared release: a function of the store whose value is permitted to
    flow to the channel (the framework's `φ(High)`). -/
abbrev Release := Store → Val

/-- `o` reveals **at most** `φ`: any two runs agreeing on Low *and* on `φ`
    agree on `o`. This is the framework's Policy proof obligation `𝒜̂ ⊑ φ`. -/
def ReleasesAtMost (c : Cmd) (o : Obs) (P : Partition) (φ : Release) : Prop :=
  ∀ σ σ', lowEq P σ σ' → φ σ = φ σ' → obs o c σ = obs o c σ'

/-- **Closure is the `φ = const` special case** (framework §5) — proved as a
    *theorem*, not encoded as a definitional collapse, so the strata stay
    syntactically distinct and the "was anything declassified?" provenance
    survives in the derivation. -/
theorem closure_is_const_policy (c : Cmd) (o : Obs) (P : Partition) (v : Val) :
    ReleasesAtMost c o P (fun _ => v) ↔ J_NI c o P := by
  constructor
  · intro h σ σ' hle; exact h σ σ' hle rfl
  · intro h σ σ' hle _; exact h σ σ' hle

/-! ## §5 Observation language, adversary, generation -/

/-- The sayable observations 𝒪 (parametrized by the partition, since
    `result` mentions it). -/
def OO (P : Partition) : List Obs := [wall, branchO, resultO P]

/-- Adversaries are capabilities: subsets of 𝒪. -/
def A_remote   (P : Partition) : List Obs := [resultO P]
def A_local    (P : Partition) : List Obs := [resultO P, wall]
def A_physical (P : Partition) : List Obs := [resultO P, wall, branchO]

/-- Generation `G(𝒪,𝒜)`: the obligations `J(o,H)` owed are exactly those
    for observations the adversary actually sees. We represent the obligation
    set by the carrier list of observations (J, H ride along, uninstantiated). -/
def Gen (𝒜 : List Obs) : List Obs := 𝒜

/-- **Lemma 1 (𝒜-monotonicity).** A stronger adversary owes a superset of
    obligations. -/
theorem gen_mono {𝒜 𝒜' : List Obs} (h : 𝒜 ⊆ 𝒜') : Gen 𝒜 ⊆ Gen 𝒜' := h

/-- The adversary chain `remote ⊆ local ⊆ physical`. -/
theorem A_chain (P : Partition) :
    A_remote P ⊆ A_local P ∧ A_local P ⊆ A_physical P := by
  refine ⟨?_, ?_⟩
  · intro o ho
    simp only [A_remote, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho; simp [A_local, List.mem_cons]
  · intro o ho
    simp only [A_local, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp [A_physical, List.mem_cons]

end ConfTyping
