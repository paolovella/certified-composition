/-
  The abstract 2-safety module — generalizing `J_NI` to any J expressible as a
  binary trace-relation, and characterizing where separability holds.

  RESULT (correcting §10's conjecture). The conjecture "separable ⟺ 2-safety"
  is FALSE: separability is the *congruence refinement* of 2-safety
  (`PairClosed`), and `Rbad` witnesses `separable ⊊ 2-safety` deterministically,
  no randomness. What IS true: among *admissible* J (A2 ∧ A3), the only
  nondegenerate *2-safety* one is `J_NI` (`qualitative_admissible_is_JNI`),
  which is separable. This stops at arity 2: `ksafety_above_twosafety` exhibits
  an admissible deterministic 3-safety property (`notAllDistinct`) that is not
  `J_NI`. So the qualitative region is THREE nested layers — admissible 2-safety
  (= J_NI) ⊊ proper k-safety (k>2) ⊊ hyperproperties (= J_ε) — and only the
  outermost needs a distribution. The mathlib boundary is the k-safety /
  hyperproperty boundary, not the 2-safety boundary.

  All mathlib-free. Mathlib enters only to exhibit that the quantitative
  non-separable region is *inhabited* (a concrete `J_ε`) — a sanity check on a
  proven characterization, not a load-bearing step.
-/
import ConfTyping.Joint
import ConfTyping.Pleak

namespace ConfTyping

/-! ## The lift: J as a binary trace-relation -/

/-- A 2-safety property is a binary relation on observed values (refuted by a
    pair of Low-equal traces). -/
abbrev TwoSafety := Val → Val → Prop

/-- Lift a relation to a confidentiality judgment. `J_NI` is `R := (· = ·)`. -/
def J_rel (R : TwoSafety) (c : Cmd) (o : Obs) (P : Partition) : Prop :=
  ∀ σ σ', lowEq P σ σ' → R (obs o c σ) (obs o c σ')

theorem JNI_is_rel (c : Cmd) (o : Obs) (P : Partition) :
    J_NI c o P ↔ J_rel (· = ·) c o P := Iff.rfl

/-- **Separability condition** (pin 1): `R` is a congruence for `Val.pair`. -/
def PairClosed (R : TwoSafety) : Prop :=
  ∀ x x' y y', R x x' → R y y' → R (.pair x y) (.pair x' y')

/-- **A3 for `J_rel`** (pin 2): preservation under all post-processings. -/
def PostClosed (R : TwoSafety) : Prop :=
  ∀ (f : Val → Val) x x', R x x' → R (f x) (f x')

/-! ## Forward and backward over the whole class -/

/-- A3 transfers across post-processing at the relation level. -/
theorem rel_postproc (R : TwoSafety) (hpost : PostClosed R) (f : Val → Val)
    (c : Cmd) (o : Obs) (P : Partition) :
    J_rel R c o P → J_rel R c (post f o) P := by
  intro h σ σ' hle; exact hpost f _ _ (h σ σ' hle)

/-- **FORWARD over the class.** `PairClosed` (+ a reflexive seed) ⇒ separable.
    `J_NI`'s `perchannel_to_joint` is this at `R := (· = ·)`. -/
theorem rel_perchannel_to_joint (R : TwoSafety) (c : Cmd) (P : Partition)
    (hpc : PairClosed R) (hseed : R (.int 0) (.int 0)) :
    ∀ 𝒜, (∀ o ∈ 𝒜, J_rel R c o P) → J_rel R c (joint 𝒜) P := by
  intro 𝒜; induction 𝒜 with
  | nil => intro _ σ σ' _; exact hseed
  | cons a as ih =>
      intro h σ σ' hle
      exact hpc _ _ _ _ (h a (by simp) σ σ' hle)
              (ih (fun o ho => h o (List.mem_cons_of_mem a ho)) σ σ' hle)

/-- **BACKWARD over the class.** `PostClosed` (A3) ⇒ complete. -/
theorem rel_joint_to_perchannel (R : TwoSafety) (c : Cmd) (P : Partition)
    (hpost : PostClosed R) :
    ∀ 𝒜, J_rel R c (joint 𝒜) P → ∀ o ∈ 𝒜, J_rel R c o P := by
  intro 𝒜; induction 𝒜 with
  | nil => intro _ o ho; simp at ho
  | cons a as ih =>
      intro hj o ho
      have ha : J_rel R c a P :=
        joint_cons_fst a as ▸ rel_postproc R hpost fstV c (joint (a :: as)) P hj
      have htail : J_rel R c (joint as) P :=
        joint_cons_snd a as ▸ rel_postproc R hpost sndV c (joint (a :: as)) P hj
      rcases List.mem_cons.mp ho with rfl | ho'
      · exact ha
      · exact ih htail o ho'

theorem rel_separability_equiv (R : TwoSafety) (c : Cmd) (P : Partition)
    (hpc : PairClosed R) (hpost : PostClosed R) (hseed : R (.int 0) (.int 0))
    (𝒜 : List Obs) :
    (∀ o ∈ 𝒜, J_rel R c o P) ↔ J_rel R c (joint 𝒜) P :=
  ⟨rel_perchannel_to_joint R c P hpc hseed 𝒜, rel_joint_to_perchannel R c P hpost 𝒜⟩

/-! ## The headline: A3 collapses any relation to total-or-equality -/

/-- **A3 is brutal.** Preservation under *all* unary functions forces `R` to be
    either the total relation or a subrelation of equality: relate one distinct
    pair `a ≠ b`, and a relabeling function drags `R` to the total relation. -/
theorem postclosed_collapse (R : TwoSafety) (hpost : PostClosed R) :
    (∀ x x', R x x') ∨ (∀ x x', R x x' → x = x') := by
  classical
  by_cases h : ∃ a b, R a b ∧ a ≠ b
  · obtain ⟨a, b, hab, hne⟩ := h
    left
    intro c d
    have key := hpost (fun v => if v = a then c else d) a b hab
    rw [if_pos rfl, if_neg (Ne.symm hne)] at key
    exact key
  · right
    intro x x' hx
    by_cases hxx : x = x'
    · exact hxx
    · exact absurd ⟨x, x', hx, hxx⟩ h

/-- **The corrected §10, qualitative side.** Among A2 ∧ A3-admissible J, the
    only nondegenerate binary-relation (2-safety) one is `J_NI`. A3 collapses
    `R` to total-or-equality; A2 (non-triviality) deletes the total relation;
    reflexivity (A3 again, on the nonempty witness) pushes `⊆ Eq` up to `Eq`. -/
theorem qualitative_admissible_is_JNI (R : TwoSafety)
    (hpost : PostClosed R)
    (hA2 : ¬ (∀ x x', R x x'))          -- A2: not the trivial total relation
    (hne : ∃ x x', R x x') :            -- the property is inhabited
    ∀ x x', R x x' ↔ x = x' := by
  rcases postclosed_collapse R hpost with htot | hsub
  · exact absurd htot hA2
  · obtain ⟨a, a', haa'⟩ := hne
    have e : a = a' := hsub a a' haa'
    rw [← e] at haa'                    -- haa' : R a a
    intro x x'
    refine ⟨hsub x x', ?_⟩
    intro hxx; subst hxx
    have := hpost (fun _ => x) a a haa'
    simpa using this

/-! ## The non-example: separable ⊊ 2-safety, deterministically -/

def Val.isPair : Val → Bool
  | .pair _ _ => true
  | _         => false

/-- A 2-safety relation that is NOT `PairClosed`: equal first component when
    both are pairs, else blind to non-pairs. -/
def Rbad : TwoSafety := fun x x' =>
  (∃ a b a' b', x = .pair a b ∧ x' = .pair a' b' ∧ a = a')
    ∨ (x.isPair = false ∧ x'.isPair = false)

theorem Rbad_not_pairClosed : ¬ PairClosed Rbad := by
  intro hpc
  have key := hpc (.int 0) (.int 1) (.int 0) (.int 0)
                  (Or.inr ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩)
  rcases key with ⟨a, b, a', b', h1, h2, h3⟩ | ⟨h1, _⟩
  · injection h1 with ha _
    injection h2 with ha' _
    rw [← ha, ← ha'] at h3
    injection h3 with h3'
    simp at h3'
  · simp [Val.isPair] at h1

/-- **The refutation.** `Rbad` is 2-safety but non-separable: two non-pair
    leaking channels (`branchO`) each satisfy `J_rel Rbad` via the "neither
    pair" branch, yet their tuple exposes the leak through the first-component
    test. So `separable ⊊ 2-safety` — no randomness used. -/
theorem Rbad_nonseparable :
    ∃ (c : Cmd) (o₁ o₂ : Obs) (P : Partition),
      J_rel Rbad c o₁ P ∧ J_rel Rbad c o₂ P ∧ ¬ J_rel Rbad c (tup o₁ o₂) P := by
  refine ⟨Pleak, branchO, branchO, Phigh, ?_, ?_, ?_⟩
  · intro σ σ' _; exact Or.inr ⟨rfl, rfl⟩
  · intro σ σ' _; exact Or.inr ⟨rfl, rfl⟩
  · intro h
    have key := h σ0 σ1 lowEq_σ
    simp only [obs, tup, branchO] at key
    rw [branch_σ0, branch_σ1] at key
    rcases key with ⟨a, b, a', b', h1, h2, h3⟩ | ⟨h1, _⟩
    · injection h1 with ha _
      injection h2 with ha' _
      rw [← ha, ← ha'] at h3
      injection h3 with h3'
      simp at h3'
    · simp [Val.isPair] at h1

/-! ## Arity 3: the k-safety hierarchy lives strictly above 2-safety

A3 is *simultaneous* (one post-processor `f` on the whole observation, since
post-processing composes `f` with the single channel `o`). Simultaneous unary
`f` can only *coarsen* a tuple's equality-pattern, never refine it — so A3
closes a property upward to the diagonal but is blind downward. At arity ≥ 3
that leaves room: `notAllDistinct` is admissible (A2 ∧ A3), deterministic, and
**not** `J_NI`. So `qualitative_admissible_is_JNI` does not extend past
arity 2; the correct characterization is admissible **2-safety** ⟺ `J_NI`. -/

abbrev ThreeSafety := Val → Val → Val → Prop

def J_rel3 (R : ThreeSafety) (c : Cmd) (o : Obs) (P : Partition) : Prop :=
  ∀ σ₁ σ₂ σ₃, lowEq P σ₁ σ₂ → lowEq P σ₂ σ₃ →
    R (obs o c σ₁) (obs o c σ₂) (obs o c σ₃)

/-- A3 at arity 3: one `f` applied to all three coordinates (simultaneous). -/
def PostClosed3 (R : ThreeSafety) : Prop :=
  ∀ (f : Val → Val) x y z, R x y z → R (f x) (f y) (f z)

/-- The canonical 3-safety-not-2-safety property (Clarkson–Schneider shape):
    refuted only by exhibiting *three* all-distinct traces. -/
def notAllDistinct : ThreeSafety := fun x y z => ¬(x ≠ y ∧ y ≠ z ∧ x ≠ z)

/-- **A3 holds** — because `f` a function preserves the coincidences that make
    a triple not-all-distinct. -/
theorem notAllDistinct_postclosed : PostClosed3 notAllDistinct := by
  intro f x y z h hcon
  exact h ⟨fun e => hcon.1 (congrArg f e),
           fun e => hcon.2.1 (congrArg f e),
           fun e => hcon.2.2 (congrArg f e)⟩

/-- `branchO` on `P_leak` is two-valued under High-variation, so any three
    traces are never all distinct — it satisfies the ternary property. -/
theorem branch_Pleak_val (σ : Store) :
    obs branchO Pleak σ = .bits (if σ "b" ≠ 0 then [true] else [false]) := by
  simp only [obs, branchO, Pleak, eval, evalE]
  by_cases h : σ "b" ≠ 0 <;> simp [h]

theorem branchO_J_rel3 : J_rel3 notAllDistinct Pleak branchO Phigh := by
  intro σ₁ σ₂ σ₃ _ _
  simp only [notAllDistinct, branch_Pleak_val]
  by_cases h1 : σ₁ "b" ≠ 0 <;> by_cases h2 : σ₂ "b" ≠ 0 <;> by_cases h3 : σ₃ "b" ≠ 0 <;>
    simp_all

/-- **2-safety ⊊ admissible-qualitative.** `notAllDistinct` is admissible
    (A3 holds; A2 via the partition-parameterized lift) and satisfied by a
    channel `J_NI` rejects. So "admissible qualitative ⟺ J_NI" is too strong:
    only the *2-safety* fragment collapses to `J_NI`, and the proper k-safety
    hierarchy (k > 2) is inhabited, deterministic, and mathlib-free. -/
theorem ksafety_above_twosafety :
    PostClosed3 notAllDistinct
      ∧ J_rel3 notAllDistinct Pleak branchO Phigh
      ∧ ¬ J_NI Pleak branchO Phigh :=
  ⟨notAllDistinct_postclosed, branchO_J_rel3, branch_not_closable⟩

/-! ## The k-ary picture: admissible ⟹ kernel-determined

A property of a k-tuple of traces closed under *simultaneous* post-processing
(one `f` on all coordinates — the faithful A3) depends only on the tuple's
**kernel**: which coordinates are equal, i.e. the pairwise equalities. So there
are **no k-irreducible admissible properties** — every admissible k-safety
property is a function of pairwise equalities. The k-safety hierarchy is real
(unbounded refutation degree) but its *atoms* are all 2-ary; region 2 is the
up-set lattice of the partition lattice Πₖ, infinite yet finitely generated. -/

/-- Simultaneous A3 at arbitrary arity: one `f` applied to all coordinates. -/
def SimA3 {k : Nat} (P : (Fin k → Val) → Prop) : Prop :=
  ∀ (f : Val → Val) (x : Fin k → Val), P x → P (fun i => f (x i))

/-- Same kernel = same pairwise-equality pattern. -/
def sameKernel {k : Nat} (x x' : Fin k → Val) : Prop :=
  ∀ i j, x i = x j ↔ x' i = x' j

/-- Kernel coarsening: `x'` merges at least the coordinates `x` does
    (`ker x ⊆ ker x'`), i.e. `x'` is higher in the partition lattice. -/
def kerLE {k : Nat} (x x' : Fin k → Val) : Prop :=
  ∀ i j, x i = x j → x' i = x' j

/-- **A3 ⟹ up-closed.** A simultaneous-A3 property is preserved when the kernel
    is *coarsened*: the coarser `x'` factors as `f∘x` (the relabeling `x i ↦ x' i`
    is well-defined exactly because `ker x ⊆ ker x'`), and A3 transports `P`. -/
theorem A3_coarsen {k : Nat} (P : (Fin k → Val) → Prop) (hP : SimA3 P)
    (x x' : Fin k → Val) (hle : kerLE x x') : P x → P x' := by
  classical
  intro hx
  have hP' := hP (fun v => if h : ∃ i, x i = v then x' h.choose else .int 0) x hx
  have heq : (fun i => (if h : ∃ j, x j = x i then x' h.choose else .int 0)) = x' := by
    funext i
    have hex : ∃ j, x j = x i := ⟨i, rfl⟩
    rw [dif_pos hex]
    exact hle hex.choose i hex.choose_spec
  rwa [heq] at hP'

/-- **A3 ⟹ kernel-determined.** Same pairwise-equality pattern ⟹ same truth
    value (coarsening both ways). No admissible property sees past the pairwise
    equalities — the "genuinely k-ary" admissible property does not exist. -/
theorem A3_factors_kernel {k : Nat} (P : (Fin k → Val) → Prop) (hP : SimA3 P)
    (x x' : Fin k → Val) (hk : sameKernel x x') : P x → P x' :=
  A3_coarsen P hP x x' (fun i j h => (hk i j).mp h)

theorem no_irreducible_admissible {k : Nat} (P : (Fin k → Val) → Prop)
    (hP : SimA3 P) (x x' : Fin k → Val) (hk : sameKernel x x') : P x ↔ P x' :=
  ⟨A3_factors_kernel P hP x x' hk,
   A3_factors_kernel P hP x' x (fun i j => (hk i j).symm)⟩

/-- A property is an **up-set of the partition lattice**: closed under coarsening
    the kernel (closed upward in the refinement order). -/
def RespectsCoarsening {k : Nat} (P : (Fin k → Val) → Prop) : Prop :=
  ∀ x x', kerLE x x' → P x → P x'

/-- **The Πₖ up-set characterization.** A k-safety property is admissible
    (simultaneous-A3) **iff** it is an up-set of the kernel-coarsening order —
    closed upward in the partition lattice Πₖ. Forward is `A3_coarsen`; backward
    is that `ker x ⊆ ker (f∘x)` always, so respecting coarsening yields A3.
    Fully general over `k`, mathlib-free.

    The realizability edge (pinned, not hidden): this characterizes admissible
    properties as up-sets of the order on *realizable* kernels. For a value-rich
    channel (`Val` is `.int`-infinite) every partition of `Fin k` is realizable,
    so the order is the full Πₖ and the family grows with `k`; for a
    Boolean-valued channel only ≤2-block kernels are realizable and region 2
    truncates to a finite stub. "Realizable kernels = full Πₖ for `Val`" needs
    `Finset.min'` combinatorics (mathlib) and stays argued; the iff does not. -/
theorem simA3_iff_respectsCoarsening {k : Nat} (P : (Fin k → Val) → Prop) :
    SimA3 P ↔ RespectsCoarsening P := by
  constructor
  · intro hP x x' hle hx
    exact A3_coarsen P hP x x' hle hx
  · intro hR f x hx
    exact hR x (fun i => f (x i)) (fun i j h => congrArg f h) hx

end ConfTyping
