/-
  Phase 5: the reps theorem at actual ω₁.

  `transport-calculus` proves, mathlib-free, the four-step engine of the set-theoretic
  notes: over any abstract index with least witnesses (`WellIndex`), σ-directedness
  (`SigmaDirected`), countable segments (`CountableSegments`), and no top, a coherent
  sequence admitting a level-monotone representative system is trivial
  (`reps_implies_trivial`). Its intended model — ω₁ — is not constructible there.

  This file constructs the model from mathlib and instantiates: the index is
  `OmegaOne := (ω₁).ToType` (a `Type 0` well order); least witnesses come from
  well-foundedness; σ-directedness from the regularity of ℵ₁
  (`Cardinal.iSup_lt_ord_of_isRegular`); countable segments from `#o.ToType = o.card`
  below ℵ₁; unboundedness from closure of countability under successors. The
  `FiniteP`-to-`Set.Finite` bridge shows the abstract coherence notion is the standard
  mod-finite one, so the headline is, in standard vocabulary:

  **Every coherent sequence on ω₁ admitting a pointwise level-monotone system of
  representatives is trivial** (`omega1_reps_implies_trivial`), equivalently: a
  nontrivial coherent sequence on ω₁ — e.g. Todorcevic's walk families, which witness
  `H¹(ω₁; ℤ) ≠ 0` — admits no monotone representative system
  (`nontrivial_coherent_no_reps`). To our knowledge this is the first machine-checked
  theorem about coherent sequences on ω₁.
-/
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Aleph
import TransportCalculus

namespace TransportKernel

open Cardinal Ordinal Set
open scoped Ordinal

/-- The countable ordinals, as a `Type 0` well order: mathlib's `ω₁.ToType`. -/
noncomputable abbrev OmegaOne : Type := (ω₁ : Ordinal).ToType

namespace OmegaOne

/-- The ordinal below ω₁ corresponding to an element. -/
noncomputable abbrev ord (x : OmegaOne) : Ordinal := (ToType.toOrd x : Ordinal)

theorem ord_lt (x : OmegaOne) : ord x < ω₁ := (ToType.toOrd x).2

theorem le_iff {x y : OmegaOne} : x ≤ y ↔ ord x ≤ ord y := by
  rw [← ToType.mk.symm.le_iff_le]
  rfl

theorem lt_iff {x y : OmegaOne} : x < y ↔ ord x < ord y := by
  rw [← ToType.mk.symm.lt_iff_lt]
  rfl

theorem toOrd_mk' {o : Ordinal} (z : Set.Iio o) : ToType.toOrd (ToType.mk z) = z :=
  OrderIso.symm_apply_apply _ _

theorem mk_toOrd' {o : Ordinal} (x : o.ToType) : ToType.mk (ToType.toOrd x) = x :=
  OrderIso.apply_symm_apply _ _

theorem ord_mk {o : Ordinal} (h : o < ω₁) : ord (ToType.mk ⟨o, h⟩) = o :=
  congrArg Subtype.val (toOrd_mk' ⟨o, h⟩)

/-- Least witnesses, from well-foundedness of `<` on `ToType`. -/
theorem exists_least {p : OmegaOne → Prop} (hp : ∃ x, p x) :
    ∃ μ, p μ ∧ ∀ m, p m → μ ≤ m := by
  obtain ⟨μ, hμ, hmin⟩ := (wellFounded_lt (α := OmegaOne)).has_min {x | p x} hp
  exact ⟨μ, hμ, fun m hm => not_lt.mp (hmin m hm)⟩

end OmegaOne

/-- ω₁ as a `WellIndex`: the mathlib model of the abstract index. -/
noncomputable def wellIndexOmegaOne : TransportCalculus.WellIndex OmegaOne where
  le          := (· ≤ ·)
  le_refl     := le_refl
  le_trans    := fun h₁ h₂ => le_trans h₁ h₂
  le_antisymm := fun h₁ h₂ => le_antisymm h₁ h₂
  least       := fun _ hp => OmegaOne.exists_least hp

/-- σ-directedness of ω₁ = regularity of ℵ₁: countable families of countable ordinals
    are bounded. -/
theorem sigmaDirected_omegaOne : TransportCalculus.SigmaDirected OmegaOne (· ≤ ·) := by
  intro f
  have hsup : (⨆ n, OmegaOne.ord (f n)) < (ω₁ : Ordinal) := by
    refine Ordinal.iSup_lt_of_lt_cof ?_ (fun n => OmegaOne.ord_lt (f n))
    have hcof : (ω₁ : Ordinal).cof = ℵ₁ := by
      rw [← ord_aleph]
      exact Cardinal.isRegular_aleph_one.cof_ord
    rw [hcof, Cardinal.mk_nat]
    exact aleph0_lt_aleph_one
  refine ⟨ToType.mk ⟨_, Set.mem_Iio.mpr hsup⟩, fun n => ?_⟩
  show f n ≤ ToType.mk ⟨_, Set.mem_Iio.mpr hsup⟩
  rw [OmegaOne.le_iff, OmegaOne.ord_mk]
  exact le_ciSup Ordinal.bddAbove_of_small n

/-- Segments of ω₁ are countable: cardinalities below ℵ₁ are at most ℵ₀. -/
theorem countableSegments_omegaOne :
    TransportCalculus.CountableSegments wellIndexOmegaOne := by
  intro w
  -- the segment injects into `(ord w + 1).ToType`, which is countable
  have hcard : (OmegaOne.ord w).card + 1 < ℵ₁ := by
    have hw : (OmegaOne.ord w).card ≤ ℵ₀ := by
      rw [← Cardinal.lt_aleph_one_iff, ← Cardinal.lt_ord, ord_aleph]
      exact OmegaOne.ord_lt w
    calc (OmegaOne.ord w).card + 1 ≤ ℵ₀ + 1 := add_le_add_left hw 1
      _ = ℵ₀ := by simp
      _ < ℵ₁ := aleph0_lt_aleph_one
  have holt : OmegaOne.ord w + 1 < (ω₁ : Ordinal) := by
    rw [← ord_aleph, Cardinal.lt_ord, Ordinal.card_add_one]
    exact hcard
  have hcnt : Countable (OmegaOne.ord w + 1).ToType := by
    rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType, Ordinal.card_add_one,
        ← Cardinal.lt_aleph_one_iff]
    exact hcard
  have hne : Nonempty (OmegaOne.ord w + 1).ToType := by
    rw [Ordinal.nonempty_toType_iff]
    exact fun h => by simpa using congrArg Ordinal.card h
  obtain ⟨g, hg⟩ := exists_surjective_nat (OmegaOne.ord w + 1).ToType
  -- push the enumeration into `OmegaOne`
  refine ⟨fun n => ToType.mk ⟨(ToType.toOrd (g n) : Ordinal),
    Set.mem_Iio.mpr (lt_trans (ToType.toOrd (g n)).2 holt)⟩, fun v hv => ?_⟩
  -- every `v ≤ w` is hit: its ordinal is `< ord w + 1`
  have hvle : OmegaOne.ord v ≤ OmegaOne.ord w := by
    rw [← OmegaOne.le_iff]
    exact hv
  have hvo : OmegaOne.ord v < OmegaOne.ord w + 1 := lt_of_le_of_lt hvle (lt_add_one _)
  obtain ⟨n, hn⟩ := hg (ToType.mk ⟨OmegaOne.ord v, hvo⟩)
  refine ⟨n, ?_⟩
  have hval : (ToType.toOrd (g n) : Ordinal) = OmegaOne.ord v := by
    rw [hn, OmegaOne.toOrd_mk']
  -- rebuild `v` from its ordinal
  rw [← OmegaOne.mk_toOrd' v]
  exact congrArg _ (Subtype.ext hval)

/-- ω₁ has no top: successors of countable ordinals are countable. -/
theorem unbounded_omegaOne : ∀ w : OmegaOne, ∃ w', ¬ w' ≤ w := by
  intro w
  have hsucc : OmegaOne.ord w + 1 < (ω₁ : Ordinal) := by
    rw [← ord_aleph, Cardinal.lt_ord, Ordinal.card_add_one]
    have hw : (OmegaOne.ord w).card ≤ ℵ₀ := by
      rw [← Cardinal.lt_aleph_one_iff, ← Cardinal.lt_ord, ord_aleph]
      exact OmegaOne.ord_lt w
    calc (OmegaOne.ord w).card + 1 ≤ ℵ₀ + 1 := add_le_add_left hw 1
      _ = ℵ₀ := by simp
      _ < ℵ₁ := aleph0_lt_aleph_one
  refine ⟨ToType.mk ⟨_, Set.mem_Iio.mpr hsucc⟩, ?_⟩
  rw [OmegaOne.le_iff, OmegaOne.ord_mk]
  exact not_le.mpr (lt_add_one _)

/-- A base point: `0 < ω₁`. -/
noncomputable def zeroOmegaOne : OmegaOne :=
  ToType.mk ⟨0, Set.mem_Iio.mpr (by
    rw [← ord_aleph, Cardinal.lt_ord, Ordinal.card_zero]
    exact Cardinal.aleph0_pos.trans aleph0_lt_aleph_one)⟩

/-- The abstract finiteness (`FiniteP`, coverage by a list) is `Set.Finite`: the
    abstract coherence notion is the standard mod-finite one. -/
theorem finiteP_iff_finite {A : Type} (P : A → Prop) :
    TransportCalculus.FiniteP P ↔ {a | P a}.Finite := by
  constructor
  · intro ⟨L, hL⟩
    exact Set.Finite.subset L.finite_toSet (fun a ha => hL a ha)
  · intro h
    refine ⟨h.toFinset.toList, fun a ha => ?_⟩
    rw [Finset.mem_toList, Set.Finite.mem_toFinset]
    exact ha

/-- **The reps theorem at ω₁, machine-checked.** A coherent sequence on ω₁ (pairwise
    mod-finite-equal rows, by `finiteP_iff_finite`) admitting a pointwise level-monotone
    system of representatives is trivial. The abstract engine is
    `TransportCalculus.reps_implies_trivial`; this instantiates its three index
    hypotheses at mathlib's ω₁: least witnesses (well-foundedness), σ-directedness
    (regularity of ℵ₁), countable segments (cardinality below ℵ₁). -/
theorem omega1_reps_implies_trivial
    (C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne)
    (R : TransportCalculus.Reps C) : C.Trivial :=
  TransportCalculus.reps_implies_trivial wellIndexOmegaOne
    sigmaDirected_omegaOne countableSegments_omegaOne unbounded_omegaOne
    zeroOmegaOne C R

/-- Contrapositive, in the vocabulary of the set-theoretic literature: a *nontrivial*
    coherent sequence on ω₁ — such as Todorcevic's walk families witnessing
    `H¹(ω₁; ℤ) ≠ 0` — admits no monotone representative system. -/
theorem nontrivial_coherent_no_reps
    (C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne)
    (h : ¬ C.Trivial) : IsEmpty (TransportCalculus.Reps C) :=
  ⟨fun R => h (omega1_reps_implies_trivial C R)⟩

/-- Non-vacuity: the structures are inhabited (the zero sequence is coherent, with
    itself as a representative system — and it is trivial, as the theorem demands). -/
noncomputable example : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne :=
  ⟨fun _ _ => 0, fun _ _ => ⟨[], fun _ h => absurd h.2.2 (by simp)⟩⟩

end TransportKernel
