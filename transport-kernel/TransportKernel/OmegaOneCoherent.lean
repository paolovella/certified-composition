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
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Countable
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

/-! ## Finite-to-one rows force nontriviality

    `omega1_reps_implies_trivial` is *conditional*: it says nothing until a nontrivial
    coherent sequence is produced, and nontriviality was cited (Todorcevic's walks), not
    proved here. This section removes the citation for a canonical class.

    A coherent sequence has **finite-to-one rows** when each row takes each value-bound
    only finitely often below its level — Todorcevic's Handbook Lemma 1.16(a) for `ρ₁`,
    whose rows `(ρ₁)_α` satisfy exactly this and whose coherence is 1.16(b). The theorem
    below is the classical ZFC engine behind "`T(ρ₁)` is Aronszajn" (Handbook 1.17),
    machine-checked here: **finite-to-one + coherent ⟹ nontrivial**, no axioms beyond
    the standard three, no walks.

    Composed with the reps theorem this makes the program's obstruction unconditional:
    a coherent sequence on ω₁ with finite-to-one rows admits *no* monotone
    representative system (`omega1_finiteToOne_no_reps`) — a statement with no
    hypothesis that has to be imported from the literature. -/

/-- The `WellIndex` strict order on ω₁ is the ordinal one. -/
theorem wi_lt_iff {u w : OmegaOne} : wellIndexOmegaOne.lt u w ↔ u < w := by
  constructor
  · rintro ⟨h1, h2⟩
    exact lt_of_le_of_ne h1 (fun h => h2 (le_of_eq h.symm))
  · intro h
    exact ⟨le_of_lt h, not_le.mpr h⟩

/-- **Finite-to-one rows.** Below every level, each row takes each value-bound only
    finitely often: Handbook 1.16(a), `{ξ ≤ α : ρ₁(ξ,α) ≤ n}` is finite. -/
def FiniteToOne (C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne) : Prop :=
  ∀ (w : OmegaOne) (n : Nat), {u : OmegaOne | u < w ∧ C.e w u ≤ n}.Finite

/-- Counting below is strictly monotone on a segment-finite set. -/
theorem ncard_lt_of_lt {S : Set OmegaOne} (h : ∀ w : OmegaOne, (S ∩ Set.Iio w).Finite)
    {a b : OmegaOne} (ha : a ∈ S) (hlt : a < b) :
    (S ∩ Set.Iio a : Set OmegaOne).ncard < (S ∩ Set.Iio b : Set OmegaOne).ncard := by
  refine Set.ncard_lt_ncard ⟨fun x hx => ⟨hx.1, lt_trans hx.2 hlt⟩, ?_⟩ (h b)
  intro hsub
  exact absurd (hsub ⟨ha, hlt⟩).2 (lt_irrefl a)

/-- **Segment-finite ⟹ countable.** A set of countable ordinals meeting every initial
    segment finitely is countable, because `u ↦ |S ∩ Iio u|` is a strictly monotone —
    hence injective — map into `ℕ`. (This is the order-type-`≤ ω` observation, done
    without building an enumeration.) -/
theorem countable_of_segments_finite {S : Set OmegaOne}
    (h : ∀ w : OmegaOne, (S ∩ Set.Iio w).Finite) : S.Countable := by
  rw [Set.countable_iff_exists_injective]
  refine ⟨fun u => (S ∩ Set.Iio u.1 : Set OmegaOne).ncard, ?_⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only at hab
  refine Subtype.ext ?_
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd hab (Nat.ne_of_lt (ncard_lt_of_lt h ha hlt))
  · exact heq
  · exact absurd hab.symm (Nat.ne_of_lt (ncard_lt_of_lt h hb hgt))

/-- **Countable ⟹ bounded**, the regularity of ℵ₁ — reusing the σ-directedness
    instance that already models it. -/
theorem bounded_of_countable {S : Set OmegaOne} (hc : S.Countable) :
    ∃ b : OmegaOne, ∀ u ∈ S, u ≤ b := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨zeroOmegaOne, fun u hu => absurd hu (by simp)⟩
  · obtain ⟨f, hf⟩ := (Set.countable_iff_exists_surjective hne).mp hc
    obtain ⟨b, hb⟩ := sigmaDirected_omegaOne (fun n => (f n : OmegaOne))
    refine ⟨b, fun u hu => ?_⟩
    obtain ⟨n, hn⟩ := hf ⟨u, hu⟩
    have : (f n : OmegaOne) = u := congrArg Subtype.val hn
    exact this ▸ hb n

/-- **Finite-to-one rows force nontriviality** — the classical ZFC engine, machine-
    checked. If one global row `E` matched every level off a finite set, then for each
    `n` the set `{u : E u ≤ n}` would meet every initial segment finitely (finite-to-one
    at that level, plus the finite mismatch), hence be countable, hence bounded by some
    `b_n`; regularity bounds the `b_n` jointly by some `B`, and any level above `B` has
    `E`-value beating every bound — impossible for an `ℕ`-valued `E`. -/
theorem omega1_finiteToOne_not_trivial
    (C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne)
    (hf : FiniteToOne C) : ¬ C.Trivial := by
  rintro ⟨E, hE⟩
  -- each value-bound set meets every initial segment finitely
  have hseg : ∀ (n : Nat) (w : OmegaOne), ({u : OmegaOne | E u ≤ n} ∩ Set.Iio w).Finite := by
    intro n w
    have h2 : {u : OmegaOne | wellIndexOmegaOne.lt u w ∧ E u ≠ C.e w u}.Finite :=
      (finiteP_iff_finite _).mp (hE w)
    refine Set.Finite.subset ((hf w n).union h2) ?_
    rintro u ⟨hEu, hlt⟩
    by_cases hveq : E u = C.e w u
    · exact Or.inl ⟨hlt, hveq ▸ hEu⟩
    · exact Or.inr ⟨wi_lt_iff.mpr hlt, hveq⟩
  -- hence each is bounded
  have hbnd : ∀ n : Nat, ∃ b : OmegaOne, ∀ u : OmegaOne, E u ≤ n → u ≤ b := by
    intro n
    obtain ⟨b, hb⟩ := bounded_of_countable (countable_of_segments_finite (hseg n))
    exact ⟨b, fun u hu => hb u hu⟩
  choose b hb using hbnd
  -- regularity bounds them jointly, and nothing can live above the joint bound
  obtain ⟨B, hB⟩ := sigmaDirected_omegaOne b
  obtain ⟨w, hw⟩ := unbounded_omegaOne B
  exact hw (le_trans (hb (E w) w le_rfl) (hB (E w)))

/-- **The obstruction, unconditional.** A coherent sequence on ω₁ whose rows are
    finite-to-one — Todorcevic's `ρ₁` is the canonical ZFC example (Handbook 1.16) —
    admits no monotone representative system. Where `nontrivial_coherent_no_reps`
    needed nontriviality as an imported hypothesis, this needs only a property of the
    rows that is checkable level by level. -/
theorem omega1_finiteToOne_no_reps
    (C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne)
    (hf : FiniteToOne C) : IsEmpty (TransportCalculus.Reps C) :=
  nontrivial_coherent_no_reps C (omega1_finiteToOne_not_trivial C hf)

/-! ## Theorem B⁻: downward dip systems force triviality

    The dip theorems of the set-theoretic notes (§53) were careful-prose only. This
    section machine-checks the downward one — the first formal dip theorem in the
    program, and the one Theorem Q (the kill of the dense failure mode of
    `(Q-rows-lim)`) rests on.

    A *downward dip system* for a coherent sequence is a finite correction `X μ` at each
    level such that at every top `γ` the total leftover — every coordinate where some
    lower row sits strictly *below* `e_γ` and escapes its own correction — is still
    finite. The theorem says such a system exists only for trivial sequences.

    The proof: call `γ` **honest at ξ** when it is above ξ and neither corrects nor leaks
    there. Honest values are non-increasing in the level (`honest_antitone`), so — ℕ being
    well-ordered — each coordinate with unboundedly many honest levels stabilizes, and
    the coordinates without them are finite (`bad_finite`, by concentrating countably many
    bounds at one level: regularity of ℵ₁ again). The stabilized values trivialize. -/

namespace DownDip

/-- The **downward defect**: coordinates below `μ` where row `μ` sits strictly below
    row `γ`. (The notes' `D⁻(μ,γ)`; the dual of the `D⁺` Theorem B runs on.) -/
def DownDefect (C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne)
    (μ γ : OmegaOne) : Set OmegaOne :=
  {ξ | ξ < μ ∧ C.e μ ξ < C.e γ ξ}

end DownDip

/-- A **downward dip system**: finite per-level corrections whose leftover, unioned over
    *all* lower levels, is still finite at every top. -/
structure DownDip (C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne) where
  X : OmegaOne → Set OmegaOne
  X_finite : ∀ μ, (X μ).Finite
  leftover_finite : ∀ γ : OmegaOne,
    {ξ : OmegaOne | ∃ μ, μ < γ ∧ ξ ∈ DownDip.DownDefect C μ γ ∧ ξ ∉ X μ}.Finite

namespace DownDip

/-- The leftover at a top level. -/
def V {C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne}
    (D : DownDip C) (γ : OmegaOne) : Set OmegaOne :=
  {ξ : OmegaOne | ∃ μ, μ < γ ∧ ξ ∈ DownDefect C μ γ ∧ ξ ∉ D.X μ}

theorem V_finite {C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne}
    (D : DownDip C) (γ : OmegaOne) : (D.V γ).Finite := D.leftover_finite γ

/-- `γ` is **honest at `ξ`** when it lies above `ξ` and neither corrects nor leaks
    there — so its value at `ξ` is one the system takes responsibility for. -/
def Honest {C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne}
    (D : DownDip C) (ξ γ : OmegaOne) : Prop := ξ < γ ∧ ξ ∉ D.X γ ∧ ξ ∉ D.V γ

variable {C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne}

/-- **Honest values are non-increasing in the level.** An increase between two honest
    levels would be a downward defect escaping the lower level's own correction, hence a
    leak at the upper one — which honesty forbids. -/
theorem honest_antitone (D : DownDip C) {ξ μ γ : OmegaOne}
    (hμ : D.Honest ξ μ) (hγ : D.Honest ξ γ) (hlt : μ < γ) : C.e γ ξ ≤ C.e μ ξ := by
  by_contra hcon
  exact hγ.2.2 ⟨μ, hlt, ⟨hμ.1, not_le.mp hcon⟩, hμ.2.1⟩

/-- The coordinates whose honest levels are bounded — the ones the system eventually
    stops vouching for. -/
def Bad (D : DownDip C) : Set OmegaOne := {ξ : OmegaOne | ∃ δ, ∀ γ, D.Honest ξ γ → γ ≤ δ}

/-- **Only finitely many coordinates go permanently unvouched.** If infinitely many did,
    regularity of ℵ₁ would concentrate their bounds — and themselves — below one level;
    above that level none of them is honest, so all of them sit in one level's finite
    correction-plus-leftover. -/
theorem bad_finite (D : DownDip C) : D.Bad.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  have g := hinf.natEmbedding
  choose δ hδ using fun n : Nat => (g n).2
  obtain ⟨a, ha⟩ := sigmaDirected_omegaOne δ
  obtain ⟨b, hb⟩ := sigmaDirected_omegaOne (fun n => ((g n : ↥D.Bad) : OmegaOne))
  obtain ⟨c, hc⟩ := sigmaDirected_omegaOne (fun n => if n = 0 then a else b)
  have hac : a ≤ c := by have := hc 0; simpa using this
  have hbc : b ≤ c := by have := hc 1; simpa using this
  obtain ⟨top, htop⟩ := unbounded_omegaOne c
  have hctop : c < top := not_le.mp htop
  have hmem : ∀ n : Nat, ((g n : ↥D.Bad) : OmegaOne) ∈ D.X top ∪ D.V top := by
    intro n
    have hlt : ((g n : ↥D.Bad) : OmegaOne) < top :=
      lt_of_le_of_lt (le_trans (hb n) hbc) hctop
    by_cases hx : ((g n : ↥D.Bad) : OmegaOne) ∈ D.X top
    · exact Or.inl hx
    · by_cases hv : ((g n : ↥D.Bad) : OmegaOne) ∈ D.V top
      · exact Or.inr hv
      · exact absurd (le_trans (le_trans (hδ n top ⟨hlt, hx, hv⟩) (ha n)) hac)
          (not_le.mpr hctop)
  have hinj : Function.Injective (fun n : Nat => ((g n : ↥D.Bad) : OmegaOne)) :=
    fun m n hmn => g.injective (Subtype.ext hmn)
  exact ((D.X_finite top).union (D.V_finite top)).not_infinite
    (Set.infinite_of_injective_forall_mem hinj hmem)

/-- For a vouched coordinate the honest levels are unbounded. -/
theorem honest_unbounded (D : DownDip C) {ξ : OmegaOne} (h : ξ ∉ D.Bad) (δ : OmegaOne) :
    ∃ γ, D.Honest ξ γ ∧ ¬ γ ≤ δ := by
  by_contra hcon
  refine h ⟨δ, fun γ hγ => ?_⟩
  by_contra hle
  exact hcon ⟨γ, hγ, hle⟩

theorem exists_honest (D : DownDip C) {ξ : OmegaOne} (h : ξ ∉ D.Bad) :
    ∃ γ, D.Honest ξ γ :=
  let ⟨γ, hγ, _⟩ := D.honest_unbounded h ξ; ⟨γ, hγ⟩

/-- The stabilized honest value: the least value any honest level gives the coordinate.
    (Junk `0` at unvouched coordinates — they are finite, so they wash out.) -/
noncomputable def Eval (D : DownDip C) (ξ : OmegaOne) : Nat :=
  sInf {n : Nat | ∃ γ, D.Honest ξ γ ∧ C.e γ ξ = n}

theorem eval_mem (D : DownDip C) {ξ : OmegaOne} (h : ξ ∉ D.Bad) :
    ∃ γ, D.Honest ξ γ ∧ C.e γ ξ = D.Eval ξ := by
  obtain ⟨γ, hγ⟩ := D.exists_honest h
  have hne : {n : Nat | ∃ γ, D.Honest ξ γ ∧ C.e γ ξ = n}.Nonempty :=
    ⟨C.e γ ξ, γ, hγ, rfl⟩
  exact Nat.sInf_mem hne

theorem eval_le (D : DownDip C) {ξ γ : OmegaOne} (hγ : D.Honest ξ γ) :
    D.Eval ξ ≤ C.e γ ξ :=
  Nat.sInf_le ⟨γ, hγ, rfl⟩

/-- A level attaining the stabilized value. -/
noncomputable def att (D : DownDip C) {ξ : OmegaOne} (h : ξ ∉ D.Bad) : OmegaOne :=
  Classical.choose (D.eval_mem h)

theorem att_spec (D : DownDip C) {ξ : OmegaOne} (h : ξ ∉ D.Bad) :
    D.Honest ξ (D.att h) ∧ C.e (D.att h) ξ = D.Eval ξ :=
  Classical.choose_spec (D.eval_mem h)

/-- **Stabilization.** At or above the attaining level every honest level gives the
    stabilized value: `≤` by antitonicity, `≥` by leastness. -/
theorem eval_eq_of_honest (D : DownDip C) {ξ γ : OmegaOne} (h : ξ ∉ D.Bad)
    (hγ : D.Honest ξ γ) (hge : D.att h ≤ γ) : C.e γ ξ = D.Eval ξ := by
  rcases eq_or_lt_of_le hge with heq | hlt
  · rw [← heq]; exact (D.att_spec h).2
  · exact le_antisymm
      (le_trans (D.honest_antitone (D.att_spec h).1 hγ hlt) (le_of_eq (D.att_spec h).2))
      (D.eval_le hγ)

end DownDip

/-- **Theorem B⁻, machine-checked.** A coherent sequence on ω₁ admitting a downward dip
    system is trivial. The dual of the notes' Theorem B — and strictly easier, because a
    non-increasing ℕ-valued family stabilizes for free, where the upward theorem needs a
    witness-concentration argument for unbounded columns. -/
theorem omega1_downDip_trivial
    (C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne)
    (D : DownDip C) : C.Trivial := by
  classical
  refine ⟨D.Eval, fun w => ?_⟩
  rw [finiteP_iff_finite]
  obtain ⟨enum, henum⟩ := countableSegments_omegaOne w
  obtain ⟨s, hs⟩ := sigmaDirected_omegaOne
    (fun n => if h : enum n ∉ D.Bad then D.att h else enum n)
  obtain ⟨p, hp⟩ := sigmaDirected_omegaOne (fun n => if n = 0 then s else w)
  have hsp : s ≤ p := by have := hp 0; simpa using this
  have hwp : w ≤ p := by have := hp 1; simpa using this
  obtain ⟨δ, hδ⟩ := unbounded_omegaOne p
  have hpδ : p < δ := not_le.mp hδ
  have hwδ : w < δ := lt_of_le_of_lt hwp hpδ
  have hcoh : {u : OmegaOne | wellIndexOmegaOne.lt u δ ∧ wellIndexOmegaOne.lt u w ∧
      C.e δ u ≠ C.e w u}.Finite := (finiteP_iff_finite _).mp (C.coh δ w)
  refine Set.Finite.subset
    (((D.bad_finite.union (D.X_finite δ)).union (D.V_finite δ)).union hcoh) ?_
  rintro u ⟨hlt, hne⟩
  by_contra hout
  simp only [Set.mem_union, not_or] at hout
  obtain ⟨⟨⟨hbad, hX⟩, hV⟩, hcohu⟩ := hout
  have hltδ : u < δ := lt_trans (wi_lt_iff.mp hlt) hwδ
  have hhon : D.Honest u δ := ⟨hltδ, hX, hV⟩
  obtain ⟨n, hn⟩ := henum u (le_of_lt (wi_lt_iff.mp hlt))
  have hatt : D.att hbad ≤ δ := by
    have hsn : D.att hbad ≤ s := by
      have h0 := hs n
      rw [hn] at h0
      rwa [dif_pos hbad] at h0
    exact le_trans (le_trans hsn hsp) (le_of_lt hpδ)
  have h1 : C.e δ u = D.Eval u := D.eval_eq_of_honest hbad hhon hatt
  have h2 : C.e δ u = C.e w u := by
    by_contra hd
    exact hcohu ⟨wi_lt_iff.mpr hltδ, hlt, hd⟩
  exact hne (h1 ▸ h2)

/-- The converse (Theorem A's dip, downward): a trivialization *is* a downward dip
    system — correct each level where it departs from the global row, and every
    surviving downward defect at a top is a departure of the global row *there*. -/
noncomputable def DownDip.ofTrivial
    {C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne}
    (h : C.Trivial) : DownDip C := by
  classical
  set E := Classical.choose h with hEdef
  have hE := Classical.choose_spec h
  refine
    { X := fun μ => {ξ : OmegaOne | ξ < μ ∧ C.e μ ξ ≠ E ξ}
      X_finite := fun μ => ?_
      leftover_finite := fun γ => ?_ }
  · refine Set.Finite.subset ((finiteP_iff_finite _).mp (hE μ)) ?_
    rintro ξ ⟨hlt, hne⟩
    exact ⟨wi_lt_iff.mpr hlt, fun hEq => hne hEq.symm⟩
  · refine Set.Finite.subset ((finiteP_iff_finite _).mp (hE γ)) ?_
    rintro ξ ⟨μ, hμγ, ⟨hξμ, hval⟩, hxout⟩
    have heq : C.e μ ξ = E ξ := by
      by_contra hd
      exact hxout ⟨hξμ, hd⟩
    have hlt2 : E ξ < C.e γ ξ := heq ▸ hval
    exact ⟨wi_lt_iff.mpr (lt_trans hξμ hμγ), Nat.ne_of_lt hlt2⟩

/-- **Theorem B⁻ as an equivalence.** A coherent sequence on ω₁ admits a downward dip
    system **iff** it is trivial. (The `←` direction also settles non-vacuity: the
    structure is inhabited exactly on the trivial sequences, so the theorem is not
    quantifying over nothing.) -/
theorem omega1_downDip_iff_trivial
    (C : TransportCalculus.CoherentSeq OmegaOne wellIndexOmegaOne) :
    Nonempty (DownDip C) ↔ C.Trivial :=
  ⟨fun ⟨D⟩ => omega1_downDip_trivial C D, fun h => ⟨DownDip.ofTrivial h⟩⟩

end TransportKernel
