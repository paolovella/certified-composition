/-
  When minimality composes, and the exact condition — the positive half of the pair.

  `jcomp_every_entry_inert` showed composition destroying minimality: two components
  verified under the **same** assumptions compose to a base carrying both copies, and
  every entry goes dead. `IndexedBases` repaired that with deduplication. What was never
  asked is the other case, which is the one the repo's central claim is actually about:
  two components certified by **different tools**, whose bases share nothing.

  The answer is that it composes freely, and the condition is sharp.

  ── The statement ──
  Over independent worlds `W₁ × W₂`, with bases `Γ₁ ++ Γ₂` and goal `G₁ ∧ G₂`:

      Minimal Γ₁ G₁ n₁  →  Minimal Γ₂ G₂ n₂
        →  (∃ w₁, Sat (Γ₁ w₁))  →  (∃ w₂, Sat (Γ₂ w₂))
        →  Minimal (Γ₁ ++ Γ₂) (G₁ ∧ G₂) (n₁ + n₂)

  No interaction term, no side condition beyond each base being satisfiable *somewhere*.
  This is the trusted-base analogue of `Bridge.pair_comp_cert`, and the pair it completes
  is worth stating in one place:

  * **`Bridge.pair_comp_cert`** — bundled *guarantees* accumulate componentwise, free.
  * **`minimal_pair`** — bundled *trusted bases* stay minimal componentwise, free, when
    the worlds are independent.
  * **`jcomp_every_entry_inert`** — and both fail within a single world, where the bases
    coincide instead of being independent, until the index is deduplicated.

  So heterogeneity is the easy case for the bill exactly as stage C found it to be for
  the algebra, and homogeneity is the one that needs work. That inverts the intuition the
  whole programme started from.

  ── The satisfiability hypotheses are not decoration ──
  `pair_needs_satisfiability` exhibits two minimal bases whose composite is **not**
  minimal, for no reason but that one of them holds in no world. The witness is the
  predicate applied to its own hypothesis.
-/
import ConfTyping.LoadBearing

namespace ConfTyping

/-! ## Independent worlds -/

/-- Two bases over independent worlds, appended. -/
def pairBase {W₁ W₂ : Type} (mkΓ₁ : W₁ → Ledger) (mkΓ₂ : W₂ → Ledger) :
    W₁ × W₂ → Ledger := fun w => mkΓ₁ w.1 ++ mkΓ₂ w.2

/-- Their goals, conjoined. -/
def pairGoal {W₁ W₂ : Type} (G₁ : W₁ → Prop) (G₂ : W₂ → Prop) :
    W₁ × W₂ → Prop := fun w => G₁ w.1 ∧ G₂ w.2

theorem pairBase_size {W₁ W₂ : Type} {mkΓ₁ : W₁ → Ledger} {mkΓ₂ : W₂ → Ledger}
    {n₁ n₂ : Nat} (h₁ : LedgerSize mkΓ₁ n₁) (h₂ : LedgerSize mkΓ₂ n₂) :
    LedgerSize (pairBase mkΓ₁ mkΓ₂) (n₁ + n₂) := by
  intro w
  show (mkΓ₁ w.1 ++ mkΓ₂ w.2).length = n₁ + n₂
  rw [List.length_append, h₁ w.1, h₂ w.2]

/-! ## The left half: an entry of the first base still bears -/

/-- An entry bearing in the first component still bears in the composite — witnessed by
    the same world for the first factor and *any* satisfying world for the second. -/
theorem loadBearingAt_pair_left {W₁ W₂ : Type} {mkΓ₁ : W₁ → Ledger} {mkΓ₂ : W₂ → Ledger}
    {G₁ : W₁ → Prop} {G₂ : W₂ → Prop} {n₁ i : Nat}
    (hs₁ : LedgerSize mkΓ₁ n₁) (hi : i < n₁)
    (hsat₂ : ∃ w₂, Sat (mkΓ₂ w₂))
    (h : LoadBearingAt mkΓ₁ G₁ i) :
    LoadBearingAt (pairBase mkΓ₁ mkΓ₂) (pairGoal G₁ G₂) i := by
  obtain ⟨w₁, hsat, hgoal⟩ := h
  obtain ⟨w₂, hsat2⟩ := hsat₂
  refine ⟨(w₁, w₂), ?_, ?_⟩
  · show Sat ((mkΓ₁ w₁ ++ mkΓ₂ w₂).eraseIdx i)
    rw [List.eraseIdx_append_of_lt_length (by rw [hs₁ w₁]; exact hi)]
    exact (sat_append _ _).mpr ⟨hsat, hsat2⟩
  · exact fun hg => hgoal hg.1

/-! ## The right half: indices shift by the first base's length -/

theorem loadBearingAt_pair_right {W₁ W₂ : Type} {mkΓ₁ : W₁ → Ledger} {mkΓ₂ : W₂ → Ledger}
    {G₁ : W₁ → Prop} {G₂ : W₂ → Prop} {n₁ j : Nat}
    (hs₁ : LedgerSize mkΓ₁ n₁)
    (hsat₁ : ∃ w₁, Sat (mkΓ₁ w₁))
    (h : LoadBearingAt mkΓ₂ G₂ j) :
    LoadBearingAt (pairBase mkΓ₁ mkΓ₂) (pairGoal G₁ G₂) (n₁ + j) := by
  obtain ⟨w₂, hsat, hgoal⟩ := h
  obtain ⟨w₁, hsat1⟩ := hsat₁
  refine ⟨(w₁, w₂), ?_, ?_⟩
  · show Sat ((mkΓ₁ w₁ ++ mkΓ₂ w₂).eraseIdx (n₁ + j))
    rw [List.eraseIdx_append_of_length_le (by rw [hs₁ w₁]; omega),
        hs₁ w₁, Nat.add_sub_cancel_left]
    exact (sat_append _ _).mpr ⟨hsat1, hsat⟩
  · exact fun hg => hgoal hg.2

/-! ## The theorem -/

/-- **Minimality composes across independent worlds, componentwise and free.** Two
    minimal bases about disjoint concerns append to a minimal base for the conjoined
    goal — the trusted-base analogue of `Bridge.pair_comp_cert`.

    The contrast with `jcomp_every_entry_inert` is the content: there the two components
    ranged over the *same* world and their bases coincided, so every entry was made
    redundant by its twin. Here they cannot interfere, because no world of one factor
    says anything about the other. -/
theorem minimal_pair {W₁ W₂ : Type} {mkΓ₁ : W₁ → Ledger} {mkΓ₂ : W₂ → Ledger}
    {G₁ : W₁ → Prop} {G₂ : W₂ → Prop} {n₁ n₂ : Nat}
    (hsat₁ : ∃ w₁, Sat (mkΓ₁ w₁)) (hsat₂ : ∃ w₂, Sat (mkΓ₂ w₂))
    (h₁ : Minimal mkΓ₁ G₁ n₁) (h₂ : Minimal mkΓ₂ G₂ n₂) :
    Minimal (pairBase mkΓ₁ mkΓ₂) (pairGoal G₁ G₂) (n₁ + n₂) := by
  refine ⟨pairBase_size h₁.1 h₂.1, fun i hi => ?_⟩
  by_cases hlt : i < n₁
  · exact loadBearingAt_pair_left h₁.1 hlt hsat₂ (h₁.2 i hlt)
  · have hge : n₁ ≤ i := Nat.le_of_not_lt hlt
    have hj : i - n₁ < n₂ := by omega
    have : n₁ + (i - n₁) = i := by omega
    exact this ▸ loadBearingAt_pair_right h₁.1 hsat₁ (h₂.2 (i - n₁) hj)

/-! ## The satisfiability hypotheses are load-bearing

A base that holds in no world contributes an entry nothing can satisfy, so no witness for
any *other* entry survives the append. Two minimal bases, one unsatisfiable, composite
not minimal — the predicate applied to its own hypothesis. -/

def okBase : Unit → Ledger := fun _ => [True]
def badBase : Unit → Ledger := fun _ => [False]
def falseGoal : Unit → Prop := fun _ => False

theorem okBase_minimal : Minimal okBase falseGoal 1 :=
  ⟨fun _ => rfl, fun i hi => by
    match i with
    | 0     => exact ⟨(), trivial, id⟩
    | _ + 1 => exact absurd hi (by omega)⟩

theorem badBase_minimal : Minimal badBase falseGoal 1 :=
  ⟨fun _ => rfl, fun i hi => by
    match i with
    | 0     => exact ⟨(), trivial, id⟩
    | _ + 1 => exact absurd hi (by omega)⟩

/-- **And their composite is not.** `badBase` holds in no world, so the first entry has
    no surviving witness — `minimal_pair` without `hsat₂` would be false. -/
theorem pair_needs_satisfiability :
    Minimal okBase falseGoal 1 ∧ Minimal badBase falseGoal 1
  ∧ ¬ Minimal (pairBase okBase badBase) (pairGoal falseGoal falseGoal) 2 := by
  refine ⟨okBase_minimal, badBase_minimal, fun h => ?_⟩
  obtain ⟨w, hsat, hgoal⟩ := h.2 0 (by omega)
  exact hsat.1

/-- The missing hypothesis, isolated: `badBase` is satisfied nowhere. -/
theorem badBase_unsatisfiable : ¬ ∃ w, Sat (badBase w) := by
  rintro ⟨-, h, -⟩; exact h

/-! ## What this settles

    **The pair is complete.** Guarantees bundle componentwise (`Bridge.pair_comp_cert`);
    trusted bases stay minimal componentwise across independent worlds (`minimal_pair`);
    and both notions degenerate inside a single world, where the bases coincide, until
    deduplication removes the duplication (`jcompD_minimal`).

    **And it inverts the expected difficulty.** Stage C found heterogeneous composition
    free in the algebra and costly only at `hmap` — the hypothesis that two certificates
    are about one artifact. The bill behaves the same way: *different* tools compose for
    nothing, and it is the *same* tool applied twice that needs work. The intuition this
    programme started from — that heterogeneity is the hard case — is wrong in both
    layers, for the same structural reason.

    **Not claimed.** `pairBase` puts the two bases over a product of worlds, which is the
    formal content of "the tools' assumptions are independent". Two tools sharing an
    assumption — both trusting the same C semantics, say — are *not* independent in this
    sense, and the theorem says nothing about them. That case is `jcomp`'s, and its repair
    is deduplication over a common index, which two tools do not yet share. -/

end ConfTyping
