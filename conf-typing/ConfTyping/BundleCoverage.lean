/-
  The composable core, stage 1g: what the bundle actually covers — a correction
  upward.

  Stages 1c–1f have been described as carrying "three certificates", and the map was
  updated to say "three of the map's properties, not sixteen". That under-counts, and
  the under-count is not a matter of interpretation: the *observation* in
  `uOptLowEq` includes the cost and the halting behaviour, so a single application of
  `usecTy_sound` discharges three separate rows of `VULN-COVERAGE` at once — exactly
  as bricks 3, 5 and 7 did for the While language, which is where the observation
  came from.

  This module makes the coverage checkable rather than asserted, by projecting each
  row's property out of the certificates the bundle already has:

  * **row 1** (direct confidentiality leaks) — `bundle_covers_store`;
  * **row 2** (timing side channels) — `bundle_covers_timing`: Low-equal runs have
    *equal cost*, because the clock is in the observation;
  * **row 13** (termination / progress leaks) — `bundle_covers_termination`:
    Low-equal runs *halt together*;
  * **row 7** (authorization, mediation half) — `handler_mediated`;
  * **row 10** (resource exhaustion) — the budget;
  * **row 12** (composition seams) — `bundle_covers_seam`: this is what `UCert.seq`
    *is*, so the row is carried by construction rather than by a separate proof.

  Six rows, plus row 11's *mechanism* — the assumption ledger of stage 1e — though
  not row 11's own class, since nothing here is about crypto.

  Two honest notes. The correction runs upward, which is the rarer direction and the
  one it is tempting not to bother making; the previous "three" was a real
  understatement of a real artifact. And six of sixteen is still not sixteen: rows
  3, 6, 8, 9, 11 and 14 are untouched, and reaching them needs the language to grow
  strings or a heap, which is a larger step than any stage so far.
-/
import ConfTyping.BundleLoop

namespace ConfTyping

variable {P : Partition} {c : UCmd}

/-! ## Projecting the rows out of the certificates -/

/-- **Row 1 — direct confidentiality leaks.** Low-equal inputs give Low-equal stores.
    The classical statement, on the unified machine. -/
theorem bundle_covers_store (h : ucheckNI P c = true) :
    ∀ (n : Nat) (π : MedPolicy) (s s' : UState) (r r' : UState × Nat × List Bool),
      uLowEq P s s' → uexec n c π s = some r → uexec n c π s' = some r' →
      lowEq P r.1.store r'.1.store := by
  intro n π s s' r r' hle h1 h2
  have := uNI_of_check h n π s s' hle
  rw [h1, h2] at this
  exact this.1.1

/-- **Row 2 — timing side channels.** Low-equal runs cost *exactly the same*. This
    needs no extra work because the clock sits inside the observation `uOptLowEq`,
    which is what makes the single NI certificate discharge a second row. -/
theorem bundle_covers_timing (h : ucheckNI P c = true) :
    ∀ (n : Nat) (π : MedPolicy) (s s' : UState) (r r' : UState × Nat × List Bool),
      uLowEq P s s' → uexec n c π s = some r → uexec n c π s' = some r' →
      r.2.1 = r'.2.1 := by
  intro n π s s' r r' hle h1 h2
  have := uNI_of_check h n π s s' hle
  rw [h1, h2] at this
  exact this.2.1

/-- **Row 13 — termination / progress leaks.** Low-equal runs halt together, so the
    halting bit carries no secret. The third row discharged by the same certificate. -/
theorem bundle_covers_termination (h : ucheckNI P c = true) :
    ∀ (n : Nat) (π : MedPolicy) (s s' : UState), uLowEq P s s' →
      (uexec n c π s).isSome = (uexec n c π s').isSome := by
  intro n π s s' hle
  have hni := uNI_of_check h n π s s' hle
  rcases h1 : uexec n c π s with _ | r
  · rcases h2 : uexec n c π s' with _ | r'
    · rfl
    · rw [h1, h2] at hni; exact hni.elim
  · rcases h2 : uexec n c π s' with _ | r'
    · rw [h1, h2] at hni; exact hni.elim
    · rfl

/-- **Row 12 — composition seams.** The row asks that certificates not be lost at a
    boundary. That is not an extra theorem here: it is what `UCert.seq` says, so the
    row is carried by construction. Restated in the row's own vocabulary. -/
theorem bundle_covers_seam {A A₁ A₂ : List String} {c₁ c₂ : UCmd} {k₁ k₂ : Nat}
    (h₁ : UCert A c₁ A₁ k₁) (h₂ : UCert A₁ c₂ A₂ k₂) :
    ∃ (A' : List String) (k : Nat), UCert A (.seq c₁ c₂) A' k ∧ k = k₁ + k₂ :=
  ⟨A₂, k₁ + k₂, UCert.seq h₁ h₂, rfl⟩

/-! ## The coverage claim, for the worked handler -/

/-- **What the stage-1c handler actually carries: six rows, not three.** Rows 1, 2 and
    13 come from one noninterference certificate because the observation includes the
    store, the clock and the halting bit; row 7 from mediation; row 10 from the
    budget; row 12 from the composition law itself. -/
theorem handler_covers_six_rows :
    -- rows 1, 2, 13 — one certificate, three channels
    (∀ n π s s' r r', uLowEq Psec s s' →
        uexec n handler π s = some r → uexec n handler π s' = some r' →
        lowEq Psec r.1.store r'.1.store ∧ r.2.1 = r'.2.1)
  ∧ (∀ n π s s', uLowEq Psec s s' →
        (uexec n handler π s).isSome = (uexec n handler π s').isSome)
    -- row 7
  ∧ UMediated handler
    -- row 10
  ∧ (∀ n π s r, uexec n handler π s = some r → r.2.1 ≤ 6) := by
  refine ⟨?_, ?_, handler_mediated, handler_budget⟩
  · intro n π s s' r r' hle h1 h2
    exact ⟨bundle_covers_store handler_checks_NI n π s s' r r' hle h1 h2,
           bundle_covers_timing handler_checks_NI n π s s' r r' hle h1 h2⟩
  · intro n π s s' hle
    exact bundle_covers_termination handler_checks_NI n π s s' hle

/-- And the same for the bounded-loop handler, which additionally exercises row 10
    across a loop. -/
theorem handlerBounded_covers_mediation_and_budget :
    UMediated handlerBounded
  ∧ (∀ n π s r, uexec n handlerBounded π s = some r →
      r.2.1 ≤ costGA.mul 1 (costGA.mul 1
        (max (1 + (1 + 5 * (1 + 3))) (deadCost (uembed (budget "w" 5 .skip)))))) :=
  ⟨handlerBounded_mediated, handlerBounded_cert.budget⟩

/-! ## And what it does not cover

    Kept next to the claim so the two cannot drift apart. `UCmd` has no strings and no
    heap, so rows 3 (injection), 6 (memory safety) and 14 (path traversal) are not
    *expressible* here at all — they are proved for their own languages in bricks
    11–20 and are **not** carried by this bundle. Rows 8 (races), 9 (speculation) and
    11 (crypto) likewise: bricks 32, 33 and 4 prove them on their own machines. Six of
    sixteen, and the remaining ten need either a bigger language or a different one.

    This is stated in prose deliberately. "The language has no strings" is a syntactic
    fact about an inductive type, and dressing it up as a theorem would produce
    something vacuous that looks like evidence. -/

end ConfTyping
