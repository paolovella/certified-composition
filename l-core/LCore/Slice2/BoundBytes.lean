/-
  BOUND-01 step 4: a budget over loops, on literal RV64 bytes, by the kernel's transfers alone.

  VS-2's account recorded that over loops only `rel` reached the bytes. Here `countUp`, a loop counted by its public input, carries `rel` and a
  budget to its literal image: on every admissible input and in every environment, at every fuel, the machine runs at most
  `8 * (4n + 2) + 5` instructions, where `n` is the public word read back from the bytes. `capped` carries a constant budget, plain `bound`.

  **How tight.** The source budget `4n + 2` is exact (`countUp_budget`). `rvPass` charges each source step the largest step any frame can take
  (`xf`: `stepL * c + tailC`, BOUND-01 step 5a), so on the bytes `countUp` is bounded by `32n + 21` and runs `19n + 9`, and `capped` by 97 and runs
  at most 83. *Before step 5a* the transformer charged every step the whole code's length, and the budgets were ~~`26 * (4n + 2) + 26`~~ and
  ~~672~~: sound, and five to eight times loose.
-/
import LCore.Slice2.Budget

namespace LCore.Slice2.BoundBytes

open Slice (W64 sec0 inp)
open Slice.Rv
open Slice.Slots (encBytes wordAt wordAt_enc)
open Slots (compile fits)
open Lower (genP okP xf pipeline slice_carries)
open OnMachine (pipeline_comp)
open For (countUp capped countUp_checks capped_checks)
open Budget (budget slice_boundR countUp_counted capped_bound)

set_option maxRecDepth 100000

/-! ## `countUp` -/

def countUpNats : List Nat :=
  [183, 3, 2, 0, 3, 180, 131, 0, 35, 176, 131, 64, 3, 180, 3, 64, 99, 4, 4, 4, 3, 180, 3, 64, 19, 116, 244, 3, 51, 4,
  132, 0, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 116, 0, 131, 180, 131, 0, 35, 48, 148, 32, 3, 180, 3, 65, 147, 4, 16, 0,
  51, 4, 148, 0, 35, 184, 131, 64, 3, 180, 3, 64, 147, 4, 240, 255, 51, 4, 148, 0, 35, 176, 131, 64, 227, 12, 0, 250, 3, 180,
  3, 65, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]

def countUpImage : List Byte := countUpNats.map byteOf

theorem countUp_is_literal : code (genP (compile countUp)) = countUpImage := by decide

theorem countUp_pipeline :
    (pipeline sec0).comp countUp = .ok (countUpImage, Xform.id.then (xf (compile countUp))) := by
  rw [← countUp_is_literal]
  exact pipeline_comp sec0 (by decide) (by decide)

/-- The transformer's cost on this program: each step costs at most 8 instructions, and the entry, result and exit 5. -/
theorem countUp_cost (c : Nat) : (Xform.id.then (xf (compile countUp))).cost c = 8 * c + 5 := by
  show Lower.stepL (compile countUp) * c + Lower.tailC (compile countUp) = _
  have h1 : Lower.stepL (compile countUp) = 8 := by decide
  have h2 : Lower.tailC (compile countUp) = 5 := by decide
  rw [h1, h2]

/-- **The source budget, for every input**, proved and not evaluated: `4n + 2`, with `n` the second input word. -/
theorem budget_countUp (i : Nat → W64) : budget countUp i = 4 * (i 1).val + 2 := by
  simp [budget, countUp, For.forN, Budget.counters, push, Budget.pot, costOf, Slice.upd, Slice.eval, Slice.initFrom]
  omega

/-- **`rel` on the bytes**, by transfer alone. -/
theorem countUp_rel_bytes : Cert.rel (rvLang sec0) countUpImage := slice_carries countUp_checks countUp_pipeline

/-- **`boundR` on the bytes**, by transfer alone. -/
theorem countUp_boundR_bytes : Cert.boundR (rvLang sec0) ((pipeline sec0).liftR (Xform.id.then (xf (compile countUp)))
    (fun i k => k = budget countUp i.1)) countUpImage :=
  (pipeline sec0).boundR_transfer countUp_pipeline (slice_boundR Env sec0 countUp_counted)

/-- **The budget, read off the bytes.** On every admissible input and in every environment, at every fuel, the machine runs at most
    `8 * (4n + 2) + 5` instructions, where `n` is the public input word as the bytes hold it. -/
theorem countUp_bytes_budget (u : (rvLang sec0).In) (hu : (rvLang sec0).Adm u) (m : Nat) :
    ((rvLang sec0).run m countUpImage u).cost ≤ 8 * (4 * (wordAt u.1 1).val + 2) + 5 := by
  obtain ⟨k, ⟨i, k', _, henc, hR, hk⟩, hc⟩ := countUp_boundR_bytes u hu
  have hu1 : u.1 = encBytes i.1 := by rw [← henc]; rfl
  rw [hu1, wordAt_enc, ← budget_countUp, ← hR, ← countUp_cost, ← hk]
  exact hc m

/-- **Not vacuous, and how tight**: the machine runs 66 instructions at `n = 3` and 199 at `n = 10`, against budgets of 117 and 341. -/
theorem countUp_runs_within :
    (Image.go countUpImage env0 2000 5 3).cost = 66 ∧ (Image.go countUpImage env0 2000 5 10).cost = 199 ∧
    (Image.go countUpImage env0 2000 5 3).out = .done ∧
    8 * (4 * 3 + 2) + 5 = 117 ∧ 8 * (4 * 10 + 2) + 5 = 341 := by
  decide +kernel

/-! ## `capped`: a constant budget on the bytes -/

def cappedNats : List Nat :=
  [183, 3, 2, 0, 19, 4, 64, 0, 35, 176, 131, 64, 3, 180, 131, 0, 35, 180, 131, 64, 3, 180, 3, 64, 99, 4, 4, 4, 3, 180,
  131, 64, 99, 4, 4, 2, 3, 180, 131, 65, 147, 4, 16, 0, 51, 4, 148, 0, 35, 188, 131, 64, 3, 180, 131, 64, 147, 4, 240, 255,
  51, 4, 148, 0, 35, 180, 131, 64, 99, 4, 0, 0, 19, 0, 0, 0, 3, 180, 3, 64, 147, 4, 240, 255, 51, 4, 148, 0, 35, 176,
  131, 64, 227, 12, 0, 250, 3, 180, 131, 65, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]

def cappedImage : List Byte := cappedNats.map byteOf

theorem capped_is_literal : code (genP (compile capped)) = cappedImage := by decide

theorem capped_pipeline :
    (pipeline sec0).comp capped = .ok (cappedImage, Xform.id.then (xf (compile capped))) := by
  rw [← capped_is_literal]
  exact pipeline_comp sec0 (by decide) (by decide)

theorem capped_rel_bytes : Cert.rel (rvLang sec0) cappedImage := slice_carries capped_checks capped_pipeline

/-- **A constant budget on the bytes**, plain `bound`, for every input however large: 97 instructions. -/
theorem capped_bound_bytes : Cert.bound (rvLang sec0) 97 cappedImage := by
  have h := (pipeline sec0).bound_transfer capped_pipeline (capped_bound Env sec0)
  have : (Xform.id.then (xf (compile capped))).cost 23 = 97 := by
    show Lower.stepL (compile capped) * 23 + Lower.tailC (compile capped) = 97
    have h1 : Lower.stepL (compile capped) = 4 := by decide
    have h2 : Lower.tailC (compile capped) = 5 := by decide
    rw [h1, h2]
  rwa [this] at h

/-- The machine runs 83 instructions at the cap and 51 with nothing to do, against the budget of 97. -/
theorem capped_runs_within :
    (Image.go cappedImage env0 2000 5 10).cost = 83 ∧ (Image.go cappedImage env0 2000 5 0).cost = 51 := by
  decide +kernel

end LCore.Slice2.BoundBytes
