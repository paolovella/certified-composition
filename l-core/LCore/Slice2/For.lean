/-
  BOUND-01 step 2: the counted loop, as sugar (the user's decision of 2026-11-06, and step 2's design in `backlog/BOUND-01.md`).

  `forN c e b` runs `b` as many times as `e`'s value. `forMax c d N e b` runs it `min (value e) N` times, in exactly `N` rounds, so its running
  time does not depend on `e`. Both are `sliceLang` programs, so the checker, both passes and the bytes are VS-2's, unchanged. The budget each one
  carries is step 3's: here they are only shown to mean what they say, to be accepted, and to compile.
-/
import LCore.Slice2.Teeth

namespace LCore.Slice2.For

open Slice (W64 Expr sec0 inp)
open Slice.Rv
open Slice.Slots (encBytes)
open Slots (compile fits)
open Lower (genP okP)

set_option maxRecDepth 100000

/-- `c := e; while c (b; c := c - 1)`. -/
def forN (c : String) (e : Expr) (b : Cmd) : Cmd :=
  .seq (.assign c e) (.loop (.var c) (.seq b (.assign c (.add (.var c) minusOne))))

/-- `c := N; d := e; while c ((if d then (b; d := d - 1)); c := c - 1)`: always `N` rounds, `b` in the first `min (value e) N`. -/
def forMax (c d : String) (N : Nat) (e : Expr) (b : Cmd) : Cmd :=
  .seq (.assign c (num N)) (.seq (.assign d e)
    (.loop (.var c) (.seq (.ite (.var d) (.seq b (.assign d (.add (.var d) minusOne))) .skip) (.assign c (.add (.var c) minusOne)))))

/-! ## Two programs -/

/-- **Counted by a public input**: store at each index from `n` down to 1, and count the rounds. -/
def countUp : Prog where
  inputs := ["s", "n"]
  body := forN "c" (.var "n") (.seq (.store (.var "c") (.var "n")) (.assign "r" (.add (.var "r") (num 1))))
  ret := .var "r"

/-- **Counted, and capped at 4.** -/
def capped : Prog where
  inputs := ["s", "n"]
  body := forMax "c" "d" 4 (.var "n") (.assign "r" (.add (.var "r") (num 1)))
  ret := .var "r"

/-- **Refused**: counted by the secret, so how long it runs would show it. -/
def countSecret : Prog where
  inputs := ["s", "n"]
  body := forN "c" (.var "s") (.assign "r" (.add (.var "r") (num 1)))
  ret := num 0

theorem countUp_checks : sliceCheck sec0 countUp = true := by decide
theorem capped_checks : sliceCheck sec0 capped = true := by decide
theorem countSecret_refused : sliceCheck sec0 countSecret = false := by decide

/-! ## They mean what they say, in the source -/

def src (p : Prog) (n a b : Nat) : Beh := (sliceLang Unit sec0).run n p (inp a b, ())

/-- **`forN` runs its body `n` times.** -/
theorem countUp_counts :
    (src countUp 100 5 3).ev.map Teeth.evCode = [4] ∧ (src countUp 100 5 0).ev.map Teeth.evCode = [1] ∧
    (src countUp 100 5 3).out = .done := by
  decide +kernel

/-- **`forMax` runs it `min n 4` times**: twice for 2, four times for 10. -/
theorem capped_caps :
    (src capped 100 5 2).ev.map Teeth.evCode = [3] ∧ (src capped 100 5 10).ev.map Teeth.evCode = [5] ∧
    (src capped 100 5 0).ev.map Teeth.evCode = [1] := by
  decide +kernel

/-- **Why the cap is there** (a side agent's note, and the user's decision "1 and 3 together"): counted by a public input of `2^63`, `forN` has not
    finished after 400 steps, and would not for `2^63` rounds. `forMax` with the same input has finished. -/
theorem why_the_cap :
    (src countUp 400 5 (2 ^ 63)).out = .fuel ∧ (src capped 400 5 (2 ^ 63)).out = .done := by
  decide +kernel

/-- **The capped loop's step count does not depend on the input** past the cap. -/
theorem capped_steps_constant_past_the_cap :
    (src capped 100 5 4).cost = (src capped 100 5 10).cost ∧ (src capped 100 5 10).cost = (src capped 100 5 (2 ^ 63)).cost := by
  decide +kernel

/-! ## They compile, with VS-2's passes unchanged -/

theorem countUp_ok : fits countUp = true ∧ okP (compile countUp) = true := by decide
theorem capped_ok : fits capped = true ∧ okP (compile capped) = true := by decide

/-- **And they run on the machine as in the source.** -/
theorem capped_on_machine :
    (Image.go (code (genP (compile capped))) env0 300 5 10).ev.map Teeth.evCode = [5] ∧
    (Image.go (code (genP (compile capped))) env0 300 5 2).ev.map Teeth.evCode = [3] := by
  decide +kernel

theorem countUp_on_machine :
    (Image.go (code (genP (compile countUp))) env0 300 5 3).ev.map Teeth.evCode = [4] := by
  decide +kernel

end LCore.Slice2.For
