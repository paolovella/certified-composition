/-
  RC-01 step 2b: the operators `^ | & -` and `>> k` in the language VS-1 and VS-2 share, through both passes to the bytes.

  `verifyTail` is `crypto_verify_16`'s return expression, `(1 & ((d - 1) >> 8)) - 1`, over a public input `d`: 0 when `d` is 0, else
  `2^64 - 1`, the word whose low 32 bits are the C `int` -1 (`RC-01-READING` §3). It means that in the source, and the compiled bytes compute
  the same.
-/
import LCore.Slice2.BoundBytes

namespace LCore.Slice2.Ops

open Slice (W64 Expr Op sec0 inp)
open Slice.Rv
open Slots (compile fits)
open Lower (genP okP)

set_option maxRecDepth 100000

def lit (n : Nat) : Expr := .lit (W64.ofNat n)

/-- `(1 & ((d - 1) >> 8)) - 1`, with `d` the public input `n`. -/
def tailE (d : Expr) : Expr := .bin .sub (.bin .and (lit 1) (.shr (.bin .sub d (lit 1)) 8)) (lit 1)

def verifyTail : Prog := { inputs := ["s", "n"], body := .assign "r" (tailE (.var "n")), ret := .var "r" }

/-- **Accepted**: it reads only the public word. -/
theorem verifyTail_checks : sliceCheck sec0 verifyTail = true := by decide

def src (p : Prog) (a b : Nat) : Beh := (sliceLang Unit sec0).run 50 p (inp a b, ())

/-- **It means what C says, on the range C gives it**: 0 for `d = 0`, and `2^64 - 1`, the C `int` -1, for `d` from 1 to 255. In C `d` is an or of
    bytes, so it never leaves that range. **Outside it the expression is not an equality test**: at `d = 2^64 - 1` it gives 0. A first draft of this
    witness claimed -1 there, and `decide` refused it. -/
theorem verifyTail_means :
    (src verifyTail 5 0).ev.map Teeth.evCode = [1] ∧
    (src verifyTail 5 1).ev.map Teeth.evCode = [2 ^ 64] ∧
    (src verifyTail 5 255).ev.map Teeth.evCode = [2 ^ 64] ∧
    (src verifyTail 5 (2 ^ 64 - 1)).ev.map Teeth.evCode = [1] := by
  decide +kernel

theorem verifyTail_ok : fits verifyTail = true ∧ okP (compile verifyTail) = true := by decide

/-- **The bytes compute the same.** -/
theorem verifyTail_on_machine :
    (Image.go (code (genP (compile verifyTail))) env0 100 5 0).ev.map Teeth.evCode = [1] ∧
    (Image.go (code (genP (compile verifyTail))) env0 100 5 7).ev.map Teeth.evCode = [2 ^ 64] := by
  decide +kernel

/-- `s ^ n`, `s | n`, `s & n` and `s - n`: each operator, with a secret operand. -/
def mixSecret (o : Op) : Prog := { inputs := ["s", "n"], body := .assign "r" (.bin o (.var "s") (.var "n")), ret := .var "r" }

/-- **Refused**: each operator carries the secret to the result. -/
theorem mixSecret_refused : sliceCheck sec0 (mixSecret .xor) = false ∧ sliceCheck sec0 (mixSecret .or) = false ∧
    sliceCheck sec0 (mixSecret .and) = false ∧ sliceCheck sec0 (mixSecret .sub) = false := by decide

/-- **And a shift does too.** -/
theorem shiftSecret_refused :
    sliceCheck sec0 { inputs := ["s", "n"], body := .assign "r" (.shr (.var "s") 3), ret := .var "r" } = false := by decide

/-- **Each operator, at the source**, on `0xf0` and `0x3c`: `xor` 204, `or` 252, `and` 48, `sub` 180, and `0xf0 >> 4` is 15. -/
theorem ops_values :
    (Slice.eval (.bin .xor (lit 0xf0) (lit 0x3c)) (fun _ => W64.ofNat 0)).val = 204 ∧
    (Slice.eval (.bin .or (lit 0xf0) (lit 0x3c)) (fun _ => W64.ofNat 0)).val = 252 ∧
    (Slice.eval (.bin .and (lit 0xf0) (lit 0x3c)) (fun _ => W64.ofNat 0)).val = 48 ∧
    (Slice.eval (.bin .sub (lit 0xf0) (lit 0x3c)) (fun _ => W64.ofNat 0)).val = 180 ∧
    (Slice.eval (.bin .sub (lit 0x3c) (lit 0xf0)) (fun _ => W64.ofNat 0)).val = 2 ^ 64 - 180 ∧
    (Slice.eval (.shr (lit 0xf0) 4) (fun _ => W64.ofNat 0)).val = 15 := by
  decide

/-- **Refused by the lowering**: a shift by 64 or more is not one `srli`. -/
theorem shift64_refused : okP { body := .set 128 (.shr (.lit (W64.ofNat 1)) 64), ret := .slot 128 } = false := by decide
theorem shift63_accepted : okP { body := .set 128 (.shr (.lit (W64.ofNat 1)) 63), ret := .slot 128 } = true := by decide

end LCore.Slice2.Ops
