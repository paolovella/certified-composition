/-
  RC-01 step 3: byte arrays as inputs, read by `loadB`, through both passes to `lbu` on the machine.

  `verify16` is libsodium's `crypto_verify_16` (`RC-01-READING`), written in L by hand: two 16-byte arrays, the input words `x0 x1` and
  `y0 y1`, compared in a counted loop whose index runs up from 0. It is the program step 5's front end must produce. Here it is only run: its
  constant-time certificate is step 4's.
-/
import LCore.Slice2.Ops

namespace LCore.Slice2.Bytes

open Slice (W64 Expr Op)
open Slice.Rv
open Slots (compile fits)
open Lower (genP okP)
open Ops (lit tailE)

set_option maxRecDepth 100000

/-- Four input words. -/
def words4 (a b c d : Nat) : Nat → W64 := fun k =>
  if k = 0 then W64.ofNat a else if k = 1 then W64.ofNat b else if k = 2 then W64.ofNat c else if k = 3 then W64.ofNat d else W64.ofNat 0

/-- The two arrays are secret: words 0 to 3. -/
def secX (k : Nat) : Bool := decide (k < 4)

def src (p : Prog) (n : Nat) (w : Nat → W64) : Beh := (sliceLang Unit secX).run n p (w, ())

/-! ## The byte read -/

/-- `t := x[i]` for a literal `i`. -/
def readX (i : Nat) : Prog := { inputs := ["x0", "x1", "y0", "y1"], body := .loadB "t" ["x0", "x1"] (lit i), ret := .var "t" }

/-- **Byte `i` of the array, little-endian**, and past its 16 bytes the index wraps, so it never reads outside. -/
theorem readX_bytes :
    (src (readX 0) 10 (words4 0x0102030405060708 0x1112131415161718 0 0)).ev.map Teeth.evCode = [0x08 + 1] ∧
    (src (readX 7) 10 (words4 0x0102030405060708 0x1112131415161718 0 0)).ev.map Teeth.evCode = [0x01 + 1] ∧
    (src (readX 8) 10 (words4 0x0102030405060708 0x1112131415161718 0 0)).ev.map Teeth.evCode = [0x18 + 1] ∧
    (src (readX 15) 10 (words4 0x0102030405060708 0x1112131415161718 0 0)).ev.map Teeth.evCode = [0x11 + 1] ∧
    (src (readX 16) 10 (words4 0x0102030405060708 0x1112131415161718 0 0)).ev.map Teeth.evCode = [0x08 + 1] := by
  decide +kernel

/-- **And the bytes on the machine are the same**, through `lbu`. -/
theorem readX_on_machine :
    (Slice.Rv.run (code (genP (compile (readX 0)))) env0 50
      (init (code (genP (compile (readX 0)))) (Slice.Slots.encBytes (words4 0x0102030405060708 0x1112131415161718 0 0)) env0)).ev.map Teeth.evCode = [0x09] ∧
    (Slice.Rv.run (code (genP (compile (readX 15)))) env0 50
      (init (code (genP (compile (readX 15)))) (Slice.Slots.encBytes (words4 0x0102030405060708 0x1112131415161718 0 0)) env0)).ev.map Teeth.evCode = [0x12] := by
  decide +kernel

/-! ## The checker, both ways -/

/-- **Accepted**: a public array at a public index, its byte returned. -/
theorem readPublic_checks :
    sliceCheck (fun _ => false) { inputs := ["x0", "x1"], body := .loadB "t" ["x0", "x1"] (lit 3), ret := .var "t" } = true := by decide

/-- **Refused**: a secret array's byte is secret, so returning it is a leak. -/
theorem readSecret_refused : sliceCheck secX (readX 3) = false := by decide

def secretIndex : Prog where
  inputs := ["x0", "x1", "y0", "y1"]
  body := .seq (.assign "j" (.var "x0")) (.loadB "t" ["y0", "y1"] (.var "j"))
  ret := lit 0

/-- **Refused**: an index that depends on the secret. -/
theorem secretIndex_refused : sliceCheck secX secretIndex = false := by decide

/-- **Refused by the checker**: an array with no words. -/
theorem emptyArray_refused :
    sliceCheck (fun _ => false) { inputs := ["x0"], body := .loadB "t" [] (lit 0), ret := lit 0 } = false := by decide

/-! ## The lowering's rules, both ways -/

/-- **Refused by the lowering**: words out of order, or three of them, which no mask fits. Accepted: one, two, four or eight in order. -/
theorem layout_rules :
    okP (compile { inputs := ["x0", "x1"], body := .loadB "t" ["x1", "x0"] (lit 0), ret := lit 0 }) = false ∧
    okP (compile { inputs := ["x0", "x1", "x2"], body := .loadB "t" ["x0", "x1", "x2"] (lit 0), ret := lit 0 }) = false ∧
    okP (compile { inputs := ["x0", "x1", "x2", "x3"], body := .loadB "t" ["x0", "x1", "x2", "x3"] (lit 0), ret := lit 0 }) = true ∧
    okP (compile { inputs := ["x0", "x1"], body := .loadB "t" ["x1"] (lit 0), ret := lit 0 }) = true := by
  decide

/-! ## `crypto_verify_16`, in L -/

/-- `for (i = 0; i < 16; i++) d |= x[i] ^ y[i]; return (1 & ((d - 1) >> 8)) - 1;`, with the index from `forN`'s counter: `i = 16 - c`. -/
def verify16 : Prog where
  inputs := ["x0", "x1", "y0", "y1"]
  body := .seq (.assign "d" (lit 0))
    (.seq (For.forN "c" (lit 16)
      (.seq (.assign "i" (.bin .sub (lit 16) (.var "c")))
        (.seq (.loadB "tx" ["x0", "x1"] (.var "i"))
          (.seq (.loadB "ty" ["y0", "y1"] (.var "i"))
            (.assign "d" (.bin .or (.var "d") (.bin .xor (.var "tx") (.var "ty"))))))))
      (.assign "r" (tailE (.var "d"))))
  ret := .var "r"

theorem verify16_ok : fits verify16 = true ∧ okP (compile verify16) = true := by decide

/-- **It compares**: 0 for equal arrays, -1 (the word `2^64 - 1`) when they differ in the first byte, the last byte, or every byte. -/
theorem verify16_compares :
    (src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeef 0x1234)).ev.map Teeth.evCode = [1] ∧
    (src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeee 0x1234)).ev.map Teeth.evCode = [2 ^ 64] ∧
    (src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeef (0x1234 + 2 ^ 63))).ev.map Teeth.evCode = [2 ^ 64] ∧
    (src verify16 400 (words4 0 0 (2 ^ 64 - 1) (2 ^ 64 - 1))).ev.map Teeth.evCode = [2 ^ 64] := by
  decide +kernel

/-- **And the compiled bytes compare the same.** -/
theorem verify16_on_machine :
    (Slice.Rv.run (code (genP (compile verify16))) env0 2000
      (init (code (genP (compile verify16))) (Slice.Slots.encBytes (words4 0xdeadbeef 0x1234 0xdeadbeef 0x1234)) env0)).ev.map Teeth.evCode = [1] ∧
    (Slice.Rv.run (code (genP (compile verify16))) env0 2000
      (init (code (genP (compile verify16))) (Slice.Slots.encBytes (words4 0xdeadbeef 0x1234 0xdeadbeee 0x1234)) env0)).ev.map Teeth.evCode = [2 ^ 64] := by
  decide +kernel

/-- **`sliceCheck` refuses it, rightly**: its result depends on the secret by design. Constant time is a different certificate, step 4's. -/
theorem verify16_not_rel : sliceCheck secX verify16 = false := by decide

end LCore.Slice2.Bytes
