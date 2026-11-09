/-
  RC-02 step 5: `sodium_add`, read from libsodium's text by the front end, is this L program, and it is constant time with its output.

  `sodiumAdd` is written by hand, from `RC-02-READING` §3, and `read_add` checks by `decide` that the front end's reading of `utils.c`'s
  lines 313 to 318 and 355 to 360 (pinned by `CSrc`) is exactly it. The reading itself is believed only by testing against clang, in step 6.
-/
import LCore.Slice2.CFront
import LCore.Slice2.CTOut

namespace LCore.Slice2.Add

open Slice (W64 Expr Op)
open Ops (lit)
open For (forN)

set_option maxRecDepth 100000

def aW : List String := ["a0", "a1", "a2", "a3"]
def bW : List String := ["b0", "b1", "b2", "b3"]

/-- **`sodium_add` at length 32, in L**: `c := 0`; 32 rounds, `i = 32 - #c`, each `c := c + (a[i] + b[i]); a[i] := c & 255; c := c >> 8`;
    then `a` is written out, and the result is 0, for a `void` function. -/
def sodiumAdd : Prog where
  inputs := aW ++ bW
  body := .seq (.assign "c" (lit 0))
    (.seq (forN "#c" (lit 32)
      (.seq (.assign "i" (.bin .sub (lit 32) (.var "#c")))
        (.seq (.loadB "ta" aW (.var "i"))
          (.seq (.loadB "tb" bW (.var "i"))
            (.seq (.assign "c" (.add (.var "c") (.add (.var "ta") (.var "tb"))))
              (.seq (.storeB aW (.var "i") (.bin .and (.var "c") (lit 255)))
                (.assign "c" (.shr (.var "c") 8))))))))
      (.emitB aW))
  ret := lit 0

/-- **The program certified is the one read from the C text.** -/
theorem read_add : CFront.readAdd CSrc.addC = some sodiumAdd := by decide +kernel

/-- Both arrays are secret: words 0 to 7. -/
def sec8 (k : Nat) : Bool := decide (k < 8)

/-- **Constant time with its output, on the source**, and refused by `ctCheck`, whose observer reads the output. -/
theorem add_checks : CT.ctOutCheck sec8 sodiumAdd = true ∧ CT.ctCheck sec8 sodiumAdd = false := by decide

theorem add_ct (E : Type) : Cert.relView (sliceLang E sec8) (sliceLang E sec8).lowIn CT.noOut sodiumAdd :=
  CT.ctOutCheck_relView add_checks.1

/-- **So `sodium_add`, as read from its text, is constant time on the source with its output.** -/
theorem addC_ct (E : Type) :
    ∃ p, CFront.readAdd CSrc.addC = some p ∧ Cert.relView (sliceLang E sec8) (sliceLang E sec8).lowIn CT.noOut p :=
  ⟨_, read_add, add_ct E⟩

/-- **It fits the pipeline**: the slots pass and the lowering accept it, for step 6. -/
theorem add_compiles : Slots.fits sodiumAdd = true ∧ Lower.okP (Slots.compile sodiumAdd) = true := by decide

/-- **It adds**: `2^64 - 1 + 1` carries into the second word. Words 0 to 3 are `a`, 4 to 7 are `b`, little-endian. -/
theorem add_carries :
    ((sliceLang Unit sec8).run 500 sodiumAdd
      (fun k => if k = 0 then W64.ofNat (2 ^ 64 - 1) else if k = 4 then W64.ofNat 1 else W64.ofNat 0, ())).ev =
      [.emit "out" ([0, 0, 0, 0, 0, 0, 0, 0, 1] ++ List.replicate 23 0), Slice.retEv (W64.ofNat 0)] := by
  decide +kernel

/-! ## Refused, each where it should be -/

/-- **Refused by the reading**: a write through the `const` parameter, a store index that can pass the end, a body that writes the loop
    index, a shift by 64, and a value returned from a `void` function. Each parses. -/
theorem add_refused_by_reading :
    CFront.readAdd CSrc.addWriteConstC = none ∧ CFront.readAdd CSrc.addStorePastEndC = none ∧
    CFront.readAdd CSrc.addWritesIndexC = none ∧ CFront.readAdd CSrc.addShift64C = none ∧ CFront.readAdd CSrc.addReturnsC = none ∧
    (CFront.parse CSrc.addWriteConstC).isSome = true ∧ (CFront.parse CSrc.addWritesIndexC).isSome = true ∧
    (CFront.parse CSrc.addReturnsC).isSome = true := by
  decide +kernel

/-- **Refused because it is not `void`**: the same body in a function declared `int`. It parses, and only the entry rule refuses it. -/
theorem add_int_refused : (CFront.parse CSrc.addIntC).isSome = true ∧ CFront.readAdd CSrc.addIntC = none := by decide +kernel

/-- **Refused by the reading, the loop's own rules**: a loop that starts at 1, and one whose update names the carry. Each parses. -/
theorem add_loop_refused :
    (CFront.parse CSrc.addStartAt1C).isSome = true ∧ CFront.readAdd CSrc.addStartAt1C = none ∧
    (CFront.parse CSrc.addUpdateOtherC).isSome = true ∧ CFront.readAdd CSrc.addUpdateOtherC = none := by
  decide +kernel

/-- **Refused by the parser**: `+ =` with a space is not C's `+=`. -/
theorem add_spaced_op_refused : CFront.parse CSrc.addSpacedOpC = none := by decide +kernel

/-- **Read, and refused by the certificate**: a store at a secret index, `a[b[i] & 31] = ...`. -/
theorem add_secret_index_refused :
    (CFront.readAdd CSrc.addSecretIndexC).isSome = true ∧ (CFront.readAdd CSrc.addSecretIndexC).map (CT.ctOutCheck sec8) = some false := by
  decide +kernel

/-- **The stated length matters**: at 16 bytes the 32-round loop would pass the end, and is refused; and without the stated `len`, the
    parameter cannot be bound. -/
theorem add_length_matters :
    CFront.readD CSrc.addC CFront.kAdd 16 [(CFront.kLen, 32)] = none ∧ CFront.readD CSrc.addC CFront.kAdd 32 [] = none := by
  decide +kernel

end LCore.Slice2.Add
