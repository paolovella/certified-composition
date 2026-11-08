/-
  RC-02 step 3: output arrays. `storeB names e v` writes `v`'s low byte into byte `e` of the input words `names`, and `emitB names` emits their
  bytes as `.emit "out"`, one step, in the middle of a run. On the machine `storeB` is one `sb` and `emitB` is one `write(1, buf, len)`.

  The witnesses here are small on purpose: route 2's six kernels check every kernel-evaluated proof again (`backlog/RC-02.md`).
-/
import LCore.Slice2.CT

namespace LCore.Slice2.Out

open Slice (W64 Expr)
open Slice.Rv
open Slots (compile fits)
open Lower (genP okP)
open Ops (lit)
open Bytes (words4 secX src)

set_option maxRecDepth 100000

/-- `x0[1] = 0x41; write(x0)`, returning 0. -/
def put1 : Prog where
  inputs := ["x0"]
  body := .seq (.storeB ["x0"] (lit 1) (lit 0x41)) (.emitB ["x0"])
  ret := lit 0

/-- The word `0x1122334455667788`'s bytes, little-endian, with byte 1 replaced by `0x41`. -/
def put1Out : List Nat := [0x88, 0x41, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11]

/-! ## What it means -/

/-- **On the source**: the output's bytes, then the result. -/
theorem put1_src : (src put1 10 (words4 0x1122334455667788 0 0 0)).ev = [.emit "out" put1Out, Slice.retEv (W64.ofNat 0)] := by decide

/-- **On the machine, the compiled bytes emit the same**, through one `sb` and one `write`. -/
theorem put1_on_machine :
    (Slice.Rv.run (code (genP (compile put1))) env0 100
      (init (code (genP (compile put1))) (Slice.Slots.encBytes (words4 0x1122334455667788 0 0 0)) env0)).ev =
      [.emit "out" put1Out, Slice.retEv (W64.ofNat 0)] := by
  decide +kernel

/-- **An output in the middle of a run**: at fuel 11 the machine has run the `write` and not the exit. It has shown the output, and its run is
    unfinished. This is the case the pass's replay had no way to state before RC-02 (`Lower.ExecE`, `Lower.catch_run`). -/
theorem put1_mid_run :
    (Slice.Rv.run (code (genP (compile put1))) env0 11
      (init (code (genP (compile put1))) (Slice.Slots.encBytes (words4 0x1122334455667788 0 0 0)) env0)).ev = [.emit "out" put1Out] ∧
    (Slice.Rv.run (code (genP (compile put1))) env0 11
      (init (code (genP (compile put1))) (Slice.Slots.encBytes (words4 0x1122334455667788 0 0 0)) env0)).out = .fuel ∧
    (Slice.Rv.run (code (genP (compile put1))) env0 10
      (init (code (genP (compile put1))) (Slice.Slots.encBytes (words4 0x1122334455667788 0 0 0)) env0)).ev = [] := by
  decide +kernel

/-! ## The checker, both ways -/

/-- Only input 0 is secret. -/
def sec0 (k : Nat) : Bool := decide (k = 0)

/-- **Accepted**: a public output. **Refused**: the same output when its word is secret, by `sliceCheck` and by `ctCheck`, whose observer reads
    `"out"`. -/
theorem emit_rules :
    sliceCheck (fun _ => false) put1 = true ∧ sliceCheck secX put1 = false ∧ CT.ctCheck secX put1 = false := by decide

def storeSecret (store : Bool) : Prog where
  inputs := ["x0", "y0"]
  body := .seq (if store then .storeB ["y0"] (lit 0) (.var "x0") else .skip) (.emitB ["y0"])
  ret := lit 0

/-- **A secret byte stored makes the array secret**: `y0` is public until `x0`'s byte is stored in it, and then emitting it is refused. -/
theorem storeSecret_rules : sliceCheck sec0 (storeSecret false) = true ∧ sliceCheck sec0 (storeSecret true) = false := by decide

/-- **Refused**: a store at a secret index, which would show the secret in its address. -/
theorem storeSecretIndex_refused :
    sliceCheck sec0 { inputs := ["x0", "y0"], body := .storeB ["y0"] (.var "x0") (lit 1), ret := lit 0 } = false ∧
    sliceCheck sec0 { inputs := ["x0", "y0"], body := .storeB ["y0"] (lit 3) (lit 1), ret := lit 0 } = true := by decide

/-! ## The lowering's rules, both ways -/

/-- **Refused by the lowering**: words out of order, three of them, an empty output. **Accepted**: two in order, for both commands. -/
theorem out_layout_rules :
    okP (compile { inputs := ["x0", "x1"], body := .storeB ["x1", "x0"] (lit 0) (lit 0), ret := lit 0 }) = false ∧
    okP (compile { inputs := ["x0", "x1", "x2"], body := .storeB ["x0", "x1", "x2"] (lit 0) (lit 0), ret := lit 0 }) = false ∧
    okP (compile { inputs := ["x0", "x1"], body := .storeB ["x0", "x1"] (lit 0) (lit 0), ret := lit 0 }) = true ∧
    okP (compile { inputs := ["x0", "x1"], body := .emitB ["x1", "x0"], ret := lit 0 }) = false ∧
    okP (compile { inputs := ["x0"], body := .emitB [], ret := lit 0 }) = false ∧
    okP (compile { inputs := ["x0", "x1"], body := .emitB ["x0", "x1"], ret := lit 0 }) = true := by
  decide

end LCore.Slice2.Out
