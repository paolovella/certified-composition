/-
  W32-01 part 2: `e << k`, a shift left by a literal amount below 64, in the language VS-1 and VS-2 share, through both passes to the bytes.

  It lowers to one `slli` (`Slice.Lower.genE`), and the bits shifted past 64 are dropped, as on RV64. `rotl` is the 64-bit rotation
  `(n << 5) | (n >> 59)` of a public input: it carries `rel` on the machine by the transfer alone, and computes there what the source does.
  The 32-bit rotation HChaCha20 needs is the same shape, masked (`research/2026-11/W32-01-READING.md`).
-/
import LCore.Slice2.OnMachine
import LCore.Slice2.Ops
import LCore.Slice2.CFront

namespace LCore.Slice2.Shl

open Slice (W64 Expr Op sec0 inp)
open Slice.Rv
open Slice.Slots (encBytes)
open Slots (compile)
open Lower (genP okP xf slice_carries pipeline)
open Ops (lit)

set_option maxRecDepth 100000

/-- **At the source**: `0xf0 << 4` is `0xf00`; `1 << 63` is `2^63`; `3 << 63` is `2^63` too, its top bit dropped; and all ones shifted
    by 32 keeps only the top half. -/
theorem shl_values :
    (Slice.eval (.shl (lit 0xf0) 4) (fun _ => W64.ofNat 0)).val = 0xf00 ∧
    (Slice.eval (.shl (lit 1) 63) (fun _ => W64.ofNat 0)).val = 2 ^ 63 ∧
    (Slice.eval (.shl (lit 3) 63) (fun _ => W64.ofNat 0)).val = 2 ^ 63 ∧
    (Slice.eval (.shl (lit (2 ^ 64 - 1)) 32) (fun _ => W64.ofNat 0)).val = 2 ^ 64 - 2 ^ 32 := by
  decide

/-- **Refused by the lowering**: a shift by 64 or more is not one `slli`. **Accepted** at 63. -/
theorem shl64_refused : okP { body := .set 128 (.shl (.lit (W64.ofNat 1)) 64), ret := .slot 128 } = false := by decide
theorem shl63_accepted : okP { body := .set 128 (.shl (.lit (W64.ofNat 1)) 63), ret := .slot 128 } = true := by decide

/-- **The secret flows through a shift**, so the checker refuses it; the same program over the public input is accepted. -/
theorem shlSecret_refused :
    sliceCheck sec0 { inputs := ["s", "n"], body := .assign "r" (.shl (.var "s") 3), ret := .var "r" } = false ∧
    sliceCheck sec0 { inputs := ["s", "n"], body := .assign "r" (.shl (.var "n") 3), ret := .var "r" } = true := by decide

/-- A 64-bit rotation left by 5 of the public input. -/
def rotl : Prog where
  inputs := ["s", "n"]
  body := .assign "r" (.bin .or (.shl (.var "n") 5) (.shr (.var "n") 59))
  ret := .var "r"

theorem rotl_checks : sliceCheck sec0 rotl = true := by decide
theorem rotl_ok : okP (compile rotl) = true := by decide
theorem rotl_pipeline : (pipeline sec0).comp rotl = .ok (code (genP (compile rotl)), Xform.id.then (xf (compile rotl))) :=
  OnMachine.pipeline_comp sec0 (by decide) rotl_ok

/-- **The lowering uses `slli`**, so the witnesses below are about the new instruction. -/
theorem rotl_uses_slli : (Insn.slli 8 8 5) ∈ genP (compile rotl) := by decide

/-- **`rotl`, on the machine.** For every byte pattern and every environment, by the transfer alone. -/
theorem rotl_on_machine : Cert.rel (rvLang sec0) (code (genP (compile rotl))) :=
  slice_carries rotl_checks rotl_pipeline

/-- **It computes on the machine what the source computes**: `0x8000000000000001` rotated left by 5 is `0x30`. -/
theorem rotl_runs_on_machine :
    (Slice.Rv.run (code (genP (compile rotl))) env0 100
      (init (code (genP (compile rotl))) (encBytes (inp 7 0x8000000000000001)) env0)).ev = [Slice.Rv.retEv (W64.ofNat 0x30)]
  ∧ (Slice.Rv.run (code (genP (compile rotl))) env0 100
      (init (code (genP (compile rotl))) (encBytes (inp 7 0x8000000000000001)) env0)).out = .done := by
  decide +kernel

/-! ## The C front end reads `e << k` -/

section Front
open CFront (lex pE rdE Tok P CE COp Bd kw)

/-- Characters to codes, through the front end's own `kw`, so no `String` lemma enters these witnesses' footprints. -/
def cs (s : List Char) : List Nat := kw s

/-- **One token, `<<`**, and `<` alone is still `<`: a loop's `i < n` lexes as before. -/
theorem lex_shl : lex (cs ['a', '<', '<', '3']) = some [.id (cs ['a']), .sym .shl, .num 3] ∧
    lex (cs ['a', ' ', '<', ' ', '3']) = some [.id (cs ['a']), .sym .lt, .num 3] := by decide

/-- **C's precedence**, both sides: `x ^ y << 3` is `x ^ (y << 3)`, `x << 1 + 2` is `x << (1 + 2)`, and `x << 2 >> 1` is
    `(x << 2) >> 1`, left to right at one level. -/
def shapes : Bool :=
  (match (lex (cs ['x', ' ', '^', ' ', 'y', ' ', '<', '<', ' ', '3'])).bind (pE 40 0) with
    | some (.bin .xor (.var _) (.bin .shl (.var _) (.num 3)), []) => true | _ => false) &&
  (match (lex (cs ['x', ' ', '<', '<', ' ', '1', ' ', '+', ' ', '2'])).bind (pE 40 0) with
    | some (.bin .shl (.var _) (.bin .add (.num 1) (.num 2)), []) => true | _ => false) &&
  (match (lex (cs ['x', ' ', '<', '<', ' ', '2', ' ', '>', '>', ' ', '1'])).bind (pE 40 0) with
    | some (.bin .shr (.bin .shl (.var _) (.num 2)) (.num 1), []) => true | _ => false)

theorem precedence_shl : shapes = true := by decide

/-- **Read by a literal below 64 only**: `x << 3` is `shl x 3`; `x << 64` and `x << y` are refused, not guessed. -/
theorem read_shl :
    rdE [(cs ['x'], .word), (cs ['y'], .word)] none (.bin .shl (.var (cs ['x'])) (.num 3)) [] = some ([], .shl (.var "x") 3, []) ∧
    rdE [(cs ['x'], .word), (cs ['y'], .word)] none (.bin .shl (.var (cs ['x'])) (.num 64)) [] = none ∧
    rdE [(cs ['x'], .word), (cs ['y'], .word)] none (.bin .shl (.var (cs ['x'])) (.var (cs ['y']))) [] = none := by decide

end Front

end LCore.Slice2.Shl
