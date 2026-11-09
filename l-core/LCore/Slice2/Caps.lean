/-
  CAP-01: the slice's caps that were not the machine's, lifted, each with an accepted and a refused witness at its new edge.

  1. **Locals are numbered among distinct names** (`Slots.uniq`). `fits` counts distinct names against the 128 slots the lowering can give
     locals (`wordsMax = 256`, of which 128 are inputs and the array). Before, slots were numbered by first position in the list of every
     occurrence, and `fits` counted occurrences: 100 straight-line statements over 12 names were refused (S-USABLE S1).
  2. **The image may be up to `dataBase - codeBase` = 65360 bytes.** It was 3000, a constant in the pass proofs, held below what the ELF
     writer could place: the data segment sat at file offset 0x1000, which held code to 3920 bytes. `Rv.elf` now puts it at the first page
     boundary after the code, and every pass proof holds at the new bound unchanged.
  3. **Literals past 12 bits**: `lui` and `addi` for a signed 32-bit value, and those and a `srli` for one shifted right. The compiler keeps
     a plan only if the machine's own functions compute the literal from it (`Slice.Lower.litPlan`), so an RV64 edge where the naive split
     is wrong is refused, not miscompiled.
-/
import LCore.Slice2.OnMachine
import LCore.Slice2.Pass
import LCore.Slice2.Ops

namespace LCore.Slice2.Caps

open Slice (W64 Expr Op)
open Ops (lit)
open Slots (fits allVars uniq)

set_option maxRecDepth 100000

def seqAll : List Cmd → Cmd
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqAll cs)

/-- `x0 + x0 + … + x0`, `n` occurrences of one name. -/
def chain : Nat → Expr
  | 0 => .var "x0"
  | n + 1 => .add (.var "x0") (chain n)

/-- One statement with 401 occurrences of two names: past the old count of 384, and two distinct names. -/
def manyOcc : Prog where
  inputs := ["x0"]
  body := .assign "t" (chain 400)
  ret := .var "t"

/-- 129 names, as literals: the kernel compares string literals fast, and names it builds slowly. -/
def nameList : List String := ["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14", "v15", "v16", "v17", "v18", "v19", "v20", "v21", "v22", "v23", "v24", "v25", "v26", "v27", "v28", "v29", "v30", "v31", "v32", "v33", "v34", "v35", "v36", "v37", "v38", "v39", "v40", "v41", "v42", "v43", "v44", "v45", "v46", "v47", "v48", "v49", "v50", "v51", "v52", "v53", "v54", "v55", "v56", "v57", "v58", "v59", "v60", "v61", "v62", "v63", "v64", "v65", "v66", "v67", "v68", "v69", "v70", "v71", "v72", "v73", "v74", "v75", "v76", "v77", "v78", "v79", "v80", "v81", "v82", "v83", "v84", "v85", "v86", "v87", "v88", "v89", "v90", "v91", "v92", "v93", "v94", "v95", "v96", "v97", "v98", "v99", "v100", "v101", "v102", "v103", "v104", "v105", "v106", "v107", "v108", "v109", "v110", "v111", "v112", "v113", "v114", "v115", "v116", "v117", "v118", "v119", "v120", "v121", "v122", "v123", "v124", "v125", "v126", "v127", "v128"]

/-- The first `n` of them, each assigned once. -/
def names (n : Nat) : Prog where
  inputs := []
  body := seqAll ((nameList.take n).map fun x => .assign x (lit 0))
  ret := lit 0

/-- **Accepted now, refused before**: 402 occurrences of two names fit. The old rule, `128 + (allVars p).length ≤ 512`, refuses them. -/
theorem manyOcc_fits : fits manyOcc = true ∧ decide (128 + (allVars manyOcc).length ≤ 512) = false := by decide

/-- **The new edge, both ways**: 128 distinct locals fit, 129 do not. -/
theorem names_edge : fits (names 128) = true ∧ fits (names 129) = false := by decide +kernel

/-! ## The image's size -/

open Lower (okP okC sC genP)

/-- `n` copies of `slot 128 := slot 128`, two instructions each, then `skip`. -/
def rep : Nat → Slots.SCmd
  | 0 => .skip
  | n + 1 => .seq (.set 128 (.slot 128)) (rep n)

def bigS (n : Nat) : Slots.SProg := { body := rep n, ret := .lit (W64.ofNat 0) }

theorem rep_sC : ∀ n, sC (rep n) = 2 * n + 1
  | 0 => rfl
  | n + 1 => by
    have := rep_sC n
    simp only [rep, sC, Slice.Lower.sE] at this ⊢
    omega

theorem rep_okC : ∀ n, okC (rep n) = true
  | 0 => rfl
  | n + 1 => by
    simp only [rep, okC, rep_okC n, Bool.and_true]
    decide

theorem bigS_okP (n : Nat) : okP (bigS n) = decide (4 * (2 * n + 6) ≤ 65360) := by
  have he : Slice.Lower.okE (Slice.Slots.SExpr.lit (W64.ofNat 0)) 0 = true := by decide
  have hs : Slice.Lower.sE (Slice.Slots.SExpr.lit (W64.ofNat 0)) = 1 := rfl
  simp only [okP, bigS, rep_okC, Lower.genP_length, rep_sC, he, hs, Bool.true_and]
  congr 1
  apply propext
  omega

/-- **The new edge, both ways**: an image of 16340 instructions, 65360 bytes, is accepted, and one of 16342 is refused. By the length
    formula, not by building them. -/
theorem image_edge : okP (bigS 8167) = true ∧ okP (bigS 8168) = false := by
  rw [bigS_okP, bigS_okP]
  decide

/-! ## Literals -/

open Slice.Lower (litLen litPlan pairVal pairOf sint)

/-- **The targets' constants are built**: HChaCha20's four in two instructions each, `0xffffffff` and fe25519's `0x7ffffffffffff` mask in
    three. -/
theorem target_literals :
    litLen (W64.ofNat 0x61707865) = 2 ∧ litLen (W64.ofNat 0x3320646e) = 2 ∧ litLen (W64.ofNat 0x79622d32) = 2 ∧
    litLen (W64.ofNat 0x6b206574) = 2 ∧ litLen (W64.ofNat 0xffffffff) = 3 ∧ litLen (W64.ofNat 0x7ffffffffffff) = 3 := by decide

/-- **The check catches a wrong split**: on RV64 `lui` sign-extends, so `0x7ffff800` split as `lui 0x80000; addi -2048` is
    `0xffffffff7ffff800`. `litPlan` computes that, finds no other plan, and the literal is refused. -/
theorem naive_split_refused :
    pairVal (pairOf (sint (W64.ofNat 0x7ffff800))).1 (pairOf (sint (W64.ofNat 0x7ffff800))).2 = W64.ofNat 0xffffffff7ffff800 ∧
    litPlan (W64.ofNat 0x7ffff800) = none := by decide

end LCore.Slice2.Caps
