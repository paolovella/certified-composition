/-
  VS-1 step 7: bytes as a theorem. `imageNats` is the compiled program, written out. `compile_is_literal` says the pipeline
  produces exactly it, by kernel evaluation, so no compiler run outside the kernel is believed. `image_carries` is about the
  literal, and the rest of this file shows the model's known deviations cannot apply to it.

  **Trust base for a statement about a real run:** the kernels; the RV model, compared with QEMU on chosen cases and not linked
  to Sail; the ELF wrapper and the loader, that the bytes land where `init` says; QEMU itself. Real hardware is not reached.

  **What it says.** For this one program, on every input with these secrets and in every environment: the same observation at
  every fuel, and at most 95 instructions. That budget is what the transformer gives, not a tight one: the program runs 18.
-/
import LCore.Slice.Lower

namespace LCore.Slice.Image

open Rv Slots Lower

/-- **The compiled `clean`, as bytes.** `test/image_diff.py` reads this list from this file. -/
def imageNats : List Nat :=
  [183, 3, 2, 0, 3, 180, 3, 0, 147, 4, 16, 0, 51, 4, 148, 0, 35, 176, 131, 32, 3, 180, 131, 0, 35, 176, 131, 32, 3, 180,
   131, 0, 99, 12, 4, 0, 3, 180, 3, 32, 131, 180, 131, 0, 51, 4, 148, 0, 35, 176, 131, 32, 99, 4, 0, 0, 19, 0, 0, 0, 3,
   180, 3, 32, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]

def cleanImage : List Byte := imageNats.map byteOf

theorem image_are_bytes : imageNats.all (· < 256) = true := by decide

/-- **The compiler's output is the literal**, by kernel evaluation. -/
theorem compile_is_literal : code (genP (compile clean)) = cleanImage := by decide

/-- **And it comes out of the certified pipeline.** -/
theorem pipeline_is_literal :
    (pipeline sec0).comp clean = .ok (cleanImage, Xform.id.then (xf (compile clean))) := by
  rw [← compile_is_literal]
  exact clean_pipeline

theorem budget_value : (Xform.id.then (xf (compile clean))).cost 4 = 95 := by decide

/-- **The literal carries `rel` and a budget**, on the machine model: every byte pattern in the secret word, and every
    environment. -/
theorem image_carries : Cert.rel (rvLang sec0) cleanImage ∧ Cert.bound (rvLang sec0) 95 cleanImage := by
  have h := clean_on_machine
  rw [compile_is_literal, budget_value] at h
  exact h

/-! ## The model's known deviations cannot apply to these bytes -/

/-- The program, instruction by instruction. -/
def cleanInsns : List Insn :=
  [ .lui 7 32, .ld 8 7 0, .addi 9 0 1, .add 8 8 9, .sd 8 7 512, .ld 8 7 8, .sd 8 7 512, .ld 8 7 8, .beq 8 0 24,
    .ld 8 7 512, .ld 9 7 8, .add 8 8 9, .sd 8 7 512, .beq 0 0 8, .addi 0 0 0, .ld 8 7 512, .add 10 8 0, .addi 17 0 93,
    .ecall ]

theorem image_is_insns : cleanImage = code cleanInsns := by decide

set_option maxRecDepth 100000 in
/-- **Every word decodes to its instruction**, so no word is outside the model. -/
theorem image_decodes :
    (List.range cleanInsns.length).all (fun j =>
      fetchI cleanImage (codeBase + 4 * j) == some (cleanInsns.getD j .ecall)) = true := by
  decide

/-- **No word is compressed**: each one's low two bits are set, and the machine takes four bytes at every PC. -/
theorem image_not_compressed :
    (List.range cleanInsns.length).all (fun j =>
      (imageNats.getD (4 * j) 0) % 4 == 3) = true := by
  decide

/-- **The only `ecall` is the exit**: it is the last instruction, right after `a7` is set to 93. -/
theorem image_one_exit :
    (cleanInsns.filter (· == .ecall)).length = 1 ∧ cleanInsns.getLast? = some .ecall ∧
      cleanInsns.getD 17 .ecall = .addi 17 0 93 := by
  decide

/-! ## It computes, and the theorem depends on these bytes -/

/-- **The literal computes**: `(5, 3)` gives 6, in 18 instructions; `(5, 0)` gives 0, in 14. -/
theorem image_runs :
    (Rv.run cleanImage env0 200 (init cleanImage (encBytes (inp 5 3)) env0)).ev = [Rv.retEv (W64.ofNat 6)]
  ∧ (Rv.run cleanImage env0 200 (init cleanImage (encBytes (inp 5 3)) env0)).cost = 18
  ∧ (Rv.run cleanImage env0 200 (init cleanImage (encBytes (inp 5 0)) env0)).ev = [Rv.retEv (W64.ofNat 0)]
  ∧ (Rv.run cleanImage env0 200 (init cleanImage (encBytes (inp 5 0)) env0)).cost = 14 := by
  decide

theorem low_inp (a a' b : Nat) : (rvLang sec0).lowIn (encBytes (inp a b), env0) (encBytes (inp a' b), env0) := by
  intro off hoff
  show encBytes (inp a b) off = encBytes (inp a' b) off
  have hk : off / 8 ≠ 0 := by
    intro h0; rw [h0] at hoff; simp [sec0] at hoff
  simp [encBytes, inp, hk]

theorem adm_inp (a b : Nat) : (rvLang sec0).Adm (encBytes (inp a b), env0) := by
  intro off hoff
  have hb : Rv.inBytes = 512 := rfl
  have h8 : cap ≤ off / 8 := by have : cap = 64 := rfl; omega
  show byteOf ((inp a b (off / 8)).val / 256 ^ (off % 8)) = byteOf 0
  rw [inp_adm a b _ h8]
  simp [W64.ofNat]

/-- **One byte changed**: the branch now reads the secret word and not the public one. -/
def tampered : List Byte :=
  (imageNats.take 30 ++ [3] ++ imageNats.drop 31).map byteOf

theorem tampered_differs : tampered ≠ cleanImage := by decide

/-- **So the certificate is about these bytes**: with that byte changed, `rel` is false. -/
theorem tampered_leaks : ¬ Cert.rel (rvLang sec0) tampered := by
  intro h
  have := h 200 _ _ (adm_inp 0 3) (adm_inp 5 3) (low_inp 0 5 3)
  revert this; decide

end LCore.Slice.Image
