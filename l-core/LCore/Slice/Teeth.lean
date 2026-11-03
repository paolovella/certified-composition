/-
  VS-1 step 9: teeth. Compiling is not certifying, and the kernel refuses a pass that misses an input or miscompiles.

  The pipeline compiles what the checker refuses. Four of the five refused programs' compiled forms provably leak on the machine
  model, so `slice_carries`'s hypothesis `sliceCheck P p = some k` is doing work; the fifth is noted below. `test/refused_diff.py`
  runs all five binaries under QEMU, and all five leak.

  No certified pass can pin the environment. That was the rejected option of step 1 for the stack pointer: an attacker who
  controls `argv` reaches inputs a pinned encoding does not. No certified pass can compile `clean` to the tampered bytes.
-/
import LCore.Slice.Image

namespace LCore.Slice.Teeth

open Rv Slots Lower Image

set_option maxRecDepth 100000

/-! ## Compiling is not certifying -/

/-- The compiled form, by the same two passes, without the checker. -/
def compiled (p : Prog) : List Byte := code (genP (compile p))

/-- **They all compile**: nothing in the pipeline looks at the secrets. -/
theorem refused_programs_compile :
    fits secretBranch = true ∧ okP (compile secretBranch) = true ∧
    fits secretRet = true ∧ okP (compile secretRet) = true ∧
    fits laundered = true ∧ okP (compile laundered) = true ∧
    fits oneArm = true ∧ okP (compile oneArm) = true ∧
    fits shadowed = true ∧ okP (compile shadowed) = true := by
  decide

/-- Refuted by two runs that differ only in the secret, in the result. -/
theorem leak_by_ev {c : List Byte} {a a' b : Nat}
    (hne : ((rvLang sec0).run 40 c (encBytes (inp a b), env0)).ev ≠ ((rvLang sec0).run 40 c (encBytes (inp a' b), env0)).ev) :
    ¬ Cert.rel (rvLang sec0) c :=
  fun h => hne (congrArg Beh.ev (h 40 _ _ (adm_inp a b) (adm_inp a' b) (low_inp a a' b)))

/-! Each compile is proved once, to a literal, and the machine runs on the literal. -/

def secretBranchImage : List Byte := ([183, 3, 2, 0, 3, 180, 3, 0, 99, 6, 4, 0, 19, 0, 0, 0, 99, 6, 0, 0, 19, 0, 0, 0, 19, 0, 0, 0, 19, 4, 0, 0, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0] : List Nat).map byteOf

theorem secretBranch_literal : compiled secretBranch = secretBranchImage := by decide

/- **Not proved here: the compiled `secretBranch` leaks on the model.** `decide` on its leakage at fuel 4 is accepted by Lean, the
   paranoid checker and nanoda, and exhausts lean4lean, con-leche and con-ron, on 44 bytes. Why is not understood: `tampered_leaks`
   also has a taken branch and passes, and neither a literal image, nor lower fuel, nor a literal modulus changed it. The gate was left
   alone and the theorem dropped. The leak is shown on the source (`secretBranch_leaks`), and on the real binary by
   `test/refused_diff.py`: the same instruction count, different PCs. -/

def secretRetImage : List Byte := ([183, 3, 2, 0, 19, 0, 0, 0, 3, 180, 3, 0, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0] : List Nat).map byteOf

theorem secretRet_literal : compiled secretRet = secretRetImage := by decide

/-- **A secret result leaks through the result.** -/
theorem secretRet_compiled_leaks : ¬ Cert.rel (rvLang sec0) (compiled secretRet) := by
  rw [secretRet_literal]
  exact leak_by_ev (a := 5) (a' := 6) (b := 1) (by decide)

def launderedImage : List Byte := ([183, 3, 2, 0, 3, 180, 3, 0, 35, 176, 131, 32, 3, 180, 3, 32, 147, 4, 16, 0, 51, 4, 148, 0, 35, 184, 131, 32, 3, 180, 3, 33, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0] : List Nat).map byteOf

theorem laundered_literal : compiled laundered = launderedImage := by decide

theorem laundered_compiled_leaks : ¬ Cert.rel (rvLang sec0) (compiled laundered) := by
  rw [laundered_literal]
  exact leak_by_ev (a := 5) (a' := 6) (b := 1) (by decide)

def oneArmImage : List Byte := ([183, 3, 2, 0, 3, 180, 131, 0, 99, 8, 4, 0, 3, 180, 3, 0, 35, 180, 131, 32, 99, 6, 0, 0, 19, 4, 0, 0, 35, 180, 131, 32, 3, 180, 131, 32, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0] : List Nat).map byteOf

theorem oneArm_literal : compiled oneArm = oneArmImage := by decide

theorem oneArm_compiled_leaks : ¬ Cert.rel (rvLang sec0) (compiled oneArm) := by
  rw [oneArm_literal]
  exact leak_by_ev (a := 5) (a' := 6) (b := 1) (by decide)

def shadowedImage : List Byte := ([183, 3, 2, 0, 19, 0, 0, 0, 3, 180, 3, 0, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0] : List Nat).map byteOf

theorem shadowed_literal : compiled shadowed = shadowedImage := by decide

theorem shadowed_compiled_leaks : ¬ Cert.rel (rvLang sec0) (compiled shadowed) := by
  rw [shadowed_literal]
  exact leak_by_ev (a := 5) (a' := 6) (b := 1) (by decide)

/-! ## The kernel refuses a pass that misses an input -/

/-- An environment no pinned encoding reaches. -/
theorem envBusy_ne : envBusy ≠ env0 := by
  intro h
  have : envBusy.rd 0 = env0.rd 0 := by rw [h]
  simp [envBusy, env0] at this

/-- **No certified pass can pin the environment.** A pass whose encoding always presents one environment misses the target
    inputs an attacker reaches through `argv`, so `cover` cannot hold. -/
theorem no_pass_pins_env {P : Nat → Bool} (pc : PassCert (slotLang Env P) (rvLang P))
    (he : ∀ i, pc.enc i = (i.1, env0)) : False := by
  have hu : (rvLang P).Adm ((fun _ => byteOf 0), envBusy) := fun _ _ => rfl
  obtain ⟨i, _, h⟩ := pc.cover _ hu
  rw [he i] at h
  exact envBusy_ne (congrArg Prod.snd h).symm

/-- **No certified pass can drop an input word.** A pass whose encoding never presents a nonzero byte in the second word misses
    target inputs, even with the environment passed through. -/
theorem no_pass_drops_a_word {P : Nat → Bool} (pc : PassCert (slotLang Env P) (rvLang P))
    (he : ∀ i, (pc.enc i).1 8 = byteOf 0) : False := by
  let u : (Nat → Byte) × Env := (fun off => if off = 8 then byteOf 1 else byteOf 0, env0)
  have hu : (rvLang P).Adm u := by
    intro off hoff
    have hb : Rv.inBytes = 512 := rfl
    have : off ≠ 8 := by omega
    simp [u, this]
  obtain ⟨i, _, h⟩ := pc.cover u hu
  have h8 := he i
  rw [h] at h8
  simp [u, byteOf] at h8

/-! ## The kernel refuses a miscompile -/

/-- **No certified pass can compile `clean` to the tampered bytes**: it would carry `rel` to bytes where it is false. -/
theorem no_pass_miscompiles {t : Xform} (pc : PassCert (sliceLang Env sec0) (rvLang sec0))
    (h : pc.comp clean = .ok (tampered, t)) : False :=
  tampered_leaks (pc.rel_transfer h (clean_rel Env))

end LCore.Slice.Teeth
