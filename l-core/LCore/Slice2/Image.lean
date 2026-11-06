/-
  VS-2 step 7: bytes as a theorem, for a program with a loop, and for one that never finishes. `scanNats` and `spinNats` are the compiled
  programs, written out. Each `..._is_literal` says the pipeline produces exactly that, by kernel evaluation, and each `..._carries` is about the literal.

  **Trust base for a statement about a real run**, as in VS-1: the kernels; the RV model, compared with QEMU on chosen cases and not linked to Sail; the
  ELF wrapper and the loader, that the bytes land where `init` says; QEMU itself. Real hardware is not reached.

  **What it says.** For `scan`, on every input with this secret word and in every environment: the same observation at every fuel. The observation
  includes each address, and those addresses move with the public input (`scan_public_moves_addresses`). There is no instruction budget, because a loop
  bound by a public input has none that holds for every input: `slice_bound` needs a loop-free program.
-/
import LCore.Slice2.OnMachine
import LCore.Slice.Teeth

namespace LCore.Slice2.Image

open Slice (W64 sec0 inp)
open Slice.Rv
open Slice.Slots (encBytes)
open Slice.Lower (fetchI envBusy)
open Slice.Image (low_inp adm_inp)
open Slots (compile)
open Lower (genP pipeline xf)
open OnMachine

set_option maxRecDepth 100000

/-- **Machine leakage as plain numbers**, one to one on the forms the machine emits: a PC `p` is `2p`, an address `a` is `2a + 1`.
    Named apart on purpose. Inside `LCore.Slice2`, a bare `mCode` is the source's (`Slice2/Source.lean`), which sends every PC to 0, and it
    wins over an `open`: this file's first version compared addresses only while saying "trace" (VS-2 log, correction of record). -/
def mCode : Lk → Nat
  | .step [p] => 2 * p
  | .addr (.ofNat a) => 2 * a + 1
  | _ => 0

theorem mCode_pc_addr : mCode (.step [65712]) = 131424 ∧ mCode (.addr (Int.ofNat 131072)) = 262145 := by decide

/-! ## `scan` -/

/-- **The compiled `scan`, as bytes.** -/
def scanNats : List Nat :=
  [183, 3, 2, 0, 3, 180, 131, 0, 35, 176, 131, 64, 3, 180, 3, 64, 99, 4, 4, 6, 3, 180, 3, 64, 19, 116, 244, 3, 51, 4, 132,
   0, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 116, 0, 131, 180, 131, 0, 35, 48, 148, 32, 3, 180, 3, 64, 19, 116, 244, 3, 51,
   4, 132, 0, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 116, 0, 3, 52, 4, 32, 35, 180, 131, 66, 3, 180, 131, 67, 131, 180, 131,
   66, 51, 4, 148, 0, 35, 188, 131, 66, 3, 180, 3, 64, 147, 4, 240, 255, 51, 4, 148, 0, 35, 176, 131, 64, 227, 12, 0, 248,
   3, 180, 131, 67, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]

def scanImage : List Byte := scanNats.map byteOf

theorem scan_are_bytes : scanNats.all (· < 256) = true := by decide

/-- **The compiler's output is the literal**, by kernel evaluation. -/
theorem scan_is_literal : code (genP (compile scan)) = scanImage := by decide

/-- **And it comes out of the certified pipeline.** -/
theorem scan_pipeline_is_literal :
    (pipeline sec0).comp scan = .ok (scanImage, Xform.id.then (xf (compile scan))) := by
  rw [← scan_is_literal]
  exact scan_pipeline

/-- **The fuel is not a constant.** VS-1's was, and could not hold a loop. -/
theorem scan_fuel_tracks (m : Nat) : (Xform.id.then (xf (compile scan))).fuel m = m := rfl

/-- **The literal carries `rel`**, by the kernel's transfer alone: every byte pattern in the secret word, and every environment. -/
theorem scan_carries : Cert.rel (rvLang sec0) scanImage := by
  have h := scan_on_machine
  rwa [scan_is_literal] at h

/-! ## The model's known deviations cannot apply to these bytes -/

/-- The program, instruction by instruction. -/
def scanInsns : List Insn :=
  [ .lui 7 32, .ld 8 7 8, .sd 8 7 1024, .ld 8 7 1024, .beq 8 0 104,
    .ld 8 7 1024, .andi 8 8 63, .add 8 8 8, .add 8 8 8, .add 8 8 8, .add 8 8 7, .ld 9 7 8, .sd 9 8 512,
    .ld 8 7 1024, .andi 8 8 63, .add 8 8 8, .add 8 8 8, .add 8 8 8, .add 8 8 7, .ld 8 8 512, .sd 8 7 1064,
    .ld 8 7 1080, .ld 9 7 1064, .add 8 8 9, .sd 8 7 1080,
    .ld 8 7 1024, .addi 9 0 (-1), .add 8 8 9, .sd 8 7 1024, .beq 0 0 (-104),
    .ld 8 7 1080, .add 10 8 0, .addi 17 0 93, .ecall ]

theorem scan_is_insns : scanImage = code scanInsns := by decide

/-- **Every word decodes to its instruction**, so no word is outside the model. -/
theorem scan_decodes :
    (List.range scanInsns.length).all (fun j =>
      fetchI scanImage (codeBase + 4 * j) == some (scanInsns.getD j .ecall)) = true := by
  decide

/-- **No word is compressed**: each one's low two bits are set, and the machine takes four bytes at every PC. -/
theorem scan_not_compressed :
    (List.range scanInsns.length).all (fun j => (scanNats.getD (4 * j) 0) % 4 == 3) = true := by
  decide

/-- **The only `ecall` is the exit**: it is the last instruction, right after `a7` is set to 93. -/
theorem scan_one_exit :
    (scanInsns.filter (· == .ecall)).length = 1 ∧ scanInsns.getLast? = some .ecall ∧
      scanInsns.getD 32 .ecall = .addi 17 0 93 := by
  decide

/-! ## It computes, and the certificate is not vacuous -/

/-- The run of a literal on two input words. -/
def go (c : List Byte) (e : Env) (n a b : Nat) : Beh := Slice.Rv.run c e n (init c (encBytes (inp a b)) e)

/-- **The literal computes**, and how long it takes depends on the public input: `27 n + 9` instructions on these. -/
theorem scan_runs :
    (go scanImage env0 200 5 3).ev = [Slice.Rv.retEv (W64.ofNat 9)] ∧ (go scanImage env0 200 5 3).cost = 90 ∧
    (go scanImage env0 200 5 2).ev = [Slice.Rv.retEv (W64.ofNat 4)] ∧ (go scanImage env0 200 5 2).cost = 63 ∧
    (go scanImage env0 200 5 0).ev = [Slice.Rv.retEv (W64.ofNat 0)] ∧ (go scanImage env0 200 5 0).cost = 9 := by
  decide +kernel

/-- **The public input really does move the addresses**, so the `rel` above is not about a program whose trace is constant. -/
theorem scan_public_moves_addresses :
    (go scanImage env0 200 5 3).lk.map mCode ≠ (go scanImage env0 200 5 2).lk.map mCode := by
  decide +kernel

/-- **The secret does not**, concretely, in a different environment too. The general statement is `scan_carries`. -/
theorem scan_secret_does_not :
    (go scanImage env0 200 5 3).lk.map mCode = (go scanImage envBusy 200 6 3).lk.map mCode := by
  decide +kernel

/-! ## The theorem depends on these bytes -/

/-- **One byte changed**: the first store's index reads the secret word, not the counter. The PCs stay as they are, so only the address shows it. -/
def tamperedIndex : List Byte := (scanNats.take 23 ++ [0] ++ scanNats.drop 24).map byteOf

theorem tamperedIndex_differs : tamperedIndex ≠ scanImage := by decide

theorem tamperedIndex_addresses_differ :
    ((rvLang sec0).run 14 tamperedIndex (encBytes (inp 1 1), env0)).lk.map mCode ≠
      ((rvLang sec0).run 14 tamperedIndex (encBytes (inp 2 1), env0)).lk.map mCode := by
  decide +kernel

/-- Program counters alone, which do not see this one. -/
def pcOnly : Lk → Nat
  | .step [p] => p
  | _ => 0

theorem tamperedIndex_same_pcs :
    ((rvLang sec0).run 14 tamperedIndex (encBytes (inp 1 1), env0)).lk.map pcOnly =
      ((rvLang sec0).run 14 tamperedIndex (encBytes (inp 2 1), env0)).lk.map pcOnly := by
  decide +kernel

/-- **So the certificate is about these bytes, and sees addresses**: with that byte changed, `rel` is false, through an address alone. -/
theorem tamperedIndex_leaks : ¬ Cert.rel (rvLang sec0) tamperedIndex :=
  fun h => tamperedIndex_addresses_differ
    (congrArg (fun b : Beh => b.lk.map mCode) (h 14 _ _ (adm_inp 1 1) (adm_inp 2 1) (low_inp 1 2 1)))

/-- **One byte changed**: the loop's counter starts from the secret word, not the public one. -/
def tamperedGuard : List Byte := (scanNats.take 6 ++ [3] ++ scanNats.drop 7).map byteOf

theorem tamperedGuard_differs : tamperedGuard ≠ scanImage := by decide

theorem tamperedGuard_costs_differ :
    ((rvLang sec0).run 80 tamperedGuard (encBytes (inp 1 1), env0)).cost ≠
      ((rvLang sec0).run 80 tamperedGuard (encBytes (inp 2 1), env0)).cost := by
  decide +kernel

/-- **With that byte changed, `rel` is false**, through how long it runs. -/
theorem tamperedGuard_leaks : ¬ Cert.rel (rvLang sec0) tamperedGuard :=
  fun h => tamperedGuard_costs_differ
    (congrArg Beh.cost (h 80 _ _ (adm_inp 1 1) (adm_inp 2 1) (low_inp 1 2 1)))

/-! ## `spin` -/

/-- **The compiled `spin`, as bytes.** -/
def spinNats : List Nat :=
  [183, 3, 2, 0, 19, 4, 16, 0, 99, 6, 4, 0, 19, 0, 0, 0, 227, 10, 0, 254, 19, 4, 0, 0, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]

def spinImage : List Byte := spinNats.map byteOf

theorem spin_is_literal : code (genP (compile spin)) = spinImage := by decide

theorem spin_fuel_tracks (m : Nat) : (Xform.id.then (xf (compile spin))).fuel m = m := rfl

/-- **The literal carries `rel`, for a run that does not end.** -/
theorem spin_carries : Cert.rel (rvLang sec0) spinImage := by
  have h := spin_on_machine
  rwa [spin_is_literal] at h

/-- **It never finishes**, at any fuel and in any environment. -/
theorem spin_image_never_finishes (m : Nat) (e : Env) : ((rvLang sec0).run m spinImage (encBytes (inp 5 1), e)).out = .fuel := by
  have h := spin_never_finishes_on_machine m e
  rwa [spin_is_literal] at h

/-- **And it runs**: a loop of three instructions, at a fixed fuel, so "it never finishes" is not a machine that stopped. -/
theorem spin_image_runs : (go spinImage env0 40 5 1).cost = 40 ∧ (go spinImage env0 40 5 1).out = .fuel := by
  decide +kernel

end LCore.Slice2.Image
