/-
  VS-2 step 9: teeth. Compiling is not certifying. The pipeline compiles every program the checker refuses, and each one's literal
  image provably leaks on the machine, through the channel its refusal names: an address, the PCs, the result, or whether and when
  the run finishes. So `slice_carries`'s hypothesis `sliceCheck P p = true` is doing work. `test/refused2_diff.py` runs the same
  bytes under QEMU.

  Each compile is proved once, to a literal, and the machine runs on the literal. Leakage is compared through `Image.mCode`, PCs and addresses, never
  through `DecidableEq Lk` over unevaluated values (VS-2 step 1).
-/
import LCore.Slice2.Image

namespace LCore.Slice2.Teeth

open Slice (W64 sec0 inp)
open Slice.Rv
open Slice.Slots (encBytes)
open Slice.Image (low_inp adm_inp)
open Image (mCode)
open Slots (compile fits)
open Lower (genP okP)

set_option maxRecDepth 100000

/-- The compiled form, by the same two passes, without the checker. -/
def compiled (p : Prog) : List Byte := code (genP (compile p))

/-- **They are all refused, and they all compile**: nothing in the pipeline looks at the secrets. -/
theorem refused_programs_compile :
    sliceCheck sec0 secretLoad = false ∧ fits secretLoad = true ∧ okP (compile secretLoad) = true ∧
    sliceCheck sec0 secretStore = false ∧ fits secretStore = true ∧ okP (compile secretStore) = true ∧
    sliceCheck sec0 secretLoop = false ∧ fits secretLoop = true ∧ okP (compile secretLoop) = true ∧
    sliceCheck sec0 secondIter = false ∧ fits secondIter = true ∧ okP (compile secondIter) = true ∧
    sliceCheck sec0 throughArray = false ∧ fits throughArray = true ∧ okP (compile throughArray) = true ∧
    sliceCheck sec0 arrayInLoop = false ∧ fits arrayInLoop = true ∧ okP (compile arrayInLoop) = true := by
  decide

/-- Refuted by two runs that differ only in the secret, in the leakage. -/
theorem leak_by_lk {c : List Byte} {n a a' b : Nat}
    (hne : ((rvLang sec0).run n c (encBytes (inp a b), env0)).lk.map mCode ≠ ((rvLang sec0).run n c (encBytes (inp a' b), env0)).lk.map mCode) :
    ¬ Cert.rel (rvLang sec0) c :=
  fun h => hne (congrArg (fun r : Beh => r.lk.map mCode) (h n _ _ (adm_inp a b) (adm_inp a' b) (low_inp a a' b)))

/-- **A result as a plain number**: the value returned plus one, and 0 for anything else. The machine emits only `ret` events. Deciding `=` on
    `Ev` lists runs the derived `DecidableEq` over unevaluated values, which ran two kernels out of fuel here (receipt `vs2-step9-export`),
    as `Lk`'s did in step 1. -/
def evCode : Ev → Nat
  | .ext _ [Int.ofNat v] => v + 1
  | _ => 0

theorem evCode_ret : evCode (Slice.Rv.retEv (W64.ofNat 9)) = 10 := by decide

/-- Refuted in the result. -/
theorem leak_by_ev {c : List Byte} {n a a' b : Nat}
    (hne : ((rvLang sec0).run n c (encBytes (inp a b), env0)).ev.map evCode ≠ ((rvLang sec0).run n c (encBytes (inp a' b), env0)).ev.map evCode) :
    ¬ Cert.rel (rvLang sec0) c :=
  fun h => hne (congrArg (fun r : Beh => r.ev.map evCode) (h n _ _ (adm_inp a b) (adm_inp a' b) (low_inp a a' b)))

/-- Refuted in whether the run has finished. -/
theorem leak_by_out {c : List Byte} {n a a' b : Nat}
    (hne : ((rvLang sec0).run n c (encBytes (inp a b), env0)).out ≠ ((rvLang sec0).run n c (encBytes (inp a' b), env0)).out) :
    ¬ Cert.rel (rvLang sec0) c :=
  fun h => hne (congrArg Beh.out (h n _ _ (adm_inp a b) (adm_inp a' b) (low_inp a a' b)))

/-- Refuted in how long it ran. -/
theorem leak_by_cost {c : List Byte} {n a a' b : Nat}
    (hne : ((rvLang sec0).run n c (encBytes (inp a b), env0)).cost ≠ ((rvLang sec0).run n c (encBytes (inp a' b), env0)).cost) :
    ¬ Cert.rel (rvLang sec0) c :=
  fun h => hne (congrArg Beh.cost (h n _ _ (adm_inp a b) (adm_inp a' b) (low_inp a a' b)))

/-! ## A secret index: the address shows it -/

def secretLoadNats : List Nat :=
  [183, 3, 2, 0, 3, 180, 3, 0, 19, 116, 244, 3, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 116, 0, 3, 52, 4, 32, 35, 176, 131, 64,
   19, 4, 0, 0, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]
def secretLoadImage : List Byte := secretLoadNats.map byteOf
theorem secretLoad_literal : compiled secretLoad = secretLoadImage := by decide

theorem secretLoad_compiled_leaks : ¬ Cert.rel (rvLang sec0) (compiled secretLoad) := by
  rw [secretLoad_literal]
  exact leak_by_lk (n := 8) (a := 1) (a' := 2) (b := 1) (by decide +kernel)

def secretStoreNats : List Nat :=
  [183, 3, 2, 0, 3, 180, 3, 0, 19, 116, 244, 3, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 116, 0, 147, 4, 16, 0, 35, 48, 148, 32,
   19, 4, 0, 0, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]
def secretStoreImage : List Byte := secretStoreNats.map byteOf
theorem secretStore_literal : compiled secretStore = secretStoreImage := by decide

theorem secretStore_compiled_leaks : ¬ Cert.rel (rvLang sec0) (compiled secretStore) := by
  rw [secretStore_literal]
  exact leak_by_lk (n := 9) (a := 1) (a' := 2) (b := 1) (by decide +kernel)

/-- **Only the address**: the two runs take the same PCs and the same time, and return the same result. -/
def pcOnly : Lk → Nat
  | .step [p] => p
  | _ => 0

theorem secretStore_same_pcs :
    ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 1 1), env0)).lk.map pcOnly =
      ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 2 1), env0)).lk.map pcOnly := by
  decide +kernel

theorem secretStore_same_cost :
    ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 1 1), env0)).cost =
      ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 2 1), env0)).cost := by
  decide +kernel

theorem secretStore_same_result :
    ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 1 1), env0)).ev.map evCode =
      ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 2 1), env0)).ev.map evCode := by
  decide +kernel

/-- Each part is its own theorem, at the fuel where the run has just finished (13 instructions): two kernels ran out of fuel on the three
    together at fuel 40 (receipt `vs2-step9-export`). -/
theorem secretStore_only_the_address :
    ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 1 1), env0)).lk.map pcOnly =
      ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 2 1), env0)).lk.map pcOnly ∧
    ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 1 1), env0)).cost =
      ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 2 1), env0)).cost ∧
    ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 1 1), env0)).ev.map evCode =
      ((rvLang sec0).run 14 secretStoreImage (encBytes (inp 2 1), env0)).ev.map evCode :=
  ⟨secretStore_same_pcs, secretStore_same_cost, secretStore_same_result⟩

/-! ## A secret loop guard: whether and when it finishes -/

def secretLoopNats : List Nat :=
  [183, 3, 2, 0, 3, 180, 3, 0, 99, 12, 4, 0, 3, 180, 3, 0, 147, 4, 240, 255, 51, 4, 148, 0, 35, 176, 131, 0, 227, 4, 0, 254, 19, 4, 0, 0,
   51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]
def secretLoopImage : List Byte := secretLoopNats.map byteOf
theorem secretLoop_literal : compiled secretLoop = secretLoopImage := by decide

/-- **When**: both finish, after 14 and 21 instructions. -/
theorem secretLoop_when_1 :
    ((rvLang sec0).run 22 secretLoopImage (encBytes (inp 1 1), env0)).out = .done ∧
    ((rvLang sec0).run 22 secretLoopImage (encBytes (inp 1 1), env0)).cost = 14 := by
  decide +kernel

theorem secretLoop_when_2 :
    ((rvLang sec0).run 22 secretLoopImage (encBytes (inp 2 1), env0)).out = .done ∧
    ((rvLang sec0).run 22 secretLoopImage (encBytes (inp 2 1), env0)).cost = 21 := by
  decide +kernel

theorem secretLoop_when :
    ((rvLang sec0).run 22 secretLoopImage (encBytes (inp 1 1), env0)).out = .done ∧
    ((rvLang sec0).run 22 secretLoopImage (encBytes (inp 2 1), env0)).out = .done ∧
    ((rvLang sec0).run 22 secretLoopImage (encBytes (inp 1 1), env0)).cost = 14 ∧
    ((rvLang sec0).run 22 secretLoopImage (encBytes (inp 2 1), env0)).cost = 21 :=
  ⟨secretLoop_when_1.1, secretLoop_when_2.1, secretLoop_when_1.2, secretLoop_when_2.2⟩

/-- **Whether**: at the same fuel one has finished and the other has not, and never will before `2^63` iterations. -/
theorem secretLoop_whether :
    ((rvLang sec0).run 30 secretLoopImage (encBytes (inp 1 1), env0)).out = .done ∧
    ((rvLang sec0).run 30 secretLoopImage (encBytes (inp (2 ^ 63) 1), env0)).out = .fuel := by
  decide +kernel

theorem secretLoop_compiled_leaks_when : ¬ Cert.rel (rvLang sec0) (compiled secretLoop) := by
  rw [secretLoop_literal]
  exact leak_by_cost (n := 22) (a := 1) (a' := 2) (b := 1) (by rw [secretLoop_when.2.2.1, secretLoop_when.2.2.2]; decide)

theorem secretLoop_compiled_leaks_whether : ¬ Cert.rel (rvLang sec0) (compiled secretLoop) := by
  rw [secretLoop_literal]
  exact leak_by_out (n := 30) (a := 1) (a' := 2 ^ 63) (b := 1) (by rw [secretLoop_whether.1, secretLoop_whether.2]; decide)

/-! ## The fixed point: a branch on a secret, on the second iteration only -/

def secondIterNats : List Nat :=
  [183, 3, 2, 0, 19, 4, 0, 0, 35, 176, 131, 64, 19, 4, 32, 0, 35, 180, 131, 64, 3, 180, 131, 64, 99, 10, 4, 2, 3, 180, 3, 64, 99, 6, 4, 0,
   19, 0, 0, 0, 99, 4, 0, 0, 19, 0, 0, 0, 3, 180, 3, 0, 35, 176, 131, 64, 3, 180, 131, 64, 147, 4, 240, 255, 51, 4, 148, 0, 35, 180, 131,
   64, 227, 6, 0, 252, 19, 4, 0, 0, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]
def secondIterImage : List Byte := secondIterNats.map byteOf
theorem secondIter_literal : compiled secondIter = secondIterImage := by decide

/-- The two runs agree until the second iteration's branch, at instruction 22. -/
theorem secondIter_first_iteration_same :
    ((rvLang sec0).run 21 secondIterImage (encBytes (inp 0 1), env0)).lk.map mCode =
      ((rvLang sec0).run 21 secondIterImage (encBytes (inp 5 1), env0)).lk.map mCode := by
  decide +kernel

theorem secondIter_compiled_leaks : ¬ Cert.rel (rvLang sec0) (compiled secondIter) := by
  rw [secondIter_literal]
  exact leak_by_lk (n := 22) (a := 0) (a' := 5) (b := 1) (by decide +kernel)

/-! ## The array's bit: a secret through the array and out -/

def throughArrayNats : List Nat :=
  [183, 3, 2, 0, 19, 4, 0, 0, 19, 116, 244, 3, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 116, 0, 131, 180, 3, 0, 35, 48, 148, 32,
   19, 4, 0, 0, 19, 116, 244, 3, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 116, 0, 3, 52, 4, 32, 35, 180, 131, 64, 3, 180, 131, 64,
   51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]
def throughArrayImage : List Byte := throughArrayNats.map byteOf
theorem throughArray_literal : compiled throughArray = throughArrayImage := by decide

/-- **Only the result**: the same PCs and addresses, and a different value returned. -/
theorem throughArray_only_the_result :
    ((rvLang sec0).run 22 throughArrayImage (encBytes (inp 1 1), env0)).lk.map mCode =
      ((rvLang sec0).run 22 throughArrayImage (encBytes (inp 2 1), env0)).lk.map mCode := by
  decide +kernel

theorem throughArray_compiled_leaks : ¬ Cert.rel (rvLang sec0) (compiled throughArray) := by
  rw [throughArray_literal]
  exact leak_by_ev (n := 22) (a := 1) (a' := 2) (b := 1) (by decide +kernel)

/-! ## The array's bit in a loop -/

def arrayInLoopNats : List Nat :=
  [183, 3, 2, 0, 19, 4, 32, 0, 35, 176, 131, 64, 3, 180, 3, 64, 99, 6, 4, 6, 19, 4, 0, 0, 19, 116, 244, 3, 51, 4,
  132, 0, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4, 116, 0, 3, 52, 4, 32, 35, 180, 131, 64, 3, 180, 131, 64, 99, 6, 4, 0,
  19, 0, 0, 0, 99, 4, 0, 0, 19, 0, 0, 0, 19, 4, 0, 0, 19, 116, 244, 3, 51, 4, 132, 0, 51, 4, 132, 0, 51, 4,
  132, 0, 51, 4, 116, 0, 131, 180, 3, 0, 35, 48, 148, 32, 3, 180, 3, 64, 147, 4, 240, 255, 51, 4, 148, 0, 35, 176, 131, 64,
  227, 10, 0, 248, 19, 4, 0, 0, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]
def arrayInLoopImage : List Byte := arrayInLoopNats.map byteOf
theorem arrayInLoop_literal : compiled arrayInLoop = arrayInLoopImage := by decide

theorem arrayInLoop_compiled_leaks : ¬ Cert.rel (rvLang sec0) (compiled arrayInLoop) := by
  rw [arrayInLoop_literal]
  exact leak_by_lk (n := 42) (a := 0) (a' := 5) (b := 1) (by decide +kernel)

/-! ## And what the checker accepts does not -/

/-- **The same tooling, on an accepted program, finds nothing**, so the refutations above are not the tooling's. -/
theorem scan_same_at_the_same_points :
    ((rvLang sec0).run 42 Image.scanImage (encBytes (inp 0 1), env0)).lk.map mCode =
      ((rvLang sec0).run 42 Image.scanImage (encBytes (inp 5 1), env0)).lk.map mCode ∧
    ((rvLang sec0).run 40 Image.scanImage (encBytes (inp 1 1), env0)).out =
      ((rvLang sec0).run 40 Image.scanImage (encBytes (inp (2 ^ 63) 1), env0)).out := by
  decide +kernel

end LCore.Slice2.Teeth
