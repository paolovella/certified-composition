/-
  RC-01 step 6: `crypto_verify_16`, as read from libsodium's text, constant time and with a constant budget on its literal RV64 image, by the
  kernel's transfers alone.

  `verify16_ct_bytes` is `relView_transfer` applied to `CT.verify16_ct`, and its `hR` is the pass's own `low_cover`. `verify16_bound_bytes`
  is `bound_transfer` applied to a constant source budget. No proof here is about the machine's instructions: those are the passes' (VS-2,
  RC-01 steps 2 and 3).

  **What this says**, with the model, the hardware contract and the reading of C as the trusted base (`backlog/RC-01.md`, "The claim,
  exactly"): on every pair of inputs whose public bytes agree, here none, since all 32 are secret, and in every environment, at every fuel, the
  image's PCs, addresses, instruction count and outcome are equal, whatever the two arrays hold.
-/
import LCore.Slice2.CFront
import LCore.Slice2.BoundBytes

namespace LCore.Slice2.CTBytes

open Slice (W64)
open Slice.Rv
open Slice.Slots (encBytes)
open Slots (compile fits)
open Lower (genP okP xf pipeline)
open OnMachine (pipeline_comp)
open Bytes (verify16 secX words4)

set_option maxRecDepth 100000

def verify16Nats : List Nat :=
  [183, 3, 2, 0, 19, 4, 0, 0, 35, 176, 131, 64, 19, 4, 0, 1, 35, 180, 131, 64, 3, 180, 131, 64, 99, 4, 4, 6, 19, 4,
  0, 1, 131, 180, 131, 64, 51, 4, 148, 64, 35, 184, 131, 64, 3, 180, 3, 65, 19, 116, 244, 0, 51, 4, 116, 0, 3, 68, 4, 0,
  35, 188, 131, 64, 3, 180, 3, 65, 19, 116, 244, 0, 51, 4, 116, 0, 3, 68, 4, 1, 35, 184, 131, 66, 3, 180, 3, 64, 131, 180,
  131, 65, 3, 181, 3, 67, 179, 196, 164, 0, 51, 100, 148, 0, 35, 176, 131, 64, 3, 180, 131, 64, 147, 4, 240, 255, 51, 4, 148, 0,
  35, 180, 131, 64, 227, 12, 0, 248, 19, 4, 16, 0, 131, 180, 3, 64, 19, 5, 16, 0, 179, 132, 164, 64, 147, 212, 132, 0, 51, 116,
  148, 0, 147, 4, 16, 0, 51, 4, 148, 64, 35, 180, 131, 68, 3, 180, 131, 68, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]

/-- **The image**: 180 bytes, 45 instructions. -/
def verify16Image : List Byte := verify16Nats.map byteOf

theorem verify16_is_literal : code (genP (compile verify16)) = verify16Image := by decide

theorem verify16_pipeline : (pipeline secX).comp verify16 = .ok (verify16Image, Xform.id.then (xf (compile verify16))) := by
  rw [← verify16_is_literal]
  exact pipeline_comp secX Bytes.verify16_ok.1 Bytes.verify16_ok.2

/-! ## Constant time, on the bytes -/

/-- **`crypto_verify_16`'s image is constant time on the machine**: for every two inputs agreeing on the public bytes and every environment,
    at every fuel, the same PCs, addresses, cost and outcome. By the transfer alone. -/
theorem verify16_ct_bytes : Cert.relView (rvLang secX) (rvLang secX).lowIn CT.noRet verify16Image :=
  (pipeline secX).relView_transfer verify16_pipeline (pipeline secX).low_cover (CT.verify16_ct _)

/-- **And it is the image of the function read from the C text**: the front end's output, compiled, is these bytes. -/
theorem verify16C_ct_bytes :
    ∃ p, CFront.read16 CSrc.verify16C = some p ∧ (pipeline secX).comp p = .ok (verify16Image, Xform.id.then (xf (compile verify16))) ∧
      Cert.relView (rvLang secX) (rvLang secX).lowIn CT.noRet verify16Image :=
  ⟨_, CFront.read_verify16, verify16_pipeline, verify16_ct_bytes⟩

/-! ## A constant budget, on the bytes -/

theorem verify16_counted : Budget.counted verify16 = true := by decide

/-- **The source budget does not depend on the input**: 100 steps. -/
theorem verify16_budget_const (i : Nat → W64) : Budget.budget verify16 i = 100 := by
  simp [Budget.budget, verify16, For.forN, Budget.counters, push, Budget.pot, costOf, Slice.upd, Slice.eval, Ops.lit, W64.ofNat,
    Ops.tailE]
  rfl

theorem verify16_bound (E : Type) : Cert.bound (sliceLang E secX) 100 verify16 := by
  refine (Cert.bound_iff_boundR _ _ _).mpr ?_
  intro i hi
  obtain ⟨k, hk, hb⟩ := Budget.slice_boundR E secX verify16_counted i hi
  exact ⟨k, by rw [hk]; exact verify16_budget_const i.1, hb⟩

/-- **A constant budget on the bytes**: 905 instructions, on every input and in every environment. -/
theorem verify16_bound_bytes : Cert.bound (rvLang secX) 905 verify16Image := by
  have h := (pipeline secX).bound_transfer verify16_pipeline (verify16_bound Env)
  have : (Xform.id.then (xf (compile verify16))).cost 100 = 905 := by
    show Lower.stepL (compile verify16) * 100 + Lower.tailC (compile verify16) = 905
    have h1 : Lower.stepL (compile verify16) = 9 := by decide
    have h2 : Lower.tailC (compile verify16) = 5 := by decide
    rw [h1, h2]
  rwa [this] at h

/-! ## On the model, concretely

  Not repeated here. `verify16_ct_bytes` gives the equal traces. `Bytes.verify16_on_machine` gives the two results, 0 and `2^64 - 1`, from the
  same compiled bytes. `test/verify16_diff.py` measures 452 instructions on 92 pairs under QEMU and the model. A kernel witness of three runs
  cost 15 s per kernel check, and every kernel of route 2 checks it again (`backlog/RC-01.md`, step 6's CI).
-/

/-! ## Teeth, on the bytes -/

def earlyExitImage : List Byte := code (genP (compile CT.earlyExit))

/-- **The early exit, compiled, leaks on the machine**: a first byte that differs stops it after 36 instructions, while one that agrees is
    still running at 37. Run to the end, the second takes 59 (`verify16_diff.py` measures both under QEMU). The runs are cut at fuel 37, the
    first at which their costs differ, so the kernel evaluates 73 steps rather than 95, and route 2's six kernels evaluate them again
    (`backlog/RC-01.md`, step 6's CI). Comparing the PC traces instead, which part at fuel 33, timed out in the kernel: deciding equality of
    two leakage lists costs far more than the runs. -/
theorem earlyExit_bytes_leak :
    (Slice.Rv.run earlyExitImage env0 37 (init earlyExitImage (encBytes (words4 1 0 0 0)) env0)).cost ≠
      (Slice.Rv.run earlyExitImage env0 37 (init earlyExitImage (encBytes (words4 0x100 0 0 0)) env0)).cost := by
  decide +kernel

end LCore.Slice2.CTBytes
