/-
  RC-02 step 6: `sodium_add`, as read from libsodium's text, constant time with its output and with a constant budget, on its literal RV64
  image, by the kernel's transfers alone.

  `add_ct_bytes` is `relView_transfer` applied to `Add.add_ct`, with the pass's own `low_cover` as `hR`. `add_bound_bytes` is
  `bound_transfer` applied to a constant source budget. No proof here is about the machine's instructions: those are the passes'.

  **What this says**, with the model, the hardware contract and the reading of C as the trusted base (`backlog/RC-02.md`, "The claim,
  exactly"): on every two inputs, here all 64 bytes secret, in every environment and at every fuel, the image's PCs, addresses, instruction
  count, outcome and every event but the output and the result are the same, whatever the two arrays hold. And it runs at most 1825
  instructions.
-/
import LCore.Slice2.Add
import LCore.Slice2.BoundBytes

namespace LCore.Slice2.AddBytes

open Slice (W64)
open Slice.Rv
open Slice.Slots (encBytes)
open Slots (compile)
open Lower (genP okP xf pipeline)
open OnMachine (pipeline_comp)
open Ops (lit)
open Add (sodiumAdd sec8 aW bW)

set_option maxRecDepth 100000

def addNats : List Nat := [
  183, 3, 2, 0, 19, 4, 0, 0, 35, 176, 131, 64, 19, 4, 0, 2, 35, 180, 131, 64, 3, 180, 131, 64, 99, 8, 4, 8, 19, 4,
  0, 2, 131, 180, 131, 64, 51, 4, 148, 64, 35, 188, 131, 64, 3, 180, 131, 65, 19, 116, 244, 1, 51, 4, 116, 0, 3, 68, 4, 0,
  35, 180, 131, 66, 3, 180, 131, 65, 19, 116, 244, 1, 51, 4, 116, 0, 3, 68, 4, 2, 35, 188, 131, 68, 3, 180, 3, 64, 131, 180,
  131, 66, 3, 181, 131, 69, 179, 132, 164, 0, 51, 4, 148, 0, 35, 176, 131, 64, 3, 180, 131, 65, 19, 116, 244, 1, 51, 4, 116, 0,
  131, 180, 3, 64, 19, 5, 240, 15, 179, 244, 164, 0, 35, 0, 148, 0, 3, 180, 3, 64, 19, 84, 132, 0, 35, 176, 131, 64, 3, 180,
  131, 64, 147, 4, 240, 255, 51, 4, 148, 0, 35, 180, 131, 64, 227, 8, 0, 246, 19, 5, 16, 0, 147, 133, 3, 0, 19, 6, 0, 2,
  147, 8, 0, 4, 115, 0, 0, 0, 19, 4, 0, 0, 51, 5, 4, 0, 147, 8, 208, 5, 115, 0, 0, 0]

/-- **The image**: 204 bytes, 51 instructions. -/
def addImage : List Byte := addNats.map byteOf

theorem add_is_literal : code (genP (compile sodiumAdd)) = addImage := by decide

theorem add_pipeline : (pipeline sec8).comp sodiumAdd = .ok (addImage, Xform.id.then (xf (compile sodiumAdd))) := by
  rw [← add_is_literal]
  exact pipeline_comp sec8 Add.add_compiles.1 Add.add_compiles.2

/-! ## Constant time with its output, on the bytes -/

/-- **`sodium_add`'s image is constant time on the machine, with its output**: for every two inputs agreeing on the public bytes, here none,
    and every environment, at every fuel, the same PCs, addresses, cost, outcome and other events. By the transfer alone. -/
theorem add_ct_bytes : Cert.relView (rvLang sec8) (rvLang sec8).lowIn CT.noOut addImage :=
  (pipeline sec8).relView_transfer add_pipeline (pipeline sec8).low_cover (Add.add_ct _)

/-- **And it is the image of the function read from the C text.** -/
theorem addC_ct_bytes :
    ∃ p, CFront.readAdd CSrc.addC = some p ∧ (pipeline sec8).comp p = .ok (addImage, Xform.id.then (xf (compile sodiumAdd))) ∧
      Cert.relView (rvLang sec8) (rvLang sec8).lowIn CT.noOut addImage :=
  ⟨_, Add.read_add, add_pipeline, add_ct_bytes⟩

/-! ## A constant budget, on the bytes -/

theorem add_counted : Budget.counted sodiumAdd = true := by decide

/-- **The source budget does not depend on the input**: 260 steps. -/
theorem add_budget_const (i : Nat → W64) : Budget.budget sodiumAdd i = 260 := by
  simp [Budget.budget, sodiumAdd, For.forN, Budget.counters, push, Budget.pot, costOf, Slice.upd, Slice.eval, Ops.lit, W64.ofNat]
  rfl

theorem add_bound (E : Type) : Cert.bound (sliceLang E sec8) 260 sodiumAdd := by
  refine (Cert.bound_iff_boundR _ _ _).mpr ?_
  intro i hi
  obtain ⟨k, hk, hb⟩ := Budget.slice_boundR E sec8 add_counted i hi
  exact ⟨k, by rw [hk]; exact add_budget_const i.1, hb⟩

/-- **A constant budget on the bytes**: 1825 instructions, on every input and in every environment. -/
theorem add_bound_bytes : Cert.bound (rvLang sec8) 1825 addImage := by
  have h := (pipeline sec8).bound_transfer add_pipeline (add_bound Env)
  have : (Xform.id.then (xf (compile sodiumAdd))).cost 260 = 1825 := by
    show Lower.stepL (compile sodiumAdd) * 260 + Lower.tailC (compile sodiumAdd) = 1825
    have h1 : Lower.stepL (compile sodiumAdd) = 7 := by decide
    have h2 : Lower.tailC (compile sodiumAdd) = 5 := by decide
    rw [h1, h2]
  rwa [this] at h

/-! ## Teeth, on the bytes -/

/-- **A leaky variant**: the same add, with a branch on the carry after each round. -/
def leaky : Prog :=
  { sodiumAdd with body := .seq (.assign "c" (lit 0)) (.seq (For.forN "#c" (lit 32)
      (.seq (.assign "i" (.bin .sub (lit 32) (.var "#c")))
        (.seq (.loadB "ta" aW (.var "i"))
          (.seq (.loadB "tb" bW (.var "i"))
            (.seq (.assign "c" (.add (.var "c") (.add (.var "ta") (.var "tb"))))
              (.seq (.storeB aW (.var "i") (.bin .and (.var "c") (lit 255)))
                (.seq (.assign "c" (.shr (.var "c") 8)) (.ite (.var "c") (.assign "z" (lit 1)) .skip))))))))
      (.emitB aW)) }

/-- **Refused by `ctOutCheck`**, though it compiles. -/
theorem leaky_refused : CT.ctOutCheck sec8 leaky = false ∧ Slots.fits leaky = true ∧ okP (compile leaky) = true := by decide

def leakyImage : List Byte := code (genP (compile leaky))

def w8 (a b : Nat) : Nat → W64 := fun k => if k = 0 then W64.ofNat a else if k = 4 then W64.ofNat b else W64.ofNat 0

/-- **And its bytes leak**: with a first byte that carries and one that does not, the leakage differs by fuel 43, the branch on the carry
    after the first round. The leakage's length is compared, which the kernel decides fast; equality of two leakage lists is slow to decide
    (RC-01 step 6). -/
theorem leaky_bytes_leak :
    (Slice.Rv.run leakyImage env0 43 (init leakyImage (encBytes (w8 0xff 1)) env0)).lk.length ≠
      (Slice.Rv.run leakyImage env0 43 (init leakyImage (encBytes (w8 0 1)) env0)).lk.length := by
  decide +kernel

end LCore.Slice2.AddBytes
