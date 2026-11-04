/-
  VS-2 step 6: the second slice's programs on the machine, by the kernel's transfer alone.

  `scan`'s addresses move with a public input, and `spin` never finishes. Both carry `rel` on the machine for every byte pattern and every environment.
-/
import LCore.Slice2.Pass

namespace LCore.Slice2.OnMachine

open Slice (W64 sec0 inp)
open Slice.Rv
open Slice.Slots (encBytes)
open Slots (comp compile fits slotPass)
open Lower (genP okP xf compR pipeline slice_carries)

set_option maxRecDepth 100000

/-- What the two passes produce, given that the program fits. -/
theorem pipeline_comp (P : Nat → Bool) {p : Prog} (hf : fits p = true) (hk : okP (compile p) = true) :
    (pipeline P).comp p = .ok (code (genP (compile p)), Xform.id.then (xf (compile p))) := by
  have h1 : comp p = .ok (compile p, Xform.id) := by simp [comp, hf]
  have h2 : compR (compile p) = .ok (code (genP (compile p)), xf (compile p)) := by simp [compR, hk]
  simp only [pipeline, PassCert.seq, slotPass, Lower.rvPass, h1, h2]

/-! ## Literals: the rule that lets a compiled loop count down -/

/-- **Accepted**: `-1`, and the most negative immediate. **Refused**: one past each end, so the rule is not "any literal". -/
theorem literal_rule :
    okP { body := .skip, ret := .lit (W64.ofNat (2 ^ 64 - 1)) } = true ∧
    okP { body := .skip, ret := .lit (W64.ofNat (2 ^ 64 - 2048)) } = true ∧
    okP { body := .skip, ret := .lit (W64.ofNat (2 ^ 64 - 2049)) } = false ∧
    okP { body := .skip, ret := .lit (W64.ofNat 2047) } = true ∧
    okP { body := .skip, ret := .lit (W64.ofNat 2048) } = false := by
  decide

/-! ## `scan`: a loop over the array at a public index -/

theorem scan_ok : okP (compile scan) = true := by decide

theorem scan_pipeline : (pipeline sec0).comp scan = .ok (code (genP (compile scan)), Xform.id.then (xf (compile scan))) :=
  pipeline_comp sec0 (by decide) scan_ok

/-- **`scan`, on the machine.** For every byte pattern and every environment, by the transfer alone. -/
theorem scan_on_machine : Cert.rel (rvLang sec0) (code (genP (compile scan))) :=
  slice_carries scan_checks scan_pipeline

/-- **It computes on the machine what the source computes**, and finishes. -/
theorem scan_runs_on_machine :
    (Slice.Rv.run (code (genP (compile scan))) env0 200 (init (code (genP (compile scan))) (encBytes (inp 5 3)) env0)).ev = [Slice.Rv.retEv (W64.ofNat 9)]
  ∧ (Slice.Rv.run (code (genP (compile scan))) env0 200 (init (code (genP (compile scan))) (encBytes (inp 5 3)) env0)).out = .done := by
  decide +kernel

/-! ## `spin`: a loop that never ends -/

theorem spin_ok : okP (compile spin) = true := by decide

theorem spin_pipeline : (pipeline sec0).comp spin = .ok (code (genP (compile spin)), Xform.id.then (xf (compile spin))) :=
  pipeline_comp sec0 (by decide) spin_ok

/-- **`spin`, on the machine**: the certificate covers a run that does not end. -/
theorem spin_on_machine : Cert.rel (rvLang sec0) (code (genP (compile spin))) :=
  slice_carries spin_checks spin_pipeline

/-- **It never finishes on the machine**, at any fuel and in any environment, because `reflect` would give a source run that finished. -/
theorem spin_never_finishes_on_machine (m : Nat) (e : Env) :
    ((rvLang sec0).run m (code (genP (compile spin))) (encBytes (inp 5 1), e)).out = .fuel := by
  by_cases h : ((rvLang sec0).run m (code (genP (compile spin))) (encBytes (inp 5 1), e)).out = .fuel
  · exact h
  · obtain ⟨n, h1, _⟩ := (pipeline sec0).reflect _ _ _ spin_pipeline m (inp 5 1, e) (fun k hk => Slice.inp_adm 5 1 k hk) h
    have hs : ((sliceLang Env sec0).run n spin (inp 5 1, e)).out = .fuel := by
      cases n with
      | zero => rfl
      | succ n => exact spin_never_finishes n
    rw [hs] at h1
    exact h1.symm

/-- **And it does run**: cost grows with fuel, so "it never finishes" is not a machine that has stopped. -/
theorem spin_steps_on_machine :
    (Slice.Rv.run (code (genP (compile spin))) env0 40 (init (code (genP (compile spin))) (encBytes (inp 5 1)) env0)).cost = 40 := by
  decide +kernel

end LCore.Slice2.OnMachine
