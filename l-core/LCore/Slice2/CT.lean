/-
  RC-01 step 4: constant time, as `Cert.relView` with an observer blind to the result.

  `crypto_verify_16` returns whether two secret arrays are equal, so its result depends on the secret by design, and `rel` refuses it. Constant
  time asks less: that the PCs, addresses, instruction count and outcome do not depend on the secret. That is `relView lowIn noRet`, where `noRet`
  reads every channel but the result's. The kernel has the shape, and its transfer (`relView_transfer`), so no kernel change.

  **The proof adds no taint argument.** A program and the same program returning 0 have the same `noRet` view at every fuel (`run_view_ret`),
  and `sliceCheck`'s soundness (`run_same`) gives the second, since its result is public.

  `verify16`'s accumulator `d` is public at the loop head and secret after the body. `highC` took no fixpoint at a loop and refused this, so
  this step gave its loop rule one widening round (`Source.lean`, `loop_inv`).
-/
import LCore.Slice2.Bytes

namespace LCore.Slice2.CT

open Slice (W64 Expr Store tick highInit highE)
open Bytes (verify16 secX words4 src)
open Ops (lit)

set_option maxRecDepth 100000

/-- **The observer for constant time**: every channel but the result's. -/
def noRet : Observer := fun c => decide (c ≠ .ext "ret")

/-- **The constant-time checker**: `sliceCheck`'s taint analysis, without requiring a public result. -/
def ctCheck (P : Nat → Bool) (p : Prog) : Bool := (highC (highInit P p.inputs 0, false) p.body).isSome

theorem tick_view (f : Observer) (l : List Lk) (q : List Nat) (r : Beh) : (tick l q r).view f = tick l q (r.view f) := rfl

/-- **The result is all that a program's `ret` changes, and `noRet` does not read it.** -/
theorem run_view_ret (ret ret' : Expr) : ∀ (n : Nat) (k : List Frame) (s : Store) (a : Arr),
    (run ret n k s a).view noRet = (run ret' n k s a).view noRet := by
  intro n
  induction n with
  | zero =>
    intro k s a
    cases k with
    | nil => rfl
    | cons _ _ => rfl
  | succ m ih =>
    intro k s a
    cases k with
    | nil => rfl
    | cons f k =>
      obtain ⟨c, q⟩ := f
      cases c with
      | skip | assign _ _ | load _ _ | loadB _ _ _ | store _ _ => simp only [run, tick_view, ih]
      | seq c₁ c₂ => exact ih _ _ _
      | ite e c₁ c₂ => simp only [run]; split <;> simp only [tick_view, ih]
      | loop e b => simp only [run]; split <;> simp only [tick_view, ih]

/-- **`ctCheck` gives constant time on the source**, for every admissible input pair that agrees on the public positions, at every fuel. -/
theorem ctCheck_relView {E : Type} {P : Nat → Bool} {p : Prog} (h : ctCheck P p = true) :
    Cert.relView (sliceLang E P) (sliceLang E P).lowIn noRet p := by
  intro n i i' _ _ hl
  simp only [ctCheck, Option.isSome_iff_exists] at h
  obtain ⟨st, hst⟩ := h
  show (run p.ret n _ _ _).view noRet = (run p.ret n _ _ _).view noRet
  rw [run_view_ret p.ret (lit 0), run_view_ret p.ret (lit 0)]
  exact congrArg (Beh.view noRet)
    (run_same n _ _ _ _ _ _ (push_ft p.body [] hst (Sub.refl _) (FT.nil rfl)) ⟨Slice.initFrom_low hl p.inputs 0, fun _ => rfl⟩)

/-! ## `crypto_verify_16`, constant time -/

theorem verify16_ct_checks : ctCheck secX verify16 = true := by decide

/-- **`crypto_verify_16`, in L, is constant time on the source**: on every pair of inputs, whatever the secret arrays hold, at every fuel, the
    PCs, addresses, cost and outcome are the same. -/
theorem verify16_ct (E : Type) : Cert.relView (sliceLang E secX) (sliceLang E secX).lowIn noRet verify16 :=
  ctCheck_relView verify16_ct_checks

/-- **Concretely**: equal arrays and arrays differing in their last byte give different results, and the same leakage and cost. -/
theorem verify16_same_trace_different_result :
    (src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeef 0x1234)).lk.map Image.mCode =
      (src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeef (0x1234 + 2 ^ 63))).lk.map Image.mCode ∧
    (src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeef 0x1234)).cost =
      (src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeef (0x1234 + 2 ^ 63))).cost ∧
    (src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeef 0x1234)).ev.map Teeth.evCode ≠
      (src verify16 400 (words4 0xdeadbeef 0x1234 0xdeadbeef (0x1234 + 2 ^ 63))).ev.map Teeth.evCode := by
  decide +kernel

/-- **So `relView` says what `rel` cannot**: `verify16` has the first and not the second. -/
theorem verify16_not_rel (E : Type) (e : E) : ¬ Cert.rel (sliceLang E secX) verify16 := by
  intro h
  have hadm : ∀ (a b c d : Nat), (sliceLang E secX).Adm (words4 a b c d, e) := by
    intro a b c d k hk
    have : ¬ k < 4 := by simp only [Slice.cap] at hk; omega
    simp only [words4]
    repeat' split
    all_goals first | omega | rfl
  have hlow : (sliceLang E secX).lowIn (words4 0xdeadbeef 0x1234 0xdeadbeef 0x1234, e)
      (words4 0xdeadbeef 0x1234 0xdeadbeef (0x1234 + 2 ^ 63), e) := by
    intro k hk
    have : ¬ k < 4 := by simpa [secX] using hk
    show words4 _ _ _ _ k = words4 _ _ _ _ k
    simp only [words4]
    repeat' split
    all_goals first | omega | rfl
  have he := congrArg (fun b : Beh => b.ev.map Teeth.evCode) (h 400 _ _ (hadm _ _ _ _) (hadm _ _ _ _) hlow)
  exact verify16_same_trace_different_result.2.2 he

/-! ## Refused, and the leak each refusal stops -/

/-- An early exit: stop comparing at the first differing byte, as `memcmp` may. The loop guard reads the secret. -/
def earlyExit : Prog where
  inputs := ["x0", "x1", "y0", "y1"]
  body := .seq (.assign "i" (lit 0))
    (.seq (.assign "d" (lit 0))
      (.loop (.bin .sub (lit 1) (.var "d"))
        (.seq (.loadB "tx" ["x0", "x1"] (.var "i"))
          (.seq (.loadB "ty" ["y0", "y1"] (.var "i"))
            (.seq (.assign "d" (.bin .xor (.var "tx") (.var "ty")))
              (.assign "i" (.bin .sub (.var "i") (lit 18446744073709551615))))))))
  ret := .var "d"

/-- **Refused**: the loop guard depends on the secret. -/
theorem earlyExit_refused : ctCheck secX earlyExit = false := by decide

/-- **And rightly**: arrays differing in their first byte and in their second take different time. -/
theorem earlyExit_leaks :
    (src earlyExit 400 (words4 1 0 0 0)).cost ≠ (src earlyExit 400 (words4 0x100 0 0 0)).cost := by
  decide +kernel

/-- A read at a secret index: a table lookup keyed by a secret byte. -/
def secretLookup : Prog where
  inputs := ["x0", "x1", "y0", "y1"]
  body := .seq (.loadB "j" ["x0", "x1"] (lit 0)) (.loadB "t" ["y0", "y1"] (.var "j"))
  ret := lit 0

/-- **Refused**: the index depends on the secret. -/
theorem secretLookup_refused : ctCheck secX secretLookup = false := by decide

/-- **And rightly**: the address read differs. -/
theorem secretLookup_leaks :
    (src secretLookup 50 (words4 1 0 0 0)).lk.map Image.mCode ≠ (src secretLookup 50 (words4 2 0 0 0)).lk.map Image.mCode := by
  decide +kernel

/-- **`ctCheck` accepts everything `sliceCheck` accepts**, and `verify16`, which `sliceCheck` refuses. -/
theorem sliceCheck_ctCheck (P : Nat → Bool) (p : Prog) (h : sliceCheck P p = true) : ctCheck P p = true := by
  simp only [sliceCheck] at h
  simp only [ctCheck]
  split at h
  · rename_i st hst; rw [hst]; rfl
  · simp at h

/-! ## The widened loop rule, both ways -/

/-- `n := 2; while n (b := a; a := x0; n := n - 1); return b`: after two rounds `b` holds the secret. The first round raises only `a`; the
    widened round raises `b` too, which the head did not have. -/
def chain : Prog where
  inputs := ["x0", "x1", "y0", "y1"]
  body := .seq (.assign "n" (lit 2))
    (.loop (.var "n") (.seq (.assign "b" (.var "a"))
      (.seq (.assign "a" (.var "x0")) (.assign "n" (.bin .sub (.var "n") (lit 1))))))
  ret := .var "b"

/-- **Refused by the widened round**, and the result does carry the secret. -/
theorem chain_refused : sliceCheck secX chain = false := by decide

theorem chain_leaks : (src chain 50 (words4 1 0 0 0)).ev.map Teeth.evCode ≠ (src chain 50 (words4 2 0 0 0)).ev.map Teeth.evCode := by
  decide +kernel

/-- **Accepted by the widened round**: the secret `a` is read only into itself, and `b` is public. -/
def chainOk : Prog where
  inputs := ["x0", "x1", "y0", "y1"]
  body := .seq (.assign "n" (lit 2))
    (.loop (.var "n") (.seq (.assign "b" (.var "n"))
      (.seq (.assign "a" (.bin .xor (.var "a") (.var "x0"))) (.assign "n" (.bin .sub (.var "n") (lit 1))))))
  ret := .var "b"

theorem chainOk_checks : sliceCheck secX chainOk = true := by decide

end LCore.Slice2.CT
