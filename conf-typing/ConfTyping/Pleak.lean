/-
  Layer 3: the worked example P_leak (§7).

  P_leak ≡ if b then l := 1 else l := 0,   with b ∈ High, l ∈ Low.

  We prove the three separations of §7:
    • wall    is High-invariant   (always 2)   → closable
    • result  is NOT High-invariant            → Policy forced (§7.3)
    • branch  is NOT High-invariant            → residual (§7.4)
-/
import ConfTyping.Obs

namespace ConfTyping

def Pleak : Cmd :=
  .ite (.var "b") (.assign "l" (.num 1)) (.assign "l" (.num 0))

/-- `b` is the only High variable; `l` is Low. -/
def Phigh : Partition := fun x => x == "b"

/-! ### §7.2 wall is closable: it is constantly 2, hence High-invariant. -/

theorem wall_const : ∀ σ, (eval Pleak σ).2.1 = 2 := by
  intro σ
  simp only [Pleak, eval]
  split <;> rfl

theorem wall_closure : J_NI Pleak wall Phigh := by
  intro σ σ' _
  simp only [obs, wall]
  rw [wall_const σ, wall_const σ']

/-! ### §7.3 result is not closable. Two Low-equal stores produce different
    Low results, because the program publishes the High bit by design. -/

def σ0 : Store := upd (fun _ => 0) "b" 1
def σ1 : Store := fun _ => 0

theorem eval_σ0_l : (eval Pleak σ0).1 "l" = 1 := by
  simp [Pleak, eval, evalE, σ0, upd]

theorem eval_σ1_l : (eval Pleak σ1).1 "l" = 0 := by
  simp [Pleak, eval, evalE, σ1, upd]

theorem lowEq_σ : lowEq Phigh σ0 σ1 := by
  intro x hx
  have hxb : x ≠ "b" := by
    intro h; subst h; simp [Phigh] at hx
  simp [σ0, σ1, upd, hxb]

theorem result_not_closable : ¬ J_NI Pleak (resultO Phigh) Phigh := by
  intro h
  have key := h σ0 σ1 lowEq_σ
  simp only [obs, resultO] at key
  injection key with hf
  have hl := congrFun hf "l"
  simp only [Phigh] at hl
  rw [eval_σ0_l, eval_σ1_l] at hl
  exact absurd hl (by decide)

/-! ### §7.4 branch is not closable either — a distinct obligation on a
    distinct channel, leaking the *same* bit `result` releases by policy. -/

theorem branch_σ0 : (eval Pleak σ0).2.2 = [true] := by
  simp [Pleak, eval, evalE, σ0, upd]

theorem branch_σ1 : (eval Pleak σ1).2.2 = [false] := by
  simp [Pleak, eval, evalE, σ1]

theorem branch_not_closable : ¬ J_NI Pleak branchO Phigh := by
  intro h
  have key := h σ0 σ1 lowEq_σ
  simp only [obs, branchO] at key
  injection key with hb
  rw [branch_σ0, branch_σ1] at hb
  exact absurd hb (by decide)

/-! ### §7.3 (bounded). `result` reveals *at most the bit* `(b ≠ 0)`.

This is the substantive Policy obligation: not "result is permitted" (a
fiat), but a proof that the only thing `result` leaks about High is the
declassified bit. The whole point P_leak exists to make. -/

/-- P_leak writes only `l`, setting it to the published bit. -/
theorem eval_Pleak_store (σ : Store) :
    (eval Pleak σ).1 = upd σ "l" (if σ "b" ≠ 0 then 1 else 0) := by
  simp only [Pleak, eval, evalE]
  by_cases h : σ "b" ≠ 0 <;> simp [h]

/-- `Phigh x = false` for every variable other than the secret `b`. -/
theorem Phigh_false {x : String} (h : x ≠ "b") : Phigh x = false := by
  simp only [Phigh, beq_eq_false_iff_ne]; exact h

/-- The declared release: exactly the bit `(b ≠ 0)`. -/
def φ_bit : Release := fun σ => .int (if σ "b" ≠ 0 then 1 else 0)

/-- **The bound.** `result` reveals at most `φ_bit`: two runs that agree on
    Low and on the bit produce the same Low result. -/
theorem result_releases_at_most_bit :
    ReleasesAtMost Pleak (resultO Phigh) Phigh φ_bit := by
  intro σ σ' hle hφ
  simp only [φ_bit] at hφ
  injection hφ with hbit
  simp only [obs, resultO, eval_Pleak_store]
  congr 1
  funext x
  by_cases hxb : x = "b"
  · subst hxb; simp [Phigh]
  · rw [Phigh_false hxb]
    by_cases hxl : x = "l"
    · subst hxl
      simp only [upd]
      exact hbit
    · simp only [upd, ite_eq_right hxl]
      exact hle x (Phigh_false hxb)

/-! ### Non-vacuity: the bound has teeth.

The old unbounded policy made `result` "permitted" by fiat — a free pass
regardless of how much it leaked. Under the bounded policy, a program that
copies the *whole* secret into Low cannot be discharged with the bit-release
`φ_bit`: the `ReleasesAtMost` obligation is **false**. The policy stratum can
now tell "leaks at most the bit" from "leaks everything". -/

def Pfull : Cmd := .assign "l" (.var "b")

theorem eval_Pfull_store (σ : Store) :
    (eval Pfull σ).1 = upd σ "l" (σ "b") := by
  simp [Pfull, eval, evalE]

def σ_b1 : Store := upd (fun _ => 0) "b" 1
def σ_b2 : Store := upd (fun _ => 0) "b" 2

/-- `P_full` leaks the full value of `b`, so it does **not** release at most
    the bit — the bound proof that `result_releases_at_most_bit` supplies for
    `P_leak` is unavailable here. -/
theorem result_full_not_bounded_by_bit :
    ¬ ReleasesAtMost Pfull (resultO Phigh) Phigh φ_bit := by
  intro h
  have hle : lowEq Phigh σ_b1 σ_b2 := by
    intro x hx
    have hxb : x ≠ "b" := by intro hb; subst hb; simp [Phigh] at hx
    simp [σ_b1, σ_b2, upd, hxb]
  have hφ : φ_bit σ_b1 = φ_bit σ_b2 := by
    simp [φ_bit, σ_b1, σ_b2, upd]
  have key := h σ_b1 σ_b2 hle hφ
  simp only [obs, resultO, eval_Pfull_store] at key
  injection key with hf
  have hl := congrFun hf "l"
  simp [Phigh, σ_b1, σ_b2, upd] at hl

end ConfTyping
