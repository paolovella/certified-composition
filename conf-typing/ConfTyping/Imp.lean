/-
  Confidentiality Typing — the IMP timing instance (Paper 1), mechanized.

  Layer 1: language, instrumented operational semantics (§2), an executable
  evaluator, and the equivalence between them (which yields determinism =
  the (Sem-Det) premise of soundness).
-/

namespace ConfTyping

/-- `==` on `Int` is decided by `Int.instDecidableEq`, as under Lean 4.31. Lean 4.35 resolves
    `BEq Int` through `Int.instLinearOrderPackage`, which depends on `Classical.choice`, and every
    definition using `==` on `Int` inherited it (S-435: 299 of 305 footprint changes). Every
    module imports this one, so the pin covers the package. Removing it changes
    `tools/axioms.expected`; check-claims also guards it by name (P0-02). -/
instance (priority := high) intBEqOfDecEq : BEq Int := instBEqOfDecidableEq

/-! ## §1 Language -/

inductive Expr where
  | num : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
deriving Repr

inductive Cmd where
  | skip   : Cmd
  | assign : String → Expr → Cmd
  | seq    : Cmd → Cmd → Cmd
  | ite    : Expr → Cmd → Cmd → Cmd
deriving Repr

/-- Stores σ : Var → ℤ. -/
abbrev Store := String → Int

/-- The High/Low partition: `true` means the variable is High. -/
abbrev Partition := String → Bool

def upd (σ : Store) (x : String) (v : Int) : Store :=
  fun y => if y = x then v else σ y

def evalE : Expr → Store → Int
  | .num n,   _ => n
  | .var x,   σ => σ x
  | .add a b, σ => evalE a σ + evalE b σ

/-! ## §2 Instrumented operational semantics

The judgment `⟨c,σ⟩ ⇓ (σ', t, b)` carries final store, accumulated cost
`t : ℕ`, and branch trace `b : List Bool` (`true = tt`, `false = ff`). -/

inductive Step : Cmd → Store → Store → Nat → List Bool → Prop where
  | skip   : Step .skip σ σ 1 []
  | assign : Step (.assign x e) σ (upd σ x (evalE e σ)) 1 []
  | seq    : Step c1 σ σ1 t1 b1 → Step c2 σ1 σ2 t2 b2 →
             Step (.seq c1 c2) σ σ2 (t1 + t2) (b1 ++ b2)
  | ifT    : evalE e σ ≠ 0 → Step c1 σ σ1 t1 b1 →
             Step (.ite e c1 c2) σ σ1 (1 + t1) (true :: b1)
  | ifF    : evalE e σ = 0 → Step c2 σ σ2 t2 b2 →
             Step (.ite e c1 c2) σ σ2 (1 + t2) (false :: b2)

/-- The same semantics as a total, structurally-recursive evaluator.
    Loops are omitted (§1), so every command terminates. -/
def eval : Cmd → Store → (Store × Nat × List Bool)
  | .skip,       σ => (σ, 1, [])
  | .assign x e, σ => (upd σ x (evalE e σ), 1, [])
  | .seq c1 c2,  σ =>
      let r1 := eval c1 σ
      let r2 := eval c2 r1.1
      (r2.1, r1.2.1 + r2.2.1, r1.2.2 ++ r2.2.2)
  | .ite e c1 c2, σ =>
      if evalE e σ ≠ 0 then
        let r := eval c1 σ
        (r.1, 1 + r.2.1, true :: r.2.2)
      else
        let r := eval c2 σ
        (r.1, 1 + r.2.1, false :: r.2.2)

/-- The evaluator realizes the relation. -/
theorem eval_step : ∀ c σ, Step c σ (eval c σ).1 (eval c σ).2.1 (eval c σ).2.2
  | .skip,       σ => .skip
  | .assign x e, σ => .assign
  | .seq c1 c2,  σ => .seq (eval_step c1 σ) (eval_step c2 (eval c1 σ).1)
  | .ite e c1 c2, σ => by
      simp only [eval]
      by_cases h : evalE e σ ≠ 0
      · rw [ite_eq_left h]; exact .ifT h (eval_step c1 σ)
      · rw [ite_eq_right h]; exact .ifF (by simpa using h) (eval_step c2 σ)

/-- The relation has no outcomes the evaluator misses: every derivation
    agrees with `eval`. Hence the semantics is deterministic (Sem-Det). -/
theorem step_eval : Step c σ σ' t b → (σ', t, b) = eval c σ := by
  intro h
  induction h with
  | skip => rfl
  | assign => rfl
  | seq _ _ ih1 ih2 =>
      simp only [eval]
      rw [← ih1, ← ih2]
  | ifT hne _ ih =>
      simp only [eval]
      rw [ite_eq_left hne, ← ih]
  | ifF heq _ ih =>
      simp only [eval]
      rw [ite_eq_right (by simp [heq]), ← ih]

/-- (Sem-Det): the instrumented semantics is deterministic. -/
theorem determinism
    (h1 : Step c σ σ1 t1 b1) (h2 : Step c σ σ2 t2 b2) :
    σ1 = σ2 ∧ t1 = t2 ∧ b1 = b2 := by
  have e : (σ1, t1, b1) = (σ2, t2, b2) := (step_eval h1).trans (step_eval h2).symm
  injection e with hs e'
  injection e' with ht hb
  exact ⟨hs, ht, hb⟩

end ConfTyping

theorem gateWitnessBroken : (1 : Nat) = 2 := rfl
