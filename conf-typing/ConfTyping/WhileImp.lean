/-
  Loops and the termination channel — brick 7: the model grows.

  Every prior brick worked over loop-free IMP, where `eval` is a total
  structurally-recursive function. Loops break that totality, and they open a
  genuinely new channel: **termination**. A `while` whose guard is secret can
  loop forever iff a secret bit is set — leaking that bit through *whether the
  program halts*, entirely invisibly to a store- or even timing-sensitive
  analysis of terminating runs.

  This module adds loops additively (a fresh `WCmd`, so the existing 22 modules
  are untouched) with a **fuel-indexed** evaluator `wexec : Nat → WCmd → Store →
  Option Outcome` — total by structural recursion on fuel, `none` on exhaustion.
  The flow discipline `WSecTy` is **termination-sensitive**: a loop's guard must
  be Low, so two Low-equal runs proceed in lockstep — same iterations, same
  halting behaviour, same store/cost/trace at every fuel. Soundness
  (`wsecTy_sound`) is that lockstep as `optLowEq` of the fuelled outcomes: the
  termination channel is closed by construction.

  The honesty witness `wleak_leaks`: a secret-guarded loop (`while b skip`)
  halts iff `b = 0`, so at one unit of fuel one run halts and the other does
  not — noninterference fails, and `wcheck` rejects the program
  (`wleak_rejected`). Checker and semantics agree that the termination leak is
  real.
-/
import ConfTyping.SecTy

namespace ConfTyping

/-! ## The language with loops -/

inductive WCmd where
  | skip   : WCmd
  | assign : String → Expr → WCmd
  | seq    : WCmd → WCmd → WCmd
  | ite    : Expr → WCmd → WCmd → WCmd
  | loop   : Expr → WCmd → WCmd

/-- The fuel-indexed evaluator: total by structural recursion on fuel, `none`
    when fuel is exhausted (which is how non-termination shows up). -/
def wexec : Nat → WCmd → Store → Option Outcome
  | 0, _, _ => none
  | _+1, .skip, σ => some (σ, 1, [])
  | _+1, .assign x e, σ => some (upd σ x (evalE e σ), 1, [])
  | n+1, .seq c₁ c₂, σ =>
      (wexec n c₁ σ).bind fun r₁ =>
        (wexec n c₂ r₁.1).map fun r₂ =>
          (r₂.1, r₁.2.1 + r₂.2.1, r₁.2.2 ++ r₂.2.2)
  | n+1, .ite e c₁ c₂, σ =>
      if evalE e σ ≠ 0 then
        (wexec n c₁ σ).map fun r => (r.1, 1 + r.2.1, true :: r.2.2)
      else
        (wexec n c₂ σ).map fun r => (r.1, 1 + r.2.1, false :: r.2.2)
  | n+1, .loop e c, σ =>
      if evalE e σ ≠ 0 then
        (wexec n c σ).bind fun r₁ =>
          (wexec n (.loop e c) r₁.1).map fun r₂ =>
            (r₂.1, 1 + r₁.2.1 + r₂.2.1, true :: (r₁.2.2 ++ r₂.2.2))
      else some (σ, 1, [false])

/-! ## Low-equivalence of fuelled outcomes -/

/-- Two fuelled outcomes are Low-equivalent when they agree on *whether* they
    halt and, if so, on Low store, cost, and trace. The `none`/`some` mismatch
    being `False` is the termination channel: divergent halting is a leak. -/
def optLowEq (P : Partition) : Option Outcome → Option Outcome → Prop
  | none,   none   => True
  | some r, some r' => lowEq P r.1 r'.1 ∧ r.2.1 = r'.2.1 ∧ r.2.2 = r'.2.2
  | _,      _      => False

/-- Threading Low-equivalence through `Option.bind`. -/
theorem optLowEq_bind {P : Partition} {a a' : Option Outcome}
    (h : optLowEq P a a') {f f' : Outcome → Option Outcome}
    (hf : ∀ r r', lowEq P r.1 r'.1 → r.2.1 = r'.2.1 → r.2.2 = r'.2.2 →
          optLowEq P (f r) (f' r')) :
    optLowEq P (a.bind f) (a'.bind f') := by
  cases a with
  | none => cases a' with
    | none => exact True.intro
    | some r' => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact hf r r' h.1 h.2.1 h.2.2

/-- Threading Low-equivalence through `Option.map`. -/
theorem optLowEq_map {P : Partition} {a a' : Option Outcome}
    (h : optLowEq P a a') {g g' : Outcome → Outcome}
    (hg : ∀ r r', lowEq P r.1 r'.1 → r.2.1 = r'.2.1 → r.2.2 = r'.2.2 →
          lowEq P (g r).1 (g' r').1 ∧ (g r).2.1 = (g' r').2.1
            ∧ (g r).2.2 = (g' r').2.2) :
    optLowEq P (a.map g) (a'.map g') := by
  cases a with
  | none => cases a' with
    | none => exact True.intro
    | some r' => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact hg r r' h.1 h.2.1 h.2.2

/-! ## Termination-sensitive flow typing -/

/-- Termination-sensitive typing: like the store/timing discipline, but a
    **loop's guard must be Low** (`whileL`) — a secret-guarded loop is rejected,
    since its halting reveals the secret. No `iteH`, no `whileH`. -/
inductive WSecTy (P : Partition) : WCmd → Prop where
  | skip    : WSecTy P .skip
  | assignH : ∀ x e, P x = true → WSecTy P (.assign x e)
  | assignL : ∀ x e, exprLow P e = true → WSecTy P (.assign x e)
  | seq     : WSecTy P c₁ → WSecTy P c₂ → WSecTy P (.seq c₁ c₂)
  | iteL    : ∀ e, exprLow P e = true → WSecTy P c₁ → WSecTy P c₂ →
              WSecTy P (.ite e c₁ c₂)
  | whileL  : ∀ e, exprLow P e = true → WSecTy P c → WSecTy P (.loop e c)

/-- **Soundness — termination-sensitive noninterference.** At every fuel, two
    Low-equal runs of a well-typed command are Low-equivalent: they halt
    together and agree on Low store, running time, and trace. The termination
    channel is closed. Proof by fuel induction — the `while` case reuses the IH
    at the smaller fuel for both the body *and* the loop continuation. -/
theorem wsecTy_sound {P : Partition} :
    ∀ (n : Nat) (c : WCmd), WSecTy P c →
      ∀ σ σ', lowEq P σ σ' → optLowEq P (wexec n c σ) (wexec n c σ') := by
  intro n
  induction n with
  | zero => intro c _ σ σ' _; cases c <;> exact True.intro
  | succ m ih =>
    intro c hc σ σ' hle
    cases c with
    | skip => exact ⟨hle, rfl, rfl⟩
    | assign x e =>
        cases hc with
        | assignH _ _ hx =>
            refine ⟨?_, rfl, rfl⟩
            intro y hy
            have hyx : y ≠ x := fun h => by rw [h, hx] at hy; cases hy
            show upd σ x (evalE e σ) y = upd σ' x (evalE e σ') y
            simp only [upd, ite_eq_right hyx]; exact hle y hy
        | assignL _ _ he =>
            refine ⟨?_, rfl, rfl⟩
            intro y hy
            show upd σ x (evalE e σ) y = upd σ' x (evalE e σ') y
            simp only [upd]
            by_cases hxy : y = x
            · rw [ite_eq_left hxy, ite_eq_left hxy, evalE_lowEq e he hle]
            · rw [ite_eq_right hxy, ite_eq_right hxy]; exact hle y hy
    | seq c₁ c₂ =>
        cases hc with
        | seq hc₁ hc₂ =>
            show optLowEq P (wexec (m+1) (.seq c₁ c₂) σ) (wexec (m+1) (.seq c₁ c₂) σ')
            simp only [wexec]
            refine optLowEq_bind (ih c₁ hc₁ σ σ' hle) ?_
            intro r₁ r₁' hs₁ hcost₁ htr₁
            refine optLowEq_map (ih c₂ hc₂ r₁.1 r₁'.1 hs₁) ?_
            intro r₂ r₂' hs₂ hcost₂ htr₂
            exact ⟨hs₂, by rw [hcost₁, hcost₂], by rw [htr₁, htr₂]⟩
    | ite e c₁ c₂ =>
        cases hc with
        | iteL _ hg h₁ h₂ =>
            have hgv : evalE e σ = evalE e σ' := evalE_lowEq e hg hle
            show optLowEq P (wexec (m+1) (.ite e c₁ c₂) σ) (wexec (m+1) (.ite e c₁ c₂) σ')
            simp only [wexec]
            by_cases hb : evalE e σ ≠ 0
            · have hb' : evalE e σ' ≠ 0 := by rwa [hgv] at hb
              rw [ite_eq_left hb, ite_eq_left hb']
              refine optLowEq_map (ih c₁ h₁ σ σ' hle) ?_
              intro r r' hs hcs htr; exact ⟨hs, by rw [hcs], by rw [htr]⟩
            · have hb' : ¬ evalE e σ' ≠ 0 := by rwa [hgv] at hb
              rw [ite_eq_right hb, ite_eq_right hb']
              refine optLowEq_map (ih c₂ h₂ σ σ' hle) ?_
              intro r r' hs hcs htr; exact ⟨hs, by rw [hcs], by rw [htr]⟩
    | loop e c₀ =>
        cases hc with
        | whileL _ hg hc₀ =>
            have hgv : evalE e σ = evalE e σ' := evalE_lowEq e hg hle
            show optLowEq P (wexec (m+1) (.loop e c₀) σ) (wexec (m+1) (.loop e c₀) σ')
            simp only [wexec]
            by_cases hb : evalE e σ ≠ 0
            · have hb' : evalE e σ' ≠ 0 := by rwa [hgv] at hb
              rw [ite_eq_left hb, ite_eq_left hb']
              refine optLowEq_bind (ih c₀ hc₀ σ σ' hle) ?_
              intro r₁ r₁' hs₁ hcost₁ htr₁
              refine optLowEq_map
                (ih (.loop e c₀) (.whileL e hg hc₀) r₁.1 r₁'.1 hs₁) ?_
              intro r₂ r₂' hs₂ hcost₂ htr₂
              exact ⟨hs₂, by rw [hcost₁, hcost₂], by rw [htr₁, htr₂]⟩
            · have hb' : ¬ evalE e σ' ≠ 0 := by rwa [hgv] at hb
              rw [ite_eq_right hb, ite_eq_right hb']
              exact ⟨hle, rfl, rfl⟩

/-! ## The executable termination-sensitive checker -/

def wcheck (P : Partition) : WCmd → Bool
  | .skip        => true
  | .assign x e  => P x || exprLow P e
  | .seq c₁ c₂   => wcheck P c₁ && wcheck P c₂
  | .ite e c₁ c₂ => exprLow P e && wcheck P c₁ && wcheck P c₂
  | .loop e c   => exprLow P e && wcheck P c

theorem wcheck_sound {P : Partition} :
    ∀ {c : WCmd}, wcheck P c = true → WSecTy P c
  | .skip, _ => .skip
  | .assign _ _, h => by
      simp only [wcheck, Bool.or_eq_true] at h
      rcases h with hx | he
      · exact .assignH _ _ hx
      · exact .assignL _ _ he
  | .seq _ _, h => by
      simp only [wcheck, Bool.and_eq_true] at h
      exact .seq (wcheck_sound h.1) (wcheck_sound h.2)
  | .ite _ _ _, h => by
      simp only [wcheck, Bool.and_eq_true] at h
      exact .iteL _ h.1.1 (wcheck_sound h.1.2) (wcheck_sound h.2)
  | .loop _ _, h => by
      simp only [wcheck, Bool.and_eq_true] at h
      exact .whileL _ h.1 (wcheck_sound h.2)

/-- Termination-sensitive noninterference by `decide`. -/
theorem optLowEq_of_wcheck {P : Partition} {c : WCmd} (h : wcheck P c = true) :
    ∀ n σ σ', lowEq P σ σ' → optLowEq P (wexec n c σ) (wexec n c σ') :=
  fun n σ σ' hle => wsecTy_sound n c (wcheck_sound h) σ σ' hle

/-! ## The termination leak — the new channel, witnessed -/

/-- A secret-guarded loop: spins while the secret `b` is nonzero. It halts iff
    `b = 0`, so its termination *is* the secret bit. -/
def Wleak : WCmd := .loop (.var "b") .skip

theorem wexec_Wleak_spin (σ : Store) (h : σ "b" ≠ 0) :
    wexec 1 Wleak σ = none := by
  simp [wexec, Wleak, evalE, h]

theorem wexec_Wleak_halt (σ : Store) (h : σ "b" = 0) :
    wexec 1 Wleak σ = some (σ, 1, [false]) := by
  simp [wexec, Wleak, evalE, h]

/-- **The termination leak, witnessed.** Two runs agreeing on all public data
    but differing on the secret `b`: at one unit of fuel, one halts and the
    other spins, so `optLowEq` fails. Termination-sensitive noninterference is
    genuinely violated — the channel is real, not hypothetical. -/
theorem wleak_leaks :
    ¬ (∀ σ σ', lowEq Phigh σ σ' →
        optLowEq Phigh (wexec 1 Wleak σ) (wexec 1 Wleak σ')) := by
  intro h
  have key := h σ0 σ1 lowEq_σ
  rw [wexec_Wleak_spin σ0 (by simp [σ0, upd]),
      wexec_Wleak_halt σ1 (by simp [σ1])] at key
  exact key

/-- **The checker rejects it** — the guard `b` is not Low. Checker and
    semantics agree the loop leaks. -/
theorem wleak_rejected : wcheck Phigh Wleak = false := by decide

/-! ## A certified loop -/

/-- A Low-guarded loop: spins on the public `l`, zeroing it. Terminates in
    lockstep on Low-equal runs. -/
def Wok : WCmd := .loop (.var "l") (.assign "l" (.num 0))

/-- Certified for termination-sensitive noninterference, from one `decide`. -/
theorem wok_certified (n : Nat) (σ σ' : Store) (hle : lowEq Phigh σ σ') :
    optLowEq Phigh (wexec n Wok σ) (wexec n Wok σ') :=
  optLowEq_of_wcheck (by decide) n σ σ' hle

/-! ## Integration: the loop-free fragment embeds faithfully

    The existing 22 modules are over loop-free `Cmd`; this development is over
    `WCmd`. The two agree where they overlap: every `Cmd` embeds into `WCmd`,
    and with enough fuel `wexec` on the embedding computes exactly the total
    `eval`. So the whole prior program is the loop-free fragment of this one —
    the model *grew*, it did not fork. -/

/-- Controlled single-step unfolds (each `rfl`), so rewrites do not re-enter
    the recursive call the way `simp only [wexec]` does. -/
theorem wexec_seq_eq (n : Nat) (c₁ c₂ : WCmd) (σ : Store) :
    wexec (n+1) (.seq c₁ c₂) σ
      = (wexec n c₁ σ).bind fun r₁ =>
          (wexec n c₂ r₁.1).map fun r₂ =>
            (r₂.1, r₁.2.1 + r₂.2.1, r₁.2.2 ++ r₂.2.2) := rfl

theorem wexec_ite_eq (n : Nat) (e : Expr) (c₁ c₂ : WCmd) (σ : Store) :
    wexec (n+1) (.ite e c₁ c₂) σ
      = (if evalE e σ ≠ 0 then
          (wexec n c₁ σ).map fun r => (r.1, 1 + r.2.1, true :: r.2.2)
        else (wexec n c₂ σ).map fun r => (r.1, 1 + r.2.1, false :: r.2.2)) := rfl

theorem wexec_loop_eq (n : Nat) (e : Expr) (c : WCmd) (σ : Store) :
    wexec (n+1) (.loop e c) σ
      = (if evalE e σ ≠ 0 then
          (wexec n c σ).bind fun r₁ =>
            (wexec n (.loop e c) r₁.1).map fun r₂ =>
              (r₂.1, 1 + r₁.2.1 + r₂.2.1, true :: (r₁.2.2 ++ r₂.2.2))
        else some (σ, 1, [false])) := rfl

/-- Embed loop-free IMP into the language with loops. -/
def embed : Cmd → WCmd
  | .skip        => .skip
  | .assign x e  => .assign x e
  | .seq c₁ c₂   => .seq (embed c₁) (embed c₂)
  | .ite e c₁ c₂ => .ite e (embed c₁) (embed c₂)

/-- **Fuel monotonicity.** A halted run stays halted with one more unit of
    fuel — the interpreter never "un-terminates". -/
theorem wexec_mono :
    ∀ (n : Nat) {c : WCmd} {σ : Store} {o : Outcome},
      wexec n c σ = some o → wexec (n+1) c σ = some o := by
  intro n
  induction n with
  | zero => intro c σ o h; simp [wexec] at h
  | succ m ih =>
    intro c σ o h
    cases c with
    | skip => simpa [wexec] using h
    | assign x e => simpa [wexec] using h
    | seq c₁ c₂ =>
        rw [wexec_seq_eq] at h ⊢
        cases h₁ : wexec m c₁ σ with
        | none => rw [h₁] at h; simp at h
        | some r₁ =>
            rw [h₁, Option.bind_some] at h
            rw [ih h₁, Option.bind_some]
            cases h₂ : wexec m c₂ r₁.1 with
            | none => rw [h₂] at h; simp at h
            | some r₂ => rw [ih h₂]; rw [h₂] at h; exact h
    | ite e c₁ c₂ =>
        rw [wexec_ite_eq] at h ⊢
        by_cases hb : evalE e σ ≠ 0
        · rw [ite_eq_left hb] at h ⊢
          cases h₁ : wexec m c₁ σ with
          | none => rw [h₁] at h; simp at h
          | some r => rw [ih h₁]; rw [h₁] at h; exact h
        · rw [ite_eq_right hb] at h ⊢
          cases h₁ : wexec m c₂ σ with
          | none => rw [h₁] at h; simp at h
          | some r => rw [ih h₁]; rw [h₁] at h; exact h
    | loop e c₀ =>
        rw [wexec_loop_eq] at h ⊢
        by_cases hb : evalE e σ ≠ 0
        · rw [ite_eq_left hb] at h ⊢
          cases h₁ : wexec m c₀ σ with
          | none => rw [h₁] at h; simp at h
          | some r₁ =>
              rw [h₁, Option.bind_some] at h
              rw [ih h₁, Option.bind_some]
              cases h₂ : wexec m (.loop e c₀) r₁.1 with
              | none => rw [h₂] at h; simp at h
              | some r₂ => rw [ih h₂]; rw [h₂] at h; exact h
        · rw [ite_eq_right hb] at h ⊢; exact h

theorem wexec_mono_le {c : WCmd} {σ : Store} {o : Outcome} {n : Nat}
    (h : wexec n c σ = some o) : ∀ {m : Nat}, n ≤ m → wexec m c σ = some o := by
  intro m hnm
  induction hnm with
  | refl => exact h
  | step _ ih => exact wexec_mono _ ih

/-- **The embedding is faithful.** For every loop-free program there is a fuel
    at which `wexec` on the embedding computes exactly the total `eval` — the
    prior development is this one's loop-free fragment, and the model grew
    rather than forked. -/
theorem wexec_embed_eq (c : Cmd) (σ : Store) :
    ∃ n, wexec n (embed c) σ = some (eval c σ) := by
  induction c generalizing σ with
  | skip => exact ⟨1, rfl⟩
  | assign x e => exact ⟨1, rfl⟩
  | seq c₁ c₂ ih₁ ih₂ =>
      obtain ⟨n₁, h₁⟩ := ih₁ σ
      obtain ⟨n₂, h₂⟩ := ih₂ (eval c₁ σ).1
      refine ⟨max n₁ n₂ + 1, ?_⟩
      show wexec (max n₁ n₂ + 1) (.seq (embed c₁) (embed c₂)) σ = _
      rw [wexec_seq_eq, wexec_mono_le h₁ (Nat.le_max_left n₁ n₂), Option.bind_some,
          wexec_mono_le h₂ (Nat.le_max_right n₁ n₂), Option.map_some]
      rfl
  | ite e c₁ c₂ ih₁ ih₂ =>
      by_cases hb : evalE e σ ≠ 0
      · obtain ⟨n₁, h₁⟩ := ih₁ σ
        refine ⟨n₁ + 1, ?_⟩
        show wexec (n₁ + 1) (.ite e (embed c₁) (embed c₂)) σ = _
        rw [wexec_ite_eq, ite_eq_left hb, h₁, Option.map_some]
        show _ = some (eval (.ite e c₁ c₂) σ)
        simp only [eval, ite_eq_left hb]
      · obtain ⟨n₂, h₂⟩ := ih₂ σ
        refine ⟨n₂ + 1, ?_⟩
        show wexec (n₂ + 1) (.ite e (embed c₁) (embed c₂)) σ = _
        rw [wexec_ite_eq, ite_eq_right hb, h₂, Option.map_some]
        show _ = some (eval (.ite e c₁ c₂) σ)
        simp only [eval, ite_eq_right hb]

end ConfTyping
