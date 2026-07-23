/-
  A security label lattice — brick 18: past binary High/Low.

  Every confidentiality brick so far (1–13) rests on a *binary* partition:
  `Partition : String → Bool`, one secret level and one public level. That is
  the two-point lattice. The classic generalization (Denning) is an arbitrary
  **security lattice**: levels ordered by "may flow to", with a join, and
  noninterference stated *for every observer level* — information at level `a`
  reaches an observer at level `ℓ` only if `a ⊑ ℓ`.

  This matters because binary cannot express *mutually incomparable* secrets:
  "compartment A is secret to B and B is secret to A" needs two incomparable
  labels, which do not exist in `Bool`. This brick proves noninterference over
  an arbitrary lattice (passed as a `SecLat`), and instantiates the **diamond**
  lattice `⊥ < a, b < ⊤` (with `a`, `b` incomparable) to witness a leak that the
  binary model literally cannot state.

  * `latSecTy_ni` — noninterference for every observer level `ℓ`: a typed program
    maps states agreeing below `ℓ` to states agreeing below `ℓ`;
  * `latConfine` — a command whose context is not below `ℓ` leaves the
    `ℓ`-observable state unchanged;
  * `crosscompartment_leaks` / `crosscompartment_untypable` — over the diamond,
    a flow from compartment `a` to an observer in compartment `b` both leaks and
    is untypable — a genuinely non-binary guarantee.
-/
import ConfTyping.Imp

namespace ConfTyping

/-! ## Security lattices -/

/-- A security lattice: a "may flow to" preorder with a least-upper-bound join.
    (Antisymmetry and a bottom are not needed for noninterference.) -/
structure SecLat (L : Type) where
  le            : L → L → Prop
  join          : L → L → L
  le_refl       : ∀ a, le a a
  le_trans      : ∀ {a b c}, le a b → le b c → le a c
  join_le_left  : ∀ a b, le a (join a b)
  join_le_right : ∀ a b, le b (join a b)
  join_lub      : ∀ {a b c}, le a c → le b c → le (join a b) c

variable {L : Type} (𝓛 : SecLat L)

/-- The level of an expression: the join of the levels of the variables it
    reads (`⊥`-ish for constants — here the level of the first available join
    unit, obtained structurally). -/
def exprLevel (Γ : String → L) : Expr → L → L
  | .num _,   acc => acc
  | .var x,   acc => 𝓛.join acc (Γ x)
  | .add a b, acc => exprLevel Γ b (exprLevel Γ a acc)

/-! ## The lattice flow type system -/

/-- Flow typing at context level `pc`. Assignment to `x` requires the data level
    (`exprLevel e`) and the context `pc` to flow into `Γ x`; a branch raises the
    context by the guard's level. -/
inductive LSecTy (Γ : String → L) : L → Cmd → Prop where
  | skip   : LSecTy Γ pc .skip
  | assign : ∀ x e, 𝓛.le (exprLevel 𝓛 Γ e pc) (Γ x) → LSecTy Γ pc (.assign x e)
  | seq    : LSecTy Γ pc c₁ → LSecTy Γ pc c₂ → LSecTy Γ pc (.seq c₁ c₂)
  | ite    : ∀ e, LSecTy Γ (exprLevel 𝓛 Γ e pc) c₁ → LSecTy Γ (exprLevel 𝓛 Γ e pc) c₂ →
             LSecTy Γ pc (.ite e c₁ c₂)

/-! ## Store execution (loop-free `eval`, store projection) -/

def runS (c : Cmd) (σ : Store) : Store := (eval c σ).1

theorem runS_skip (σ : Store) : runS .skip σ = σ := rfl
theorem runS_assign (x e σ) : runS (.assign x e) σ = upd σ x (evalE e σ) := rfl
theorem runS_seq (c₁ c₂ σ) : runS (.seq c₁ c₂) σ = runS c₂ (runS c₁ σ) := rfl
theorem runS_ite (e c₁ c₂ σ) :
    runS (.ite e c₁ c₂) σ = if evalE e σ ≠ 0 then runS c₁ σ else runS c₂ σ := by
  simp only [runS, eval]; split <;> rfl

/-! ## Observer agreement -/

/-- Two stores agree for an observer at level `ℓ`: every variable observable to
    `ℓ` (level `⊑ ℓ`) holds the same value. -/
def agreeBelow (Γ : String → L) (ℓ : L) (σ σ' : Store) : Prop :=
  ∀ x, 𝓛.le (Γ x) ℓ → σ x = σ' x

/-- Monotonicity of `exprLevel` in the accumulator (a larger accumulator gives a
    larger level), used to relate the fold to the observable set. -/
theorem exprLevel_ge_acc (Γ : String → L) :
    ∀ (e : Expr) (acc : L), 𝓛.le acc (exprLevel 𝓛 Γ e acc)
  | .num _,   acc => 𝓛.le_refl acc
  | .var x,   acc => 𝓛.join_le_left acc (Γ x)
  | .add a b, acc =>
      𝓛.le_trans (exprLevel_ge_acc Γ a acc) (exprLevel_ge_acc Γ b (exprLevel 𝓛 Γ a acc))

/-- **Expressions are observable-determined.** If an expression's level is below
    the observer `ℓ`, its value is the same in any two `ℓ`-agreeing states — all
    the variables it reads are observable. -/
theorem evalE_agree (Γ : String → L) (ℓ : L) {σ σ' : Store}
    (hag : agreeBelow 𝓛 Γ ℓ σ σ') :
    ∀ (e : Expr) (acc : L), 𝓛.le (exprLevel 𝓛 Γ e acc) ℓ → evalE e σ = evalE e σ'
  | .num _,   _,   _ => rfl
  | .var x,   acc, h =>
      hag x (𝓛.le_trans (𝓛.join_le_right acc (Γ x)) h)
  | .add a b, acc, h => by
      have hb : 𝓛.le (exprLevel 𝓛 Γ b (exprLevel 𝓛 Γ a acc)) ℓ := h
      have ha : 𝓛.le (exprLevel 𝓛 Γ a acc) ℓ :=
        𝓛.le_trans (exprLevel_ge_acc 𝓛 Γ b (exprLevel 𝓛 Γ a acc)) hb
      simp only [evalE, evalE_agree Γ ℓ hag a acc ha, evalE_agree Γ ℓ hag b _ hb]

/-! ## Confinement and noninterference -/

/-- **Confinement.** If the context level `pc` is not below the observer `ℓ`,
    the command changes nothing observable to `ℓ` — every assignment target has
    level `⊒ pc ⋢ ℓ`. -/
theorem latConfine (Γ : String → L) (ℓ : L) :
    ∀ {pc : L} {c : Cmd}, LSecTy 𝓛 Γ pc c → ¬ 𝓛.le pc ℓ →
      ∀ σ, agreeBelow 𝓛 Γ ℓ σ (runS c σ) := by
  intro pc c h
  induction h with
  | skip => intro _ σ x _; rfl
  | @assign pc x e hxe =>
      intro hpc σ z hz
      rw [runS_assign]
      by_cases hzx : z = x
      · exfalso; apply hpc
        subst hzx
        exact 𝓛.le_trans (𝓛.le_trans (exprLevel_ge_acc 𝓛 Γ e pc) hxe) hz
      · simp [upd, hzx]
  | @seq pc c₁ c₂ _ _ ih₁ ih₂ =>
      intro hpc σ z hz
      rw [runS_seq]
      exact (ih₁ hpc σ z hz).trans (ih₂ hpc (runS c₁ σ) z hz)
  | @ite pc c₁ c₂ e _ _ ih₁ ih₂ =>
      intro hpc σ z hz
      have hpc' : ¬ 𝓛.le (exprLevel 𝓛 Γ e pc) ℓ :=
        fun h => hpc (𝓛.le_trans (exprLevel_ge_acc 𝓛 Γ e pc) h)
      rw [runS_ite]
      split
      · exact ih₁ hpc' σ z hz
      · exact ih₂ hpc' σ z hz

/-- **Noninterference, for every observer level.** A typed program maps states
    agreeing below `ℓ` to states agreeing below `ℓ`: information at a level not
    `⊑ ℓ` never reaches an `ℓ`-observer. Binary High/Low is the two-point
    instance; this holds for any lattice. -/
theorem latSecTy_ni (Γ : String → L) (ℓ : L) :
    ∀ {pc : L} {c : Cmd}, LSecTy 𝓛 Γ pc c →
      ∀ σ σ', agreeBelow 𝓛 Γ ℓ σ σ' → agreeBelow 𝓛 Γ ℓ (runS c σ) (runS c σ') := by
  intro pc c h
  induction h with
  | skip => intro σ σ' hag; exact hag
  | @assign pc x e hxe =>
      intro σ σ' hag z hz
      rw [runS_assign, runS_assign]
      by_cases hzx : z = x
      · subst hzx
        have hlev : 𝓛.le (exprLevel 𝓛 Γ e pc) ℓ := 𝓛.le_trans hxe hz
        simp only [upd, if_pos rfl]
        exact evalE_agree 𝓛 Γ ℓ hag e pc hlev
      · simp only [upd, if_neg hzx]; exact hag z hz
  | seq _ _ ih₁ ih₂ =>
      intro σ σ' hag z hz
      rw [runS_seq, runS_seq]
      exact ih₂ _ _ (ih₁ σ σ' hag) z hz
  | @ite pc c₁ c₂ e h₁ h₂ ih₁ ih₂ =>
      intro σ σ' hag z hz
      by_cases hguard : 𝓛.le (exprLevel 𝓛 Γ e pc) ℓ
      · -- observable guard: same branch on both runs
        have hgv : evalE e σ = evalE e σ' := evalE_agree 𝓛 Γ ℓ hag e pc hguard
        rw [runS_ite, runS_ite, ← hgv]
        split
        · exact ih₁ σ σ' hag z hz
        · exact ih₂ σ σ' hag z hz
      · -- secret guard: both branches confine below ℓ; chain the agreements
        have c₁σ := latConfine 𝓛 Γ ℓ h₁ hguard σ
        have c₁σ' := latConfine 𝓛 Γ ℓ h₁ hguard σ'
        have c₂σ := latConfine 𝓛 Γ ℓ h₂ hguard σ
        have c₂σ' := latConfine 𝓛 Γ ℓ h₂ hguard σ'
        rw [runS_ite, runS_ite]
        -- whichever branch each run takes, its result agrees below ℓ with its input
        have hσ : agreeBelow 𝓛 Γ ℓ σ (if evalE e σ ≠ 0 then runS c₁ σ else runS c₂ σ) := by
          split
          · exact fun x hx => c₁σ x hx
          · exact fun x hx => c₂σ x hx
        have hσ' : agreeBelow 𝓛 Γ ℓ σ' (if evalE e σ' ≠ 0 then runS c₁ σ' else runS c₂ σ') := by
          split
          · exact fun x hx => c₁σ' x hx
          · exact fun x hx => c₂σ' x hx
        exact ((hσ z hz).symm.trans (hag z hz)).trans (hσ' z hz)

/-! ## The diamond lattice: two incomparable compartments -/

inductive Dmd where
  | bot | la | lb | top
deriving DecidableEq

def dmdLeB : Dmd → Dmd → Bool
  | .bot, _   => true
  | _,    .top => true
  | .la,  .la => true
  | .lb,  .lb => true
  | _,    _   => false

def dmdJoin : Dmd → Dmd → Dmd
  | .bot, y    => y
  | x,    .bot => x
  | .la,  .la  => .la
  | .lb,  .lb  => .lb
  | .top, _    => .top
  | _,    .top => .top
  | .la,  .lb  => .top
  | .lb,  .la  => .top

/-- The diamond `⊥ < a, b < ⊤` with `a`, `b` incomparable — a lattice that is
    not a chain, impossible to model with `Bool`. -/
def dmdLat : SecLat Dmd where
  le a b := dmdLeB a b = true
  join := dmdJoin
  le_refl := fun a => by cases a <;> rfl
  le_trans := fun {a b c} hab hbc => by
    cases a <;> cases b <;> cases c <;> simp_all [dmdLeB]
  join_le_left := fun a b => by cases a <;> cases b <;> rfl
  join_le_right := fun a b => by cases a <;> cases b <;> rfl
  join_lub := fun {a b c} hac hbc => by
    cases a <;> cases b <;> cases c <;> simp_all [dmdLeB, dmdJoin]

/-! ## The genuinely non-binary witness -/

/-- Label environment: variable `"s"` is in compartment `a`, `"o"` in
    compartment `b`, everything else public. -/
def Γcomp : String → Dmd := fun x => if x = "s" then .la else if x = "o" then .lb else .bot

theorem Γcomp_s : Γcomp "s" = Dmd.la := rfl
theorem Γcomp_o : Γcomp "o" = Dmd.lb := rfl

/-- The cross-compartment flow: copy `a`-secret `s` into `b`-visible `o`. -/
def CrossFlow : Cmd := .assign "o" (.var "s")

/-- **It is untypable.** Flowing compartment-`a` data into a compartment-`b`
    variable requires `a ⊑ b`, which is false in the diamond — a leak the binary
    High/Low model cannot even express (there is only one secret level there).
    (`hle` is definitionally `dmdLeB a b = true`, which is `false = true`.) -/
theorem crosscompartment_untypable :
    ¬ LSecTy dmdLat Γcomp .bot CrossFlow := by
  intro h
  cases h with
  | assign _ _ hle =>
      have hle2 : dmdLeB Dmd.la Dmd.lb = true := hle
      exact absurd hle2 (by decide)

/-- **And it really leaks to a compartment-`b` observer.** Two states agreeing
    on everything `b` can see (level `⊑ b`: public and `b` itself) but differing
    on the `a`-secret `s` produce different `o` — so `s` (level `a ⋢ b`) reached
    the `b`-observer. Noninterference at `ℓ = b` genuinely fails. -/
theorem crosscompartment_leaks :
    ¬ (∀ σ σ', agreeBelow dmdLat Γcomp .lb σ σ' →
        agreeBelow dmdLat Γcomp .lb (runS CrossFlow σ) (runS CrossFlow σ')) := by
  intro h
  have hag : agreeBelow dmdLat Γcomp .lb (fun _ => 0) (fun y => if y = "s" then 1 else 0) := by
    intro x hx
    by_cases hxs : x = "s"
    · exfalso; subst hxs
      have hx2 : dmdLeB Dmd.la Dmd.lb = true := hx
      exact absurd hx2 (by decide)
    · simp [hxs]
  have hobs : dmdLat.le (Γcomp "o") Dmd.lb := (rfl : dmdLeB Dmd.lb Dmd.lb = true)
  have key := h _ _ hag "o" hobs
  simp [CrossFlow, runS_assign, upd, evalE] at key

end ConfTyping
