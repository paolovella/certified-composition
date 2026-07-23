/-
  Heap safety under loops — brick 20: the fixed-point checker.

  Brick 19's memory safety was precise because allocation addresses are static
  in *straight-line* code. Loops break that: a `while` allocates a
  runtime-variable number of cells, so no static address tracking survives. The
  sound discipline that does survive is a **loop invariant**: the set of
  valid-pointer variables must be a *fixed point* of the loop body, so it holds
  after any number of iterations.

  This brick combines brick 11's heap (a high-water mark `n`; addresses `[0, n)`
  allocated; access to a wild address is a memory error) with brick 7's
  fuel-indexed semantics (loops, `HRes = to | err | ok`, where `to` is fuel
  exhaustion / non-termination and `err` is a memory error). The checker
  `hlcheck` is flow-sensitive; for `while e c` it requires the body to *preserve*
  the tracked set (`V ⊆ hlcheck V c`) and returns that set unchanged.

  * `hlcheck_safe` — soundness by fuel induction: a checked program **never**
    returns `err` (it may `to`), and every `ok` result preserves the invariant;
    the `while` case reuses the smaller-fuel IH for the body and the loop
    continuation, with the loop invariant carrying across iterations;
  * `loopalloc_safe` — a loop that allocates and accesses fresh cells is
    accepted and never errors at any fuel;
  * `loop_wild_errors` / `loop_wild_rejected` — a loop that accesses an
    unallocated pointer errors and is rejected.
-/
import ConfTyping.Imp

namespace ConfTyping

/-! ## Expressions, machine, and outcomes -/

abbrev HLoc := Nat

/-- Minimal expressions over `Nat`-keyed variables (so witnesses reduce under
    `decide`). -/
inductive HLExpr where
  | lit : Int → HLExpr
  | var : HLoc → HLExpr

def hlval : HLExpr → (HLoc → Int) → Int
  | .lit n, _ => n
  | .var x, σ => σ x

/-- Machine state: variable store and the fresh-address mark. -/
abbrev HLState := (HLoc → Int) × Nat

def hlUpd (σ : HLoc → Int) (x : HLoc) (v : Int) : HLoc → Int :=
  fun y => if y = x then v else σ y

def hlValidB (a : Int) (n : Nat) : Bool := decide (0 ≤ a) && decide (a < n)

/-- Execution outcome: timeout (fuel out / divergence), memory error, or ok. -/
inductive HRes where
  | to  : HRes
  | err : HRes
  | ok  : HLState → HRes

def HRes.bind : HRes → (HLState → HRes) → HRes
  | .to,   _ => .to
  | .err,  _ => .err
  | .ok s, f => f s

theorem hlbind_ne_err {a : HRes} {f : HLState → HRes}
    (ha : a ≠ .err) (hf : ∀ s, a = .ok s → f s ≠ .err) : a.bind f ≠ .err := by
  cases a with
  | to => intro h; simp [HRes.bind] at h
  | err => exact absurd rfl ha
  | ok s => exact hf s rfl

theorem hlbind_ok {a : HRes} {f : HLState → HRes} {s' : HLState}
    (h : a.bind f = .ok s') : ∃ s, a = .ok s ∧ f s = .ok s' := by
  cases a with
  | to => simp [HRes.bind] at h
  | err => simp [HRes.bind] at h
  | ok s => exact ⟨s, rfl, h⟩

/-- Heap commands with loops. `access x` uses the cell `x` points to and is a
    memory error if that address is not allocated. -/
inductive HLCmd where
  | data   : HLoc → HLExpr → HLCmd
  | alloc  : HLoc → HLCmd
  | access : HLoc → HLCmd
  | seq    : HLCmd → HLCmd → HLCmd
  | ite    : HLExpr → HLCmd → HLCmd → HLCmd
  | loop   : HLExpr → HLCmd → HLCmd

def hlexec : Nat → HLCmd → HLState → HRes
  | 0,   _,          _      => .to
  | _+1, .data x e,  (σ, n) => .ok (hlUpd σ x (hlval e σ), n)
  | _+1, .alloc x,   (σ, n) => .ok (hlUpd σ x (n : Int), n + 1)
  | _+1, .access x,  (σ, n) => if hlValidB (σ x) n then .ok (σ, n) else .err
  | k+1, .seq c₁ c₂, s      => (hlexec k c₁ s).bind (hlexec k c₂)
  | k+1, .ite e c₁ c₂, (σ, n) =>
      if hlval e σ ≠ 0 then hlexec k c₁ (σ, n) else hlexec k c₂ (σ, n)
  | k+1, .loop e c,  (σ, n) =>
      if hlval e σ ≠ 0 then (hlexec k c (σ, n)).bind (hlexec k (.loop e c))
      else .ok (σ, n)

/-! ## The flow-sensitive checker with a loop fixed point -/

def hlrem (x : HLoc) (V : List HLoc) : List HLoc := V.filter (fun y => decide (y ≠ x))
def hllinter (V₁ V₂ : List HLoc) : List HLoc := V₁.filter (fun x => decide (x ∈ V₂))
def hllsubB (V₁ V₂ : List HLoc) : Bool := V₁.all (fun x => decide (x ∈ V₂))

theorem mem_of_mem_hlrem {z x V} (h : z ∈ hlrem x V) : z ∈ V := (List.mem_filter.mp h).1
theorem ne_of_mem_hlrem {z x V} (h : z ∈ hlrem x V) : z ≠ x := by
  have := (List.mem_filter.mp h).2; simpa using of_decide_eq_true this
theorem hllinter_left {z V₁ V₂} (h : z ∈ hllinter V₁ V₂) : z ∈ V₁ := (List.mem_filter.mp h).1
theorem hllinter_right {z V₁ V₂} (h : z ∈ hllinter V₁ V₂) : z ∈ V₂ := by
  have := (List.mem_filter.mp h).2; simpa using of_decide_eq_true this
theorem hllsub_mem {V₁ V₂ z} (h : hllsubB V₁ V₂ = true) (hz : z ∈ V₁) : z ∈ V₂ := by
  have := (List.all_eq_true.mp h) z hz; simpa using of_decide_eq_true this

def hlcheck : List HLoc → HLCmd → Option (List HLoc)
  | V, .data x _  => some (hlrem x V)
  | V, .alloc x   => some (x :: V)
  | V, .access x  => if x ∈ V then some V else none
  | V, .seq c₁ c₂ => (hlcheck V c₁).bind (fun V₁ => hlcheck V₁ c₂)
  | V, .ite _ c₁ c₂ =>
      match hlcheck V c₁, hlcheck V c₂ with
      | some V₁, some V₂ => some (hllinter V₁ V₂)
      | _, _ => none
  | V, .loop _ c =>
      match hlcheck V c with
      | some V₁ => if hllsubB V V₁ then some V else none   -- body must preserve V
      | none    => none

/-! ## Soundness -/

/-- Every tracked pointer variable holds a valid (allocated) address. -/
def HLInv (V : List HLoc) : HLState → Prop
  | (σ, n) => ∀ x ∈ V, 0 ≤ σ x ∧ σ x < (n : Int)

/-- **Memory safety under loops, by construction.** A checked program never
    hits a memory error (at any fuel), and every terminating run preserves the
    invariant. The `while` case carries the loop invariant across iterations,
    reusing the smaller-fuel IH for the body and the loop continuation. -/
theorem hlcheck_safe :
    ∀ (fuel : Nat) (c : HLCmd) (V V' : List HLoc) (s : HLState),
      hlcheck V c = some V' → HLInv V s →
      hlexec fuel c s ≠ .err ∧ (∀ s', hlexec fuel c s = .ok s' → HLInv V' s') := by
  intro fuel
  induction fuel with
  | zero => intro c V V' s _ _; exact ⟨by simp [hlexec], by intro s' h; simp [hlexec] at h⟩
  | succ k ih =>
    intro c V V' s hchk hinv
    obtain ⟨σ, n⟩ := s
    cases c with
    | data x e =>
        simp only [hlcheck, Option.some.injEq] at hchk; subst hchk
        refine ⟨by simp [hlexec], ?_⟩
        intro s' hs; simp only [hlexec, HRes.ok.injEq] at hs; subst hs
        intro z hz
        have hzx : z ≠ x := ne_of_mem_hlrem hz
        have := hinv z (mem_of_mem_hlrem hz)
        simpa [hlUpd, hzx] using this
    | alloc x =>
        simp only [hlcheck, Option.some.injEq] at hchk; subst hchk
        refine ⟨by simp [hlexec], ?_⟩
        intro s' hs; simp only [hlexec, HRes.ok.injEq] at hs; subst hs
        intro z hz
        by_cases hzx : z = x
        · subst hzx
          have hlval : hlUpd σ z (n : Int) z = (n : Int) := by simp [hlUpd]
          rw [hlval]; omega
        · have hzV : z ∈ V := by
            rcases List.mem_cons.mp hz with h | h
            · exact absurd h hzx
            · exact h
          have hv := hinv z hzV
          have hu : hlUpd σ x (n : Int) z = σ z := by simp [hlUpd, hzx]
          rw [hu]; omega
    | access x =>
        simp only [hlcheck] at hchk
        by_cases hxV : x ∈ V
        · rw [if_pos hxV, Option.some.injEq] at hchk; subst hchk
          have hv := hinv x hxV
          have hvb : hlValidB (σ x) n = true := by
            simp only [hlValidB, Bool.and_eq_true, decide_eq_true_eq]; exact hv
          refine ⟨by simp [hlexec, hvb], ?_⟩
          intro s' hs; simp only [hlexec, hvb, if_true, HRes.ok.injEq] at hs; subst hs
          exact hinv
        · rw [if_neg hxV] at hchk; simp at hchk
    | seq c₁ c₂ =>
        simp only [hlcheck, Option.bind_eq_bind] at hchk
        cases hV₁ : hlcheck V c₁ with
        | none => rw [hV₁] at hchk; simp at hchk
        | some V₁ =>
            rw [hV₁, Option.bind_some] at hchk
            obtain ⟨e₁, o₁⟩ := ih c₁ V V₁ (σ, n) hV₁ hinv
            refine ⟨?_, ?_⟩
            · exact hlbind_ne_err e₁ (fun s₁ hs₁ => (ih c₂ V₁ V' s₁ hchk (o₁ s₁ hs₁)).1)
            · intro s' hs
              obtain ⟨s₁, ho₁, ho₂⟩ := hlbind_ok hs
              exact (ih c₂ V₁ V' s₁ hchk (o₁ s₁ ho₁)).2 s' ho₂
    | ite e c₁ c₂ =>
        simp only [hlcheck] at hchk
        cases hV₁ : hlcheck V c₁ with
        | none => rw [hV₁] at hchk; simp at hchk
        | some V₁ => cases hV₂ : hlcheck V c₂ with
          | none => rw [hV₁, hV₂] at hchk; simp at hchk
          | some V₂ =>
              rw [hV₁, hV₂, Option.some.injEq] at hchk; subst hchk
              refine ⟨?_, ?_⟩
              · simp only [hlexec]; split
                · exact fun herr => (ih c₁ V V₁ (σ, n) hV₁ hinv).1 herr
                · exact fun herr => (ih c₂ V V₂ (σ, n) hV₂ hinv).1 herr
              · intro s' hs
                simp only [hlexec] at hs
                split at hs
                · exact fun z hz => (ih c₁ V V₁ (σ, n) hV₁ hinv).2 s' hs z (hllinter_left hz)
                · exact fun z hz => (ih c₂ V V₂ (σ, n) hV₂ hinv).2 s' hs z (hllinter_right hz)
    | loop e c =>
        cases hV₁ : hlcheck V c with
        | none => simp [hlcheck, hV₁] at hchk
        | some V₁ =>
            simp only [hlcheck, hV₁] at hchk
            by_cases hsub : hllsubB V V₁ = true
            · rw [if_pos hsub, Option.some.injEq] at hchk; subst hchk
              have hloopchk : hlcheck V (.loop e c) = some V := by
                simp only [hlcheck, hV₁, hsub, if_true]
              have bodyStep : ∀ s₁, hlexec k c (σ, n) = .ok s₁ → HLInv V s₁ := by
                intro s₁ hs₁
                have hb := (ih c V V₁ (σ, n) hV₁ hinv).2 s₁ hs₁
                intro z hz; exact hb z (hllsub_mem hsub hz)
              refine ⟨?_, ?_⟩
              · simp only [hlexec]; split
                · refine hlbind_ne_err (ih c V V₁ (σ, n) hV₁ hinv).1 ?_
                  intro s₁ hs₁
                  exact (ih (.loop e c) V V s₁ hloopchk (bodyStep s₁ hs₁)).1
                · simp [HRes.bind]
              · intro s' hs
                simp only [hlexec] at hs
                split at hs
                · obtain ⟨s₁, ho₁, ho₂⟩ := hlbind_ok hs
                  exact (ih (.loop e c) V V s₁ hloopchk (bodyStep s₁ ho₁)).2 s' ho₂
                · rw [HRes.ok.injEq] at hs; subst hs; exact hinv
            · rw [if_neg hsub] at hchk; simp at hchk

/-- **Certified heap-loop-safe by `decide`.** A checked program never errors. -/
theorem safe_of_check {c : HLCmd} {V' : List HLoc} (fuel : Nat) (σ₀ : HLoc → Int)
    (h : hlcheck [] c = some V') : hlexec fuel c (σ₀, 0) ≠ .err :=
  (hlcheck_safe fuel c [] V' (σ₀, 0) h (by intro _ hx; cases hx)).1

/-! ## Witnesses -/

/-- A loop that allocates a fresh cell and accesses it each iteration; the guard
    is a variable, so it may run any number of times. Checked: `alloc` adds `0`
    to the tracked set, `access 0` needs it, and the body preserves the set. -/
def LoopAlloc : HLCmd :=
  .loop (.var 9) (.seq (.alloc 0) (.access 0))

theorem loopalloc_checks : (hlcheck [] LoopAlloc).isSome = true := by decide

/-- Never errors, at any fuel, from any start — the allocation keeps the
    accessed pointer valid across iterations. -/
theorem loopalloc_safe (fuel : Nat) (σ₀ : HLoc → Int) :
    hlexec fuel LoopAlloc (σ₀, 0) ≠ .err := by
  obtain ⟨V', h⟩ := Option.isSome_iff_exists.mp loopalloc_checks
  exact safe_of_check fuel σ₀ h

/-- A loop that accesses an unallocated pointer `0`. -/
def LoopWild : HLCmd := .loop (.var 9) (.access 0)

/-- **It errors** — at one iteration, `access 0` dereferences address `0 ≥ n = 0`. -/
theorem loop_wild_errors :
    hlexec 3 LoopWild (fun x => if x = 9 then 1 else 0, 0) = .err := by
  simp [hlexec, LoopWild, hlval, hlValidB, HRes.bind]

/-- **And the checker rejects it** — the body accesses untracked `0`, so the
    loop body check fails. -/
theorem loop_wild_rejected : hlcheck [] LoopWild = none := by decide

end ConfTyping
