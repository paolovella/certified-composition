/-
  Pointer aliasing — brick 19: use-after-free through an alias.

  Brick 12 made `free` sound under a **linearity** discipline: tracked pointers
  held *distinct* addresses and copying was forbidden outright, so freeing one
  could not dangle another. Real code copies pointers (`q = p`), creating
  **aliases** — and then `free p` dangles `q` too. Soundly ruling out the
  resulting use-after-free needs an alias analysis, which linearity dodged by
  banning the copy.

  The insight that makes aliasing tractable *and precise* here: in a
  loop-free program the allocation addresses are **statically determined** (the
  k-th `alloc` returns address `k`), so the checker can track the *exact*
  address each pointer holds — hence exact aliasing (a must-alias analysis). A
  `copy x y` gives `x` the same tracked address as `y`; a `free x` marks that
  address freed; and an access through *any* variable holding a freed address is
  rejected — whichever alias it came through.

  * `acheck_safe` — soundness: a checked program never accesses a freed (or
    unallocated) cell, through any alias;
  * `alias_uaf_errors` / `alias_uaf_rejected` — the witness brick 12 could not
    state: `alloc p; copy q p; free p; access q` dangles `q` through the alias,
    errors at runtime, and is rejected by the checker;
  * `aliased_use_before_free_ok` — copying is *allowed* (unlike linearity): the
    same program with the access before the free is accepted and runs.
-/
import ConfTyping.Imp

namespace ConfTyping

/-! ## The machine: addresses, allocation, free, and copy -/

/-- Concrete state: variable store (holding addresses as ints), the fresh-address
    mark `n` (addresses `[0, n)` have been allocated), and the freed set `F`.
    A cell is **live** iff it is allocated and not freed. -/
abbrev AState := Store × Nat × List Int

/-- Runtime liveness of an address. -/
def liveB (a : Int) (n : Nat) (F : List Int) : Bool :=
  decide (0 ≤ a) && decide (a < n) && decide (a ∉ F)

/-- Commands: allocate, **copy a pointer** (aliasing), overwrite with plain
    data, free, and access through a pointer (models load/store — the memory
    error is the same). -/
inductive ACmd where
  | alloc  : String → ACmd            -- x := fresh cell
  | copy   : String → String → ACmd   -- x := y   (pointer copy / alias)
  | data   : String → Expr → ACmd     -- x := e   (plain int, no longer a pointer)
  | free   : String → ACmd
  | access : String → ACmd            -- use *x   (error if x's cell is dead)
  | seq    : ACmd → ACmd → ACmd

def aexec : ACmd → AState → Option AState
  | .alloc x,  (σ, n, F) => some (upd σ x (n : Int), n + 1, F)
  | .copy x y, (σ, n, F) => some (upd σ x (σ y), n, F)
  | .data x e, (σ, n, F) => some (upd σ x (evalE e σ), n, F)
  | .free x,   (σ, n, F) => if liveB (σ x) n F then some (σ, n, σ x :: F) else none
  | .access x, (σ, n, F) => if liveB (σ x) n F then some (σ, n, F) else none
  | .seq c₁ c₂, s => (aexec c₁ s).bind (aexec c₂)

/-! ## The checker: exact address tracking -/

/-- Checker state: the address each variable is known to hold (`none` = not a
    tracked pointer), the fresh mark, and the freed set — a static simulation of
    allocation, exact for straight-line code. -/
abbrev CState := (String → Option Int) × Nat × List Int

def updO (A : String → Option Int) (x : String) (v : Option Int) : String → Option Int :=
  fun y => if y = x then v else A y

def acheck : CState → ACmd → Option CState
  | (A, nx, F), .alloc x  => some (updO A x (some (nx : Int)), nx + 1, F)
  | (A, nx, F), .copy x y => some (updO A x (A y), nx, F)
  | (A, nx, F), .data x _ => some (updO A x none, nx, F)
  | (A, nx, F), .free x   =>
      match A x with
      | some a => if a ∈ F then none else some (A, nx, a :: F)
      | none   => none
  | (A, nx, F), .access x =>
      match A x with
      | some a => if a ∈ F then none else some (A, nx, F)
      | none   => none
  | CS, .seq c₁ c₂ => (acheck CS c₁).bind (fun CS₁ => acheck CS₁ c₂)

/-! ## Soundness -/

/-- The tracked address of every pointer variable matches the runtime address
    and is in-bounds; the checker's mark and freed set match the runtime's. -/
def AInv : CState → AState → Prop
  | (A, nx, F), (σ, n, Fc) =>
      nx = n ∧ F = Fc ∧ ∀ x a, A x = some a → σ x = a ∧ 0 ≤ a ∧ a < (nx : Int)

/-- **Aliasing-sound memory safety.** A checked program never accesses a freed
    or unallocated cell — through *any* alias — and the invariant is preserved.
    Freeing a cell invalidates every variable that holds its address, because
    the checker tracks addresses exactly. -/
theorem acheck_safe :
    ∀ (c : ACmd) (CS CS' : CState) (s : AState),
      acheck CS c = some CS' → AInv CS s →
      ∃ s', aexec c s = some s' ∧ AInv CS' s' := by
  intro c
  induction c with
  | alloc x =>
      intro ⟨A, nx, F⟩ CS' ⟨σ, n, Fc⟩ hchk hinv
      simp only [acheck, Option.some.injEq] at hchk; subst hchk
      obtain ⟨hnx, hF, hpt⟩ := hinv
      subst hnx; subst hF
      refine ⟨(upd σ x (nx : Int), nx + 1, F), rfl, rfl, rfl, ?_⟩
      intro z a hz
      simp only [updO] at hz
      by_cases hzx : z = x
      · subst hzx; simp only [ite_eq_left rfl] at hz
        cases hz; refine ⟨by simp [upd], ?_, ?_⟩ <;> omega
      · rw [ite_eq_right hzx] at hz
        obtain ⟨hσ, h0, hlt⟩ := hpt z a hz
        refine ⟨by simp [upd, hzx, hσ], h0, ?_⟩
        omega
  | copy x y =>
      intro ⟨A, nx, F⟩ CS' ⟨σ, n, Fc⟩ hchk hinv
      simp only [acheck, Option.some.injEq] at hchk; subst hchk
      obtain ⟨hnx, hF, hpt⟩ := hinv
      subst hnx; subst hF
      refine ⟨(upd σ x (σ y), nx, F), rfl, rfl, rfl, ?_⟩
      intro z a hz
      simp only [updO] at hz
      by_cases hzx : z = x
      · subst hzx; simp only [ite_eq_left rfl] at hz
        obtain ⟨hσ, h0, hlt⟩ := hpt y a hz
        exact ⟨by simp [upd, hσ], h0, hlt⟩
      · rw [ite_eq_right hzx] at hz
        obtain ⟨hσ, h0, hlt⟩ := hpt z a hz
        exact ⟨by simp [upd, hzx, hσ], h0, hlt⟩
  | data x e =>
      intro ⟨A, nx, F⟩ CS' ⟨σ, n, Fc⟩ hchk hinv
      simp only [acheck, Option.some.injEq] at hchk; subst hchk
      obtain ⟨hnx, hF, hpt⟩ := hinv
      subst hnx; subst hF
      refine ⟨(upd σ x (evalE e σ), nx, F), rfl, rfl, rfl, ?_⟩
      intro z a hz
      simp only [updO] at hz
      by_cases hzx : z = x
      · subst hzx; simp at hz
      · rw [ite_eq_right hzx] at hz
        obtain ⟨hσ, h0, hlt⟩ := hpt z a hz
        exact ⟨by simp [upd, hzx, hσ], h0, hlt⟩
  | free x =>
      intro ⟨A, nx, F⟩ CS' ⟨σ, n, Fc⟩ hchk hinv
      obtain ⟨hnx, hF, hpt⟩ := hinv
      subst hnx; subst hF
      cases hAx : A x with
      | none => simp [acheck, hAx] at hchk
      | some a =>
          simp only [acheck, hAx] at hchk
          by_cases haF : a ∈ F
          · rw [ite_eq_left haF] at hchk; simp at hchk
          · rw [ite_eq_right haF, Option.some.injEq] at hchk; subst hchk
            obtain ⟨hσ, h0, hlt⟩ := hpt x a hAx
            have hlive : liveB (σ x) nx F = true := by
              simp only [liveB, hσ, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨⟨h0, hlt⟩, haF⟩
            refine ⟨(σ, nx, σ x :: F), ?_, rfl, ?_, hpt⟩
            · show (if liveB (σ x) nx F then _ else _) = _; rw [ite_eq_left hlive]
            · rw [hσ]
  | access x =>
      intro ⟨A, nx, F⟩ CS' ⟨σ, n, Fc⟩ hchk hinv
      obtain ⟨hnx, hF, hpt⟩ := hinv
      subst hnx; subst hF
      cases hAx : A x with
      | none => simp [acheck, hAx] at hchk
      | some a =>
          simp only [acheck, hAx] at hchk
          by_cases haF : a ∈ F
          · rw [ite_eq_left haF] at hchk; simp at hchk
          · rw [ite_eq_right haF, Option.some.injEq] at hchk; subst hchk
            obtain ⟨hσ, h0, hlt⟩ := hpt x a hAx
            have hlive : liveB (σ x) nx F = true := by
              simp only [liveB, hσ, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨⟨h0, hlt⟩, haF⟩
            refine ⟨(σ, nx, F), ?_, rfl, rfl, hpt⟩
            show (if liveB (σ x) nx F then _ else _) = _; rw [ite_eq_left hlive]
  | seq c₁ c₂ ih₁ ih₂ =>
      intro CS CS' s hchk hinv
      simp only [acheck, Option.bind_eq_bind] at hchk
      cases hCS₁ : acheck CS c₁ with
      | none => rw [hCS₁] at hchk; simp at hchk
      | some CS₁ =>
          rw [hCS₁, Option.bind_some] at hchk
          obtain ⟨s₁, hs₁, hinv₁⟩ := ih₁ CS CS₁ s hCS₁ hinv
          obtain ⟨s', hs', hinv'⟩ := ih₂ CS₁ CS' s₁ hchk hinv₁
          refine ⟨s', ?_, hinv'⟩
          show (aexec c₁ s).bind (aexec c₂) = some s'
          rw [hs₁, Option.bind_some, hs']

/-- **Certified alias-safe by `decide`.** From the empty state a checked program
    runs without a memory error. -/
theorem asafe_of_check {c : ACmd} {CS' : CState}
    (h : acheck (fun _ => none, 0, []) c = some CS') (σ₀ : Store) :
    ∃ s', aexec c (σ₀, 0, []) = some s' := by
  obtain ⟨s', hs', _⟩ := acheck_safe c _ CS' (σ₀, 0, []) h
    ⟨rfl, rfl, by intro x a hx; simp at hx⟩
  exact ⟨s', hs'⟩

/-! ## The witness brick 12 could not state -/

/-- Use-after-free through an alias: allocate `p`, copy it to `q`, free `p`,
    then access `q`. Brick 12's linearity forbade the copy; here it is allowed
    and the danger is caught. -/
def AliasUAF : ACmd :=
  .seq (.alloc "p") (.seq (.copy "q" "p") (.seq (.free "p") (.access "q")))

/-- **It errors** — after `free p`, the cell `q` aliases is dead, so accessing
    `q` is a use-after-free. -/
theorem alias_uaf_errors (σ₀ : Store) :
    aexec AliasUAF (σ₀, 0, []) = none := by
  simp [aexec, AliasUAF, upd, liveB]

/-- **And the checker rejects it** — `copy` gave `q` the same tracked address as
    `p`, `free p` marked it freed, so the access through the alias `q` is
    flagged. Exact aliasing catches the dangling reference. -/
theorem alias_uaf_rejected : acheck (fun _ => none, 0, []) AliasUAF = none := by decide

/-- **Copying is allowed** (unlike linearity): the same program with the access
    *before* the free is accepted and runs. -/
def AliasOK : ACmd :=
  .seq (.alloc "p") (.seq (.copy "q" "p") (.seq (.access "q") (.free "p")))

theorem alias_ok_accepted : (acheck (fun _ => none, 0, []) AliasOK).isSome = true := by decide

theorem alias_ok_runs (σ₀ : Store) : ∃ s', aexec AliasOK (σ₀, 0, []) = some s' := by
  obtain ⟨CS', h⟩ := Option.isSome_iff_exists.mp alias_ok_accepted
  exact asafe_of_check h σ₀

end ConfTyping
