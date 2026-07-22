/-
  Information flow through the heap — brick 13, the unification.

  Bricks 1–10 certified *confidentiality* (noninterference) over the store;
  bricks 11–12 certified *memory safety* over a heap. This brick puts them
  together: **noninterference over a heap**. The observable is now the store
  *and* the Low region of the heap, and the leak this rules out is a secret in
  a High heap cell reaching a Low variable through a load (or High data reaching
  a Low cell through a store).

  The machine is a store plus a heap `IHeap := Int → Int`, with a static
  address partition `Q : Int → Bool` (`Q a = true` ⟹ cell `a` is High).
  Accesses are at literal addresses (a "labeled memory" model — the region of
  each access is statically known, so both runs of the noninterference argument
  touch the same cell and its known level). `iLowEq P Q` is Low-equivalence of
  the whole state: Low variables equal, Low cells equal.

  The type system `HSecTy` is the pc-label discipline extended with heap rules:
  a Low cell may be written only with Low data in a Low context (`storeL`), and
  a Low variable may be loaded only from a Low cell in a Low context (`loadL`);
  High cells and High variables absorb anything (`storeH`, `loadH`). Soundness
  (`hsecTy_ni`) is noninterference: a typed program preserves `iLowEq`. Witness
  (`heap_leak`, `leak_rejected`): loading a High cell into a Low variable leaks
  the secret and is rejected by the checker — the two halves agree.

  Orthogonality (recorded, not re-proved): memory *safety* (bricks 11–12) and
  this *information-flow* property are independent invariants of the same heap —
  one keeps accesses in bounds, the other keeps them non-leaking — and compose.
-/
import ConfTyping.SecTy
import ConfTyping.MemSafe

namespace ConfTyping

/-! ## The labeled-heap machine -/

/-- A heap of integer cells (total; memory safety is bricks 11–12's concern). -/
abbrev IHeap := Int → Int

/-- Store-and-heap state. -/
abbrev IState := Store × IHeap

/-- Low-equivalence of heaps at the address partition `Q`: Low cells agree. -/
def heapLowEq (Q : Int → Bool) (h h' : IHeap) : Prop :=
  ∀ a, Q a = false → h a = h' a

/-- Low-equivalence of whole states: Low variables and Low cells agree. -/
def iLowEq (P : Partition) (Q : Int → Bool) : IState → IState → Prop
  | (σ, h), (σ', h') => lowEq P σ σ' ∧ heapLowEq Q h h'

theorem iLowEq_symm {P Q} {s s' : IState} (h : iLowEq P Q s s') : iLowEq P Q s' s := by
  obtain ⟨σ, hp⟩ := s; obtain ⟨σ', hp'⟩ := s'
  exact ⟨fun x hx => (h.1 x hx).symm, fun a ha => (h.2 a ha).symm⟩

theorem iLowEq_trans {P Q} {a b c : IState}
    (h₁ : iLowEq P Q a b) (h₂ : iLowEq P Q b c) : iLowEq P Q a c := by
  obtain ⟨σa, ha⟩ := a; obtain ⟨σb, hb⟩ := b; obtain ⟨σc, hc⟩ := c
  exact ⟨fun x hx => (h₁.1 x hx).trans (h₂.1 x hx),
         fun n hn => (h₁.2 n hn).trans (h₂.2 n hn)⟩

/-- Heap commands: control flow plus load/store at literal addresses. -/
inductive HCmd where
  | skip   : HCmd
  | assign : String → Expr → HCmd
  | seq    : HCmd → HCmd → HCmd
  | ite    : Expr → HCmd → HCmd → HCmd
  | load   : String → Int → HCmd   -- y := h[k]
  | store  : Int → Expr → HCmd     -- h[k] := e

/-- The semantics (total: literal addresses, memory safety assumed). -/
def hexec : HCmd → IState → IState
  | .skip,        s => s
  | .assign x e,  (σ, h) => (upd σ x (evalE e σ), h)
  | .seq c₁ c₂,   s => hexec c₂ (hexec c₁ s)
  | .ite e c₁ c₂, (σ, h) => if evalE e σ ≠ 0 then hexec c₁ (σ, h) else hexec c₂ (σ, h)
  | .load y k,    (σ, h) => (upd σ y (h k), h)
  | .store k e,   (σ, h) => (σ, updH h k (evalE e σ))

/-! ## The information-flow type system -/

/-- The pc-label discipline extended to the heap. `pc = true` is a High
    (secret-dependent) context. -/
inductive HSecTy (P : Partition) (Q : Int → Bool) : Bool → HCmd → Prop where
  | skip    : HSecTy P Q pc .skip
  | assignH : ∀ x e, P x = true → HSecTy P Q pc (.assign x e)
  | assignL : ∀ x e, exprLow P e = true → HSecTy P Q false (.assign x e)
  | seq     : HSecTy P Q pc c₁ → HSecTy P Q pc c₂ → HSecTy P Q pc (.seq c₁ c₂)
  | iteL    : ∀ e, exprLow P e = true → HSecTy P Q pc c₁ → HSecTy P Q pc c₂ →
              HSecTy P Q pc (.ite e c₁ c₂)
  | iteH    : HSecTy P Q true c₁ → HSecTy P Q true c₂ → HSecTy P Q pc (.ite e c₁ c₂)
  | loadH   : ∀ y k, P y = true → HSecTy P Q pc (.load y k)          -- into High var: any cell
  | loadL   : ∀ y k, Q k = false → HSecTy P Q false (.load y k)      -- Low cell into any var, Low pc
  | storeH  : ∀ k e, Q k = true → HSecTy P Q pc (.store k e)         -- High cell: any data
  | storeL  : ∀ k e, exprLow P e = true → HSecTy P Q false (.store k e) -- Low data, Low pc

/-! ## Confinement: High-context commands leave Low observations alone -/

theorem hconfine {P Q} {pc : Bool} {c : HCmd} (h : HSecTy P Q pc c) :
    pc = true → ∀ s, iLowEq P Q s (hexec c s) := by
  induction h with
  | skip => intro _ s; obtain ⟨σ, hp⟩ := s; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | assignH x e hx =>
      intro _ s; obtain ⟨σ, hp⟩ := s
      refine ⟨fun y hy => ?_, fun _ _ => rfl⟩
      have hyx : y ≠ x := fun e => by rw [e, hx] at hy; cases hy
      show σ y = upd σ x (evalE e σ) y; simp [upd, hyx]
  | assignL x e _ => intro hpc; exact absurd hpc (by decide)
  | seq h₁ h₂ ih₁ ih₂ =>
      intro hpc s
      exact iLowEq_trans (ih₁ hpc s) (ih₂ hpc (hexec _ s))
  | iteL e _ h₁ h₂ ih₁ ih₂ =>
      intro hpc s; obtain ⟨σ, hp⟩ := s
      simp only [hexec]
      split
      · exact ih₁ hpc (σ, hp)
      · exact ih₂ hpc (σ, hp)
  | iteH h₁ h₂ ih₁ ih₂ =>
      intro _ s; obtain ⟨σ, hp⟩ := s
      simp only [hexec]
      split
      · exact ih₁ rfl (σ, hp)
      · exact ih₂ rfl (σ, hp)
  | loadH y k hy =>
      intro _ s; obtain ⟨σ, hp⟩ := s
      refine ⟨fun z hz => ?_, fun _ _ => rfl⟩
      have hzy : z ≠ y := fun e => by rw [e, hy] at hz; cases hz
      show σ z = upd σ y (hp k) z; simp [upd, hzy]
  | loadL y k _ => intro hpc; exact absurd hpc (by decide)
  | storeH k e hk =>
      intro _ s; obtain ⟨σ, hp⟩ := s
      refine ⟨fun _ _ => rfl, fun a ha => ?_⟩
      have hak : a ≠ k := fun e => by rw [e, hk] at ha; cases ha
      show hp a = updH hp k (evalE e σ) a; simp [updH, hak]
  | storeL k e _ => intro hpc; exact absurd hpc (by decide)

/-! ## Soundness: noninterference over the heap -/

/-- **Noninterference.** A typed program maps Low-equivalent states to
    Low-equivalent states — no secret (High variable or High heap cell) leaks
    into the Low observation (Low variables and Low cells). -/
theorem hsecTy_ni {P Q} {pc : Bool} {c : HCmd} (h : HSecTy P Q pc c) :
    ∀ s s', iLowEq P Q s s' → iLowEq P Q (hexec c s) (hexec c s') := by
  induction h with
  | skip => intro s s' hs; exact hs
  | assignH x e hx =>
      intro s s' hs; obtain ⟨σ, hp⟩ := s; obtain ⟨σ', hp'⟩ := s'
      refine ⟨fun y hy => ?_, hs.2⟩
      have hyx : y ≠ x := fun e => by rw [e, hx] at hy; cases hy
      show upd σ x (evalE e σ) y = upd σ' x (evalE e σ') y
      simp only [upd, if_neg hyx]; exact hs.1 y hy
  | assignL x e he =>
      intro s s' hs; obtain ⟨σ, hp⟩ := s; obtain ⟨σ', hp'⟩ := s'
      refine ⟨fun y hy => ?_, hs.2⟩
      show upd σ x (evalE e σ) y = upd σ' x (evalE e σ') y
      simp only [upd]
      by_cases hyx : y = x
      · rw [if_pos hyx, if_pos hyx, evalE_lowEq e he hs.1]
      · rw [if_neg hyx, if_neg hyx]; exact hs.1 y hy
  | seq _ _ ih₁ ih₂ => intro s s' hs; exact ih₂ _ _ (ih₁ s s' hs)
  | iteL e he _ _ ih₁ ih₂ =>
      intro s s' hs; obtain ⟨σ, hp⟩ := s; obtain ⟨σ', hp'⟩ := s'
      have hgv : evalE e σ = evalE e σ' := evalE_lowEq e he hs.1
      simp only [hexec, ← hgv]
      split
      · exact ih₁ _ _ hs
      · exact ih₂ _ _ hs
  | iteH h₁ h₂ _ _ =>
      intro s s' hs
      exact iLowEq_trans (iLowEq_symm (hconfine (.iteH h₁ h₂) rfl s))
              (iLowEq_trans hs (hconfine (.iteH h₁ h₂) rfl s'))
  | loadH y k hy =>
      intro s s' hs; obtain ⟨σ, hp⟩ := s; obtain ⟨σ', hp'⟩ := s'
      refine ⟨fun z hz => ?_, hs.2⟩
      have hzy : z ≠ y := fun e => by rw [e, hy] at hz; cases hz
      show upd σ y (hp k) z = upd σ' y (hp' k) z
      simp only [upd, if_neg hzy]; exact hs.1 z hz
  | loadL y k hk =>
      intro s s' hs; obtain ⟨σ, hp⟩ := s; obtain ⟨σ', hp'⟩ := s'
      refine ⟨fun z hz => ?_, hs.2⟩
      show upd σ y (hp k) z = upd σ' y (hp' k) z
      have hcell : hp k = hp' k := hs.2 k hk
      simp only [upd]
      by_cases hzy : z = y
      · rw [if_pos hzy, if_pos hzy, hcell]
      · rw [if_neg hzy, if_neg hzy]; exact hs.1 z hz
  | storeH k e hk =>
      intro s s' hs; obtain ⟨σ, hp⟩ := s; obtain ⟨σ', hp'⟩ := s'
      refine ⟨hs.1, fun a ha => ?_⟩
      have hak : a ≠ k := fun e => by rw [e, hk] at ha; cases ha
      show updH hp k (evalE e σ) a = updH hp' k (evalE e σ') a
      simp only [updH, if_neg hak]; exact hs.2 a ha
  | storeL k e he =>
      intro s s' hs; obtain ⟨σ, hp⟩ := s; obtain ⟨σ', hp'⟩ := s'
      have hev : evalE e σ = evalE e σ' := evalE_lowEq e he hs.1
      refine ⟨hs.1, fun a ha => ?_⟩
      show updH hp k (evalE e σ) a = updH hp' k (evalE e σ') a
      simp only [updH, hev]
      by_cases hak : a = k
      · rw [if_pos hak, if_pos hak]
      · rw [if_neg hak, if_neg hak]; exact hs.2 a ha

/-! ## The executable checker -/

def hcheck (P : Partition) (Q : Int → Bool) : Bool → HCmd → Bool
  | _,  .skip        => true
  | pc, .assign x e  => P x || (!pc && exprLow P e)
  | pc, .seq c₁ c₂   => hcheck P Q pc c₁ && hcheck P Q pc c₂
  | pc, .ite e c₁ c₂ =>
      (exprLow P e && hcheck P Q pc c₁ && hcheck P Q pc c₂)
        || (hcheck P Q true c₁ && hcheck P Q true c₂)
  | pc, .load y k    => P y || (!pc && !(Q k))
  | pc, .store k e   => Q k || (!pc && exprLow P e)

theorem hcheck_sound {P Q} :
    ∀ {pc : Bool} {c : HCmd}, hcheck P Q pc c = true → HSecTy P Q pc c
  | _, .skip, _ => .skip
  | pc, .assign x e, h => by
      simp only [hcheck, Bool.or_eq_true, Bool.and_eq_true,
                 Bool.not_eq_eq_eq_not, Bool.not_true] at h
      rcases h with hx | ⟨hpc, he⟩
      · exact .assignH _ _ hx
      · subst hpc; exact .assignL _ _ he
  | pc, .seq c₁ c₂, h => by
      simp only [hcheck, Bool.and_eq_true] at h
      exact .seq (hcheck_sound h.1) (hcheck_sound h.2)
  | pc, .ite e c₁ c₂, h => by
      simp only [hcheck, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨⟨hg, h₁⟩, h₂⟩ | ⟨h₁, h₂⟩
      · exact .iteL _ hg (hcheck_sound h₁) (hcheck_sound h₂)
      · exact .iteH (hcheck_sound h₁) (hcheck_sound h₂)
  | pc, .load y k, h => by
      simp only [hcheck, Bool.or_eq_true, Bool.and_eq_true,
                 Bool.not_eq_eq_eq_not, Bool.not_true] at h
      rcases h with hy | ⟨hpc, hk⟩
      · exact .loadH _ _ hy
      · subst hpc; exact .loadL _ _ (by simpa using hk)
  | pc, .store k e, h => by
      simp only [hcheck, Bool.or_eq_true, Bool.and_eq_true,
                 Bool.not_eq_eq_eq_not, Bool.not_true] at h
      rcases h with hk | ⟨hpc, he⟩
      · exact .storeH _ _ hk
      · subst hpc; exact .storeL _ _ he

/-- **Certified noninterferent by `decide`.** -/
theorem ni_of_check {P Q} {c : HCmd} (h : hcheck P Q false c = true) :
    ∀ s s', iLowEq P Q s s' → iLowEq P Q (hexec c s) (hexec c s') :=
  hsecTy_ni (hcheck_sound h)

/-! ## Non-vacuity and teeth: the heap leak -/

/-- All variables Low; the heap cell at address 7 is High (secret). -/
def Pall : Partition := fun _ => false
def Qsecret : Int → Bool := fun a => a == 7

/-- A safe program: read the Low cell 3 into `y`. Checks, and is
    noninterferent. -/
def HPsafe : HCmd := .load "y" 3

theorem hpsafe_ni :
    ∀ s s', iLowEq Pall Qsecret s s' →
      iLowEq Pall Qsecret (hexec HPsafe s) (hexec HPsafe s') :=
  ni_of_check (by decide)

/-- The leak: read the High cell 7 into a Low variable `y`. -/
def HPleak : HCmd := .load "y" 7

/-- **The heap leak, witnessed.** Two states with equal Low variables and equal
    Low cells but differing on the secret cell 7 produce different `y` — the
    secret flows into a Low variable. Noninterference genuinely fails. -/
theorem heap_leak :
    ¬ (∀ s s', iLowEq Pall Qsecret s s' →
        iLowEq Pall Qsecret (hexec HPleak s) (hexec HPleak s')) := by
  intro h
  have key := h (fun _ => 0, fun a => if a = 7 then 1 else 0)
               (fun _ => 0, fun _ => 0)
               ⟨fun _ _ => rfl, fun a ha => by
                  have hne : a ≠ 7 := by intro e; subst e; simp [Qsecret] at ha
                  simp [hne]⟩
  have hy := key.1 "y" (by decide)
  simp [hexec, HPleak, upd] at hy

/-- **The checker rejects the leak** — a Low variable cannot be loaded from a
    High cell in a Low context. Checker and semantics agree. -/
theorem leak_rejected : hcheck Pall Qsecret false HPleak = false := by decide

end ConfTyping
