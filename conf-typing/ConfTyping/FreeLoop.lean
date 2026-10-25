/-
  Free under loops — brick 23: the last hard combination.

  Brick 12 made `free` sound with a **linearity** invariant (tracked pointers
  hold distinct addresses, so freeing one cannot dangle another) but only for
  straight-line code. Brick 20 handled a heap under **loops** with a fixed-point
  checker but had no `free`. This brick combines them: a `while` whose body may
  `alloc` *and* `free` cells each iteration.

  The subtlety is why this is the last hard combination. Under loops the exact
  addresses of brick 19 are gone, so `free` soundness rests entirely on brick
  12's *linearity* — carried now as a **loop invariant** through fuel induction.
  And the fixed-point rule earns its keep: a loop that frees one of its
  invariant pointers cannot preserve the set, so it is rejected — that is
  exactly the double-free across iterations.

  * `flsafe` — soundness by fuel induction with a four-clause invariant
    (tracked ⟹ live, in-bounds, pairwise-distinct; freed ⟹ once-allocated); a
    checked program never hits a use-after-free/double-free/wild access, at any
    fuel;
  * `allocfree_loop_safe` — `while ( alloc; use; free )` is accepted and never
    errors (each iteration's cell is fresh, used, freed);
  * `usefree_loop_errors` / `usefree_loop_rejected` — using after free within the
    body errors and is rejected; `doublefree_loop_rejected` — freeing an
    invariant pointer each iteration is a double-free, rejected by the fixed
    point.
-/
import ConfTyping.HeapLoop

namespace ConfTyping

-- Lean 4.35: plain `simp` closes `x ≤ x` on `Int` with `Std.le_refl` at the `Int` order
-- package, which depends on `Classical.choice`. Use `Int.le_refl`, as under 4.31 (P0-02).
attribute [-simp] Std.le_refl
attribute [local simp] Int.le_refl

/-! ## The machine: a heap with free, under loops -/

abbrev FLState := (HLoc → Int) × Nat × List Int

def fLive (a : Int) (n : Nat) (F : List Int) : Bool :=
  decide (0 ≤ a) && decide (a < n) && decide (a ∉ F)

inductive FLRes where
  | to  : FLRes
  | err : FLRes
  | ok  : FLState → FLRes

def FLRes.bind : FLRes → (FLState → FLRes) → FLRes
  | .to,   _ => .to
  | .err,  _ => .err
  | .ok s, f => f s

theorem flbind_ne_err {a : FLRes} {f : FLState → FLRes}
    (ha : a ≠ .err) (hf : ∀ s, a = .ok s → f s ≠ .err) : a.bind f ≠ .err := by
  cases a with
  | to => intro h; simp [FLRes.bind] at h
  | err => exact absurd rfl ha
  | ok s => exact hf s rfl

theorem flbind_ok {a : FLRes} {f : FLState → FLRes} {s' : FLState}
    (h : a.bind f = .ok s') : ∃ s, a = .ok s ∧ f s = .ok s' := by
  cases a with
  | to => simp [FLRes.bind] at h
  | err => simp [FLRes.bind] at h
  | ok s => exact ⟨s, rfl, h⟩

inductive FLCmd where
  | data   : HLoc → HLExpr → FLCmd
  | alloc  : HLoc → FLCmd
  | access : HLoc → FLCmd
  | free   : HLoc → FLCmd
  | seq    : FLCmd → FLCmd → FLCmd
  | ite    : HLExpr → FLCmd → FLCmd → FLCmd
  | loop   : HLExpr → FLCmd → FLCmd

def flUpd (σ : HLoc → Int) (x : HLoc) (v : Int) : HLoc → Int :=
  fun y => if y = x then v else σ y

def flexec : Nat → FLCmd → FLState → FLRes
  | 0,   _,          _         => .to
  | _+1, .data x e,  (σ, n, F) => .ok (flUpd σ x (hlval e σ), n, F)
  | _+1, .alloc x,   (σ, n, F) => .ok (flUpd σ x (n : Int), n + 1, F)
  | _+1, .access x,  (σ, n, F) => if fLive (σ x) n F then .ok (σ, n, F) else .err
  | _+1, .free x,    (σ, n, F) => if fLive (σ x) n F then .ok (σ, n, σ x :: F) else .err
  | k+1, .seq c₁ c₂, s         => (flexec k c₁ s).bind (flexec k c₂)
  | k+1, .ite e c₁ c₂, (σ, n, F) =>
      if hlval e σ ≠ 0 then flexec k c₁ (σ, n, F) else flexec k c₂ (σ, n, F)
  | k+1, .loop e c,  (σ, n, F) =>
      if hlval e σ ≠ 0 then (flexec k c (σ, n, F)).bind (flexec k (.loop e c))
      else .ok (σ, n, F)

/-! ## The checker (linearity + loop fixed point) -/

def flcheck : List HLoc → FLCmd → Option (List HLoc)
  | V, .data x _  => some (hlrem x V)
  | V, .alloc x   => some (x :: V)
  | V, .access x  => if x ∈ V then some V else none
  | V, .free x    => if x ∈ V then some (hlrem x V) else none
  | V, .seq c₁ c₂ => (flcheck V c₁).bind (fun V₁ => flcheck V₁ c₂)
  | V, .ite _ c₁ c₂ =>
      match flcheck V c₁, flcheck V c₂ with
      | some V₁, some V₂ => some (hllinter V₁ V₂)
      | _, _ => none
  | V, .loop _ c =>
      match flcheck V c with
      | some V₁ => if hllsubB V V₁ then some V else none
      | none    => none

/-! ## The linearity invariant -/

def FLInv (V : List HLoc) : FLState → Prop
  | (σ, n, F) =>
      (∀ x ∈ V, fLive (σ x) n F = true) ∧
      (∀ x ∈ V, 0 ≤ σ x ∧ σ x < (n : Int)) ∧
      (∀ x ∈ V, ∀ y ∈ V, x ≠ y → σ x ≠ σ y) ∧
      (∀ a ∈ F, a < (n : Int))

theorem fLive_true {a : Int} {n : Nat} {F : List Int}
    (h0 : 0 ≤ a) (hlt : a < (n : Int)) (hF : a ∉ F) : fLive a n F = true := by
  simp only [fLive, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨h0, hlt⟩, hF⟩

/-- The invariant weakens to any subset of the tracked set — used at `ite`. -/
theorem FLInv_mono {W V : List HLoc} {s : FLState}
    (hsub : ∀ z ∈ W, z ∈ V) (h : FLInv V s) : FLInv W s := by
  obtain ⟨σ, n, F⟩ := s; obtain ⟨hli, hbd, hds, hfr⟩ := h
  exact ⟨fun z hz => hli z (hsub z hz), fun z hz => hbd z (hsub z hz),
         fun z hz w hw => hds z (hsub z hz) w (hsub w hw), hfr⟩

/-- **Memory safety with free, under loops, by construction.** A checked program
    never hits a use-after-free, double-free, or wild access (at any fuel), and
    the linearity invariant is preserved. -/
theorem flsafe :
    ∀ (fuel : Nat) (c : FLCmd) (V V' : List HLoc) (s : FLState),
      flcheck V c = some V' → FLInv V s →
      flexec fuel c s ≠ .err ∧ (∀ s', flexec fuel c s = .ok s' → FLInv V' s') := by
  intro fuel
  induction fuel with
  | zero => intro c V V' s _ _; exact ⟨by simp [flexec], by intro s' h; simp [flexec] at h⟩
  | succ k ih =>
    intro c V V' s hchk hinv
    obtain ⟨σ, n, F⟩ := s
    obtain ⟨hli, hbd, hds, hfr⟩ := hinv
    cases c with
    | data x e =>
        simp only [flcheck, Option.some.injEq] at hchk; subst hchk
        refine ⟨by simp [flexec], ?_⟩
        intro s' hs; simp only [flexec, FLRes.ok.injEq] at hs; subst hs
        refine ⟨?_, ?_, ?_, hfr⟩
        · intro z hz
          have hzx : z ≠ x := ne_of_mem_hlrem hz
          simpa [flUpd, hzx] using hli z (mem_of_mem_hlrem hz)
        · intro z hz
          have hzx : z ≠ x := ne_of_mem_hlrem hz
          simpa [flUpd, hzx] using hbd z (mem_of_mem_hlrem hz)
        · intro z hz w hw hzw
          have hzx : z ≠ x := ne_of_mem_hlrem hz
          have hwx : w ≠ x := ne_of_mem_hlrem hw
          simpa [flUpd, hzx, hwx] using
            hds z (mem_of_mem_hlrem hz) w (mem_of_mem_hlrem hw) hzw
    | alloc x =>
        simp only [flcheck, Option.some.injEq] at hchk; subst hchk
        refine ⟨by simp [flexec], ?_⟩
        intro s' hs; simp only [flexec, FLRes.ok.injEq] at hs; subst hs
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro z hz
          by_cases hzx : z = x
          · subst hzx
            have hu : flUpd σ z (n : Int) z = (n : Int) := by simp [flUpd]
            rw [hu]; refine fLive_true (by omega) (by omega) ?_
            intro hmem; exact absurd (hfr (n : Int) hmem) (by omega)
          · have hzV : z ∈ V := (List.mem_cons.mp hz).resolve_left hzx
            have hu : flUpd σ x (n : Int) z = σ z := by simp [flUpd, hzx]
            rw [hu]
            have hlz := hli z hzV
            simp only [fLive, Bool.and_eq_true, decide_eq_true_eq] at hlz
            exact fLive_true hlz.1.1 (by omega) hlz.2
        · intro z hz
          by_cases hzx : z = x
          · subst hzx; have hu : flUpd σ z (n : Int) z = (n : Int) := by simp [flUpd]
            rw [hu]; omega
          · have hzV : z ∈ V := (List.mem_cons.mp hz).resolve_left hzx
            have hu : flUpd σ x (n : Int) z = σ z := by simp [flUpd, hzx]
            rw [hu]; have := hbd z hzV; omega
        · intro z hz w hw hzw
          have hσx : ∀ p : HLoc, flUpd σ x (n : Int) p = if p = x then (n : Int) else σ p :=
            fun _ => rfl
          have key : ∀ p, p ∈ x :: V → p = x ∨ (p ∈ V ∧ p ≠ x ∧ σ p < (n : Int)) := by
            intro p hp; rcases List.mem_cons.mp hp with h | h
            · exact Or.inl h
            · by_cases hpx : p = x
              · exact Or.inl hpx
              · exact Or.inr ⟨h, hpx, (hbd p h).2⟩
          rcases key z hz with hzx | ⟨hzV, hzx, hzlt⟩
          · rcases key w hw with hwx | ⟨hwV, hwx, hwlt⟩
            · exact absurd (hzx.trans hwx.symm) hzw
            · rw [hσx z, hσx w, if_pos hzx, if_neg hwx]; omega
          · rcases key w hw with hwx | ⟨hwV, hwx, hwlt⟩
            · rw [hσx z, hσx w, if_neg hzx, if_pos hwx]; omega
            · rw [hσx z, hσx w, if_neg hzx, if_neg hwx]; exact hds z hzV w hwV hzw
        · intro a ha; have := hfr a ha; omega
    | access x =>
        simp only [flcheck] at hchk
        by_cases hxV : x ∈ V
        · rw [if_pos hxV, Option.some.injEq] at hchk; subst hchk
          have hlive := hli x hxV
          refine ⟨by simp [flexec, hlive], ?_⟩
          intro s' hs; simp only [flexec, hlive, if_true, FLRes.ok.injEq] at hs; subst hs
          exact ⟨hli, hbd, hds, hfr⟩
        · rw [if_neg hxV] at hchk; simp at hchk
    | free x =>
        simp only [flcheck] at hchk
        by_cases hxV : x ∈ V
        · rw [if_pos hxV, Option.some.injEq] at hchk; subst hchk
          have hlive := hli x hxV
          refine ⟨by simp [flexec, hlive], ?_⟩
          intro s' hs; simp only [flexec, hlive, if_true, FLRes.ok.injEq] at hs; subst hs
          refine ⟨?_, fun z hz => hbd z (mem_of_mem_hlrem hz),
                  fun z hz w hw hzw => hds z (mem_of_mem_hlrem hz) w (mem_of_mem_hlrem hw) hzw, ?_⟩
          · intro z hz
            have hzx : z ≠ x := ne_of_mem_hlrem hz
            have hzV := mem_of_mem_hlrem hz
            have hne : σ z ≠ σ x := hds z hzV x hxV hzx
            have hlz := hli z hzV
            simp only [fLive, Bool.and_eq_true, decide_eq_true_eq] at hlz
            refine fLive_true hlz.1.1 hlz.1.2 ?_
            intro hmem
            rcases List.mem_cons.mp hmem with h | h
            · exact hne h
            · exact hlz.2 h
          · intro a ha
            rcases List.mem_cons.mp ha with h | h
            · subst h; exact (hbd x hxV).2
            · exact hfr a h
        · rw [if_neg hxV] at hchk; simp at hchk
    | seq c₁ c₂ =>
        simp only [flcheck, Option.bind_eq_bind] at hchk
        cases hV₁ : flcheck V c₁ with
        | none => rw [hV₁] at hchk; simp at hchk
        | some V₁ =>
            rw [hV₁, Option.bind_some] at hchk
            obtain ⟨e₁, o₁⟩ := ih c₁ V V₁ (σ, n, F) hV₁ ⟨hli, hbd, hds, hfr⟩
            refine ⟨flbind_ne_err e₁ (fun s₁ hs₁ => (ih c₂ V₁ V' s₁ hchk (o₁ s₁ hs₁)).1), ?_⟩
            intro s' hs
            obtain ⟨s₁, ho₁, ho₂⟩ := flbind_ok hs
            exact (ih c₂ V₁ V' s₁ hchk (o₁ s₁ ho₁)).2 s' ho₂
    | ite e c₁ c₂ =>
        cases hV₁ : flcheck V c₁ with
        | none => simp [flcheck, hV₁] at hchk
        | some V₁ => cases hV₂ : flcheck V c₂ with
          | none => simp [flcheck, hV₁, hV₂] at hchk
          | some V₂ =>
              simp only [flcheck, hV₁, hV₂, Option.some.injEq] at hchk; subst hchk
              refine ⟨?_, ?_⟩
              · simp only [flexec]; split
                · exact (ih c₁ V V₁ (σ, n, F) hV₁ ⟨hli, hbd, hds, hfr⟩).1
                · exact (ih c₂ V V₂ (σ, n, F) hV₂ ⟨hli, hbd, hds, hfr⟩).1
              · intro s' hs; simp only [flexec] at hs; split at hs
                · exact FLInv_mono (fun z hz => hllinter_left hz)
                    ((ih c₁ V V₁ (σ, n, F) hV₁ ⟨hli, hbd, hds, hfr⟩).2 s' hs)
                · exact FLInv_mono (fun z hz => hllinter_right hz)
                    ((ih c₂ V V₂ (σ, n, F) hV₂ ⟨hli, hbd, hds, hfr⟩).2 s' hs)
    | loop e c =>
        cases hV₁ : flcheck V c with
        | none => simp [flcheck, hV₁] at hchk
        | some V₁ =>
            simp only [flcheck, hV₁] at hchk
            by_cases hsub : hllsubB V V₁ = true
            · rw [if_pos hsub, Option.some.injEq] at hchk; subst hchk
              have hloopchk : flcheck V (.loop e c) = some V := by
                simp only [flcheck, hV₁, hsub, if_true]
              have bodyStep : ∀ s₁, flexec k c (σ, n, F) = .ok s₁ → FLInv V s₁ := by
                intro s₁ hs₁
                exact FLInv_mono (fun z hz => hllsub_mem hsub hz)
                  ((ih c V V₁ (σ, n, F) hV₁ ⟨hli, hbd, hds, hfr⟩).2 s₁ hs₁)
              refine ⟨?_, ?_⟩
              · simp only [flexec]; split
                · refine flbind_ne_err (ih c V V₁ (σ, n, F) hV₁ ⟨hli, hbd, hds, hfr⟩).1 ?_
                  intro s₁ hs₁
                  exact (ih (.loop e c) V V s₁ hloopchk (bodyStep s₁ hs₁)).1
                · simp [FLRes.bind]
              · intro s' hs; simp only [flexec] at hs; split at hs
                · obtain ⟨s₁, ho₁, ho₂⟩ := flbind_ok hs
                  exact (ih (.loop e c) V V s₁ hloopchk (bodyStep s₁ ho₁)).2 s' ho₂
                · rw [FLRes.ok.injEq] at hs; subst hs; exact ⟨hli, hbd, hds, hfr⟩
            · rw [if_neg hsub] at hchk; simp at hchk

/-- **Certified free-under-loops-safe by `decide`.** -/
theorem flsafe_of_check {c : FLCmd} {V' : List HLoc} (fuel : Nat) (σ₀ : HLoc → Int)
    (h : flcheck [] c = some V') : flexec fuel c (σ₀, 0, []) ≠ .err := by
  have hinv : FLInv [] (σ₀, 0, []) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro x hx <;> cases hx
  exact (flsafe fuel c [] V' (σ₀, 0, []) h hinv).1

/-! ## Witnesses -/

/-- The realistic pattern: a loop that allocates a fresh cell, uses it, and frees
    it each iteration. `V = []` is preserved (the cell is local to the body). -/
def AllocFreeLoop : FLCmd :=
  .loop (.var 9) (.seq (.alloc 0) (.seq (.access 0) (.free 0)))

theorem allocfree_checks : (flcheck [] AllocFreeLoop).isSome = true := by decide

theorem allocfree_loop_safe (fuel : Nat) (σ₀ : HLoc → Int) :
    flexec fuel AllocFreeLoop (σ₀, 0, []) ≠ .err := by
  obtain ⟨V', h⟩ := Option.isSome_iff_exists.mp allocfree_checks
  exact flsafe_of_check fuel σ₀ h

/-- Use-after-free inside the body: alloc, free, then access the freed cell. -/
def UseFreeLoop : FLCmd :=
  .loop (.var 9) (.seq (.alloc 0) (.seq (.free 0) (.access 0)))

theorem usefree_loop_errors :
    flexec 4 UseFreeLoop (fun x => if x = 9 then 1 else 0, 0, []) = .err := by
  simp [flexec, UseFreeLoop, hlval, flUpd, fLive, FLRes.bind]

theorem usefree_loop_rejected : flcheck [] UseFreeLoop = none := by decide

/-- Double-free across iterations: with `p` in the loop invariant, freeing it
    each iteration double-frees. The fixed-point rule rejects it (`free`
    invalidates `p`, so the body cannot preserve the invariant set). -/
def DoubleFreeLoop : FLCmd := .loop (.var 9) (.free 0)

theorem doublefree_loop_rejected : flcheck [0] DoubleFreeLoop = none := by decide

end ConfTyping
