/-
  **UCmd with halting abort and one trace in program order** (F2 step 2). Not Ring 0.

  `uexecT` is `uexec`'s twin for L. `uexec` is locked meaning (ring0.lock) and is not edited.
  The twin differs in exactly two ways, both decided for F2:
  - **Abort halts** (the user's decision, 2026-10-29). A run that dies, by a refused check or a
    memory fault, stops at once with outcome `abort`. `uexec` instead keeps executing no-ops,
    and inside a loop it never returns (`uexec_dead_loop_diverges`), which is what made
    `vacProg`'s certificates vacuous (`Vacuity.lean`).
  - **One trace, in program order.** Events (checks, reads, emits) and leakage (branch bits,
    addresses) are each one list in the order they happen, so a run with more fuel extends
    them at the end. `ucmdLang` listed every read before every emit, which no prefix law can
    hold of.
  At every fuel, `uexecT` returns what happened so far, with outcome `fuel` if the fuel ran out.

  Proved here: `uexecT` is monotone in fuel (`uexecT_ext`), and a run that runs out of fuel has
  paid for it (`uexecT_diverge`), so `ucmdLangT` is a lawful language (`ucmdLangT_lawful`).
-/
import ConfTyping.LAdapter

namespace ConfTyping

/-- What a run did, so far. -/
structure TRun where
  st   : UState
  cost : Nat
  ev   : List LCore.Ev
  lk   : List LCore.Lk
  out  : LCore.Outcome

/-- The events of one atomic step from a live state. -/
def stepEv : UCmd → UState → List LCore.Ev
  | .check r,         _ => [.check r]
  | .access r,        _ => [.read r]
  | .sop .emit x e,   s => [.emit x ((evalS s.sstore e).map uchCode)]
  | _,                _ => []

/-- One atomic step, from a live state: `uexec`'s own step, with its events, its addresses,
    and `abort` if the step killed the run. -/
def stepT (c : UCmd) (π : MedPolicy) (s : UState) : TRun :=
  match uexec 1 c π s with
  | some r => ⟨r.1, r.2.1, stepEv c s, ((uaddrs 1 c π s).getD []).map .addr,
               if r.1.dead then .abort else .done⟩
  | none   => ⟨s, 0, [], [], .fuel⟩

/-- Run `a`, then, if it finished, `k` from where it stopped; the record of both. -/
def TRun.seqT (a : TRun) (k : UState → TRun) : TRun :=
  if a.out = .done then
    let b := k a.st
    ⟨b.st, a.cost + b.cost, a.ev ++ b.ev, a.lk ++ b.lk, b.out⟩
  else a

/-- One counted step that shows a branch bit, in front of `a`. -/
def TRun.tick (l : LCore.Lk) (a : TRun) : TRun := ⟨a.st, 1 + a.cost, a.ev, l :: a.lk, a.out⟩

/-- **The twin.** -/
def uexecT : Nat → UCmd → MedPolicy → UState → TRun
  | 0,     _, _, s => ⟨s, 0, [], [], .fuel⟩
  | n + 1, c, π, s =>
    if s.dead then ⟨s, 0, [], [], .abort⟩ else
    match c with
    | .seq c₁ c₂   => (uexecT n c₁ π s).seqT (fun t => uexecT n c₂ π t)
    | .ite e c₁ c₂ =>
        TRun.tick (.branch (decide (evalE e s.store ≠ 0)))
          (uexecT n (if evalE e s.store ≠ 0 then c₁ else c₂) π s)
    | .loop e b =>
        if evalE e s.store ≠ 0 then
          TRun.tick (.branch true) ((uexecT n b π s).seqT (fun t => uexecT n (.loop e b) π t))
        else ⟨s, 1, [], [.branch false], .done⟩
    | c => stepT c π s

/-! ## Monotone in fuel -/

/-- `b` extends `a`: a finished `a` is `b`, and otherwise `a` is a prefix of `b`. -/
def TRun.Ext (a b : TRun) : Prop :=
  (a.out ≠ .fuel → a = b) ∧ a.ev <+: b.ev ∧ a.lk <+: b.lk ∧ a.cost ≤ b.cost

theorem TRun.Ext.refl (a : TRun) : a.Ext a :=
  ⟨fun _ => rfl, List.prefix_refl _, List.prefix_refl _, Nat.le_refl _⟩

theorem prefix_append_both {α} (l : List α) {a b : List α} (h : a <+: b) : l ++ a <+: l ++ b := by
  obtain ⟨t, ht⟩ := h; exact ⟨t, by rw [List.append_assoc, ht]⟩

theorem TRun.seqT_grows (a : TRun) (k : UState → TRun) :
    a.ev <+: (a.seqT k).ev ∧ a.lk <+: (a.seqT k).lk ∧ a.cost ≤ (a.seqT k).cost := by
  unfold TRun.seqT
  split
  · exact ⟨List.prefix_append _ _, List.prefix_append _ _, Nat.le_add_right _ _⟩
  · exact ⟨List.prefix_refl _, List.prefix_refl _, Nat.le_refl _⟩

theorem TRun.seqT_ext {a a' : TRun} {k k' : UState → TRun} (h : a.Ext a')
    (hk : a.out = .done → (k a.st).Ext (k' a.st)) : (a.seqT k).Ext (a'.seqT k') := by
  by_cases ha : a.out = .done
  · have heq : a = a' := h.1 (by rw [ha]; decide)
    subst heq
    obtain ⟨h1, h2, h3, h4⟩ := hk ha
    unfold TRun.seqT
    simp only [ha, ↓reduceIte]
    refine ⟨fun hf => ?_, prefix_append_both _ h2, prefix_append_both _ h3,
      Nat.add_le_add_left h4 _⟩
    rw [h1 hf]
  · by_cases hf : a.out = .fuel
    · obtain ⟨g1, g2, g3⟩ := TRun.seqT_grows a' k'
      have hs : a.seqT k = a := by unfold TRun.seqT; rw [ite_eq_right ha]
      rw [hs]
      exact ⟨fun h' => absurd hf h', h.2.1.trans g1, h.2.2.1.trans g2, Nat.le_trans h.2.2.2 g3⟩
    · have heq : a = a' := h.1 hf
      subst heq
      have hs : a.seqT k = a := by unfold TRun.seqT; rw [ite_eq_right ha]
      have hs' : a.seqT k' = a := by unfold TRun.seqT; rw [ite_eq_right ha]
      rw [hs, hs']; exact TRun.Ext.refl _

theorem TRun.tick_ext {a a' : TRun} (l : LCore.Lk) (h : a.Ext a') : (a.tick l).Ext (a'.tick l) := by
  refine ⟨fun hf => ?_, h.2.1, ?_, Nat.add_le_add_left h.2.2.2 _⟩
  · rw [h.1 hf]
  · obtain ⟨t, ht⟩ := h.2.2.1; exact ⟨t, by simp only [TRun.tick, List.cons_append, ht]⟩

/-- **More fuel only extends a run.** -/
theorem uexecT_ext : ∀ (n n' : Nat) (c : UCmd) (π : MedPolicy) (s : UState), n ≤ n' →
    (uexecT n c π s).Ext (uexecT n' c π s) := by
  intro n
  induction n with
  | zero =>
    intro n' c π s _
    exact ⟨fun h => absurd rfl h, List.nil_prefix, List.nil_prefix, Nat.zero_le _⟩
  | succ m ih =>
    intro n' c π s hle
    obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
    have hm : m ≤ m' := by omega
    cases c with
    | seq c₁ c₂ =>
      simp only [uexecT]; split
      · exact TRun.Ext.refl _
      · exact TRun.seqT_ext (ih m' c₁ π s hm) (fun _ => ih m' c₂ π _ hm)
    | ite e c₁ c₂ =>
      simp only [uexecT]; split
      · exact TRun.Ext.refl _
      · exact TRun.tick_ext _ (ih m' _ π s hm)
    | loop e b =>
      simp only [uexecT]; split
      · exact TRun.Ext.refl _
      · split
        · exact TRun.tick_ext _ (TRun.seqT_ext (ih m' b π s hm) (fun _ => ih m' _ π _ hm))
        · exact TRun.Ext.refl _
    | _ => simp only [uexecT]; split <;> exact TRun.Ext.refl _

/-! ## A run that runs out of fuel has paid for it -/

def tsize : UCmd → Nat
  | .seq c₁ c₂   => 1 + tsize c₁ + tsize c₂
  | .ite _ c₁ c₂ => 1 + tsize c₁ + tsize c₂
  | .loop _ b    => 1 + tsize b
  | _            => 1

theorem TRun.seqT_fuel {a : TRun} {k : UState → TRun} (h : (a.seqT k).out = .fuel) :
    (a.out = .done ∧ (k a.st).out = .fuel ∧ (a.seqT k).cost = a.cost + (k a.st).cost)
    ∨ (a.out = .fuel ∧ a.seqT k = a) := by
  unfold TRun.seqT at *
  by_cases ha : a.out = .done
  · simp only [ha, ↓reduceIte] at h ⊢; exact Or.inl ⟨trivial, h, trivial⟩
  · simp only [ha, ↓reduceIte] at h ⊢; exact Or.inr ⟨h, trivial⟩

/-- An atomic step that `uexec` completes does not run out of fuel. -/
theorem stepT_ne {c : UCmd} {π : MedPolicy} {s : UState} (h : uexec 1 c π s ≠ none) :
    (stepT c π s).out ≠ .fuel := by
  unfold stepT
  cases e : uexec 1 c π s with
  | none => exact absurd e h
  | some r => by_cases hd : r.1.dead = true <;> simp [hd]

/-- **Out of fuel at `n` means at least `n - tsize c` was spent.** -/
theorem uexecT_diverge : ∀ (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState),
    (uexecT n c π s).out = .fuel → n ≤ (uexecT n c π s).cost + tsize c := by
  intro n
  induction n with
  | zero => intro c π s _; exact Nat.zero_le _
  | succ m ih =>
    intro c π s h
    cases c with
    | seq c₁ c₂ =>
      simp only [uexecT] at h ⊢
      split at h
      · cases h
      · rename_i hd; simp only [hd, Bool.false_eq_true, ↓reduceIte]
        rcases TRun.seqT_fuel h with ⟨_, h₂, hc⟩ | ⟨h₁, he⟩
        · have := ih c₂ π _ h₂; rw [hc]; simp only [tsize]; omega
        · have := ih c₁ π s h₁; rw [he]; simp only [tsize]; omega
    | ite e c₁ c₂ =>
      simp only [uexecT] at h ⊢
      split at h
      · cases h
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte, TRun.tick] at h ⊢
        by_cases hg : evalE e s.store ≠ 0
        · have h' := h; rw [ite_eq_left hg] at h'
          have := ih c₁ π s h'; rw [ite_eq_left hg]; simp only [tsize]; omega
        · have h' := h; rw [ite_eq_right hg] at h'
          have := ih c₂ π s h'; rw [ite_eq_right hg]; simp only [tsize]; omega
    | loop e b =>
      simp only [uexecT] at h ⊢
      split at h
      · cases h
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hg : evalE e s.store ≠ 0
        · rw [ite_eq_left hg] at h ⊢
          simp only [TRun.tick] at h ⊢
          rcases TRun.seqT_fuel h with ⟨_, h₂, hc⟩ | ⟨h₁, he⟩
          · have := ih _ π _ h₂; rw [hc]; simp only [tsize] at this ⊢; omega
          · have := ih b π s h₁; rw [he]; simp only [tsize]; omega
        · rw [ite_eq_right hg] at h; cases h
    | _ =>
      simp only [uexecT] at h
      split at h
      · cases h
      · exact absurd h (stepT_ne (by simp [uexec]))

/-! ## The language -/

/-- **UCmd as a lawful L `Lang`**: halting abort, one trace in program order. -/
def ucmdLangT (P : Partition) (π : MedPolicy) : LCore.Lang where
  Prog  := UCmd
  In    := Store
  lowIn := lowEq P
  run n c σ :=
    let r := uexecT n c π (initU σ)
    { ev := r.ev, lk := r.lk, cost := r.cost, out := r.out }

theorem ucmdLangT_lawful (P : Partition) (π : MedPolicy) : (ucmdLangT P π).Lawful where
  ev_mono c σ n n' h := (uexecT_ext n n' c π (initU σ) h).2.1
  lk_mono c σ n n' h := (uexecT_ext n n' c π (initU σ) h).2.2.1
  cost_mono c σ n n' h := (uexecT_ext n n' c π (initU σ) h).2.2.2
  stable c σ n n' h hf := by
    have := (uexecT_ext n n' c π (initU σ) h).1 hf
    show ({ ev := _, lk := _, cost := _, out := _ } : LCore.Beh) = { ev := _, lk := _, cost := _, out := _ }
    rw [this]
  diverge c := ⟨tsize c, fun n σ h => uexecT_diverge n c π (initU σ) h⟩

/-! ## The bridge to `uexec` -/

/-- The branch bits of a leakage trace, in order. -/
def lkBr : List LCore.Lk → List Bool :=
  List.filterMap fun | .branch b => some b | _ => none

/-- The addresses of a leakage trace, in order. -/
def lkAddr : List LCore.Lk → List Int :=
  List.filterMap fun | .addr a => some a | _ => none

def atomic : UCmd → Bool
  | .seq .. | .ite .. | .loop .. => false
  | _ => true

set_option hygiene false in
local macro "agree_tac" : tactic =>
  `(tactic| (simp only [stepT, uexec, uaddrs] at h ⊢; (repeat (split at h)) <;>
              simp_all [lkBr, lkAddr, List.filterMap_map]))

/-- An atomic step that finishes is `uexec`'s and `uaddrs`'s step, at any fuel. -/
theorem stepT_done_agree (c : UCmd) (hc : atomic c = true) (n : Nat) (π : MedPolicy) (s : UState)
    (h : (stepT c π s).out = .done) :
    uexec (n + 1) c π s = some ((stepT c π s).st, (stepT c π s).cost, lkBr (stepT c π s).lk)
  ∧ uaddrs (n + 1) c π s = some (lkAddr (stepT c π s).lk) := by
  cases c with
  | seq | ite | loop => simp [atomic] at hc
  | memop op x => cases op <;> agree_tac
  | hop op x y => cases op <;> agree_tac
  | sop op x e => cases op <;> agree_tac
  | _ => agree_tac

theorem TRun.seqT_done {a : TRun} {k : UState → TRun} (h : (a.seqT k).out = .done) :
    a.out = .done ∧ (k a.st).out = .done ∧
    a.seqT k = ⟨(k a.st).st, a.cost + (k a.st).cost, a.ev ++ (k a.st).ev,
                a.lk ++ (k a.st).lk, (k a.st).out⟩ := by
  unfold TRun.seqT at *
  by_cases ha : a.out = .done
  · simp only [ha, ↓reduceIte] at h ⊢; exact ⟨trivial, h, trivial⟩
  · simp only [ha, ↓reduceIte] at h

/-- **The bridge.** A `uexecT` run that finishes normally is a finished `uexec` run: same
    final state, same cost, its branch bits, and its addresses. So every theorem about
    finished `uexec` runs applies to it. -/
theorem uexecT_done_agree : ∀ (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState),
    (uexecT n c π s).out = .done →
      uexec n c π s = some ((uexecT n c π s).st, (uexecT n c π s).cost, lkBr (uexecT n c π s).lk)
    ∧ uaddrs n c π s = some (lkAddr (uexecT n c π s).lk) := by
  intro n
  induction n with
  | zero => intro c π s h; cases h
  | succ m ih =>
    intro c π s h
    cases c with
    | seq c₁ c₂ =>
      simp only [uexecT] at h ⊢
      split at h
      · cases h
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
        obtain ⟨ha, hb, he⟩ := TRun.seqT_done h
        obtain ⟨u₁, a₁⟩ := ih c₁ π s ha
        obtain ⟨u₂, a₂⟩ := ih c₂ π _ hb
        rw [he]
        refine ⟨?_, ?_⟩
        · rw [uexec_seq_eq, u₁, Option.bind_some, u₂, Option.map_some]
          simp [lkBr, List.filterMap_append]
        · simp only [uaddrs, u₁, a₁, a₂, Option.bind_some, Option.map_some, lkAddr,
            List.filterMap_append]
    | ite e c₁ c₂ =>
      simp only [uexecT] at h ⊢
      split at h
      · cases h
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte, TRun.tick] at h ⊢
        by_cases hg : evalE e s.store ≠ 0
        · rw [ite_eq_left hg] at h ⊢
          obtain ⟨u, a⟩ := ih c₁ π s h
          refine ⟨?_, ?_⟩
          · rw [uexec_ite_eq, ite_eq_left hg, u, Option.map_some]
            simp [lkBr, hg]
          · simp only [uaddrs, ite_eq_left hg, a, lkAddr, List.filterMap_cons]
        · rw [ite_eq_right hg] at h ⊢
          obtain ⟨u, a⟩ := ih c₂ π s h
          refine ⟨?_, ?_⟩
          · rw [uexec_ite_eq, ite_eq_right hg, u, Option.map_some]
            simp [lkBr, hg]
          · simp only [uaddrs, ite_eq_right hg, a, lkAddr, List.filterMap_cons]
    | loop e b =>
      simp only [uexecT] at h ⊢
      split at h
      · cases h
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hg : evalE e s.store ≠ 0
        · rw [ite_eq_left hg] at h ⊢
          simp only [TRun.tick] at h ⊢
          obtain ⟨ha, hb, he⟩ := TRun.seqT_done h
          obtain ⟨u₁, a₁⟩ := ih b π s ha
          obtain ⟨u₂, a₂⟩ := ih _ π _ hb
          rw [he]
          refine ⟨?_, ?_⟩
          · rw [uexec_loop_eq, ite_eq_left hg, u₁, Option.bind_some, u₂, Option.map_some]
            simp [lkBr, List.filterMap_append, Nat.add_assoc]
          · simp only [uaddrs, ite_eq_left hg, u₁, a₁, a₂, Option.bind_some, Option.map_some,
              lkAddr, List.filterMap_cons, List.filterMap_append]
        · rw [ite_eq_right hg] at h ⊢
          refine ⟨?_, ?_⟩
          · rw [uexec_loop_eq, ite_eq_right hg]; rfl
          · simp only [uaddrs, ite_eq_right hg]; rfl
    | _ =>
      simp only [uexecT] at h ⊢
      split at h
      · cases h
      · rename_i hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact stepT_done_agree _ rfl m π s h

end ConfTyping
