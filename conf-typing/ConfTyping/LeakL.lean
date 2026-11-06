/-
  Memory leaks on L (F5, row 6): `ucmdLangH`, and `leakSafe`'s `Cert.trace` on it.

  `leakSafe_sound` is about `uexec`'s final state, and `Beh` has no final heap, so on `ucmdLangS` a leak
  cannot be observed or stated. `faultEv` was added to L for the same reason. `ucmdLangH` is `urunS`,
  unchanged, plus an exit report: `leakEv` when a run finishes with memory still allocated. Runs start
  with nothing allocated, so that is exactly a leak. Everything but the report is `ucmdLangS`
  (`ucmdLangH_strip`).

  **Observer:** the exit report, like a leak checker at process exit.

  **Limits.** A run that aborts is not covered, as in `LeakCert`: `allocThenCheck` is accepted, and when
  the policy refuses its `check` the run ends with memory allocated and no report
  (`allocThenCheck_abort_unreported`). `splitPass` is over `ucmdLangS`, so this certificate is not
  carried through a pass.
-/
import ConfTyping.UStep
import ConfTyping.LeakCert

namespace ConfTyping.Leak

/-! ## The language -/

/-- What the exit report shows: memory was still allocated. -/
def leakEv : LCore.Ev := .ext "leak" []

/-- A finished run reports if it left anything allocated. An aborted or unfinished run reports nothing. -/
def exitReport (r : TRun) : List LCore.Ev :=
  if r.out = .done ∧ r.st.live.isEmpty = false then [leakEv] else []

/-- **UCmd with an exit report** as an L `Lang`. -/
def ucmdLangH (P : Partition) (π : MedPolicy) : LCore.Lang where
  Prog  := UCmd
  In    := Store
  lowIn := lowEq P
  run n c σ :=
    let r := urunS π n (push c [] []) (initU σ)
    { ev := r.ev ++ exitReport r, lk := r.lk, cost := r.cost, out := r.out }

theorem exitReport_fuel {r : TRun} (h : r.out = .fuel) : exitReport r = [] := by
  simp [exitReport, h]

theorem ucmdLangH_lawful (P : Partition) (π : MedPolicy) : (ucmdLangH P π).Lawful where
  ev_mono c σ n n' h := by
    have he := runS_ext π n n' (push c [] []) (initU σ) h
    show (urunS π n _ _).ev ++ exitReport _ <+: (urunS π n' _ _).ev ++ exitReport _
    by_cases hf : (urunS π n (push c [] []) (initU σ)).out = .fuel
    · rw [exitReport_fuel hf, List.append_nil]
      exact he.2.1.trans (List.prefix_append _ _)
    · rw [he.1 hf]; exact List.prefix_refl _
  lk_mono c σ n n' h := (runS_ext π n n' _ _ h).2.2.1
  cost_mono c σ n n' h := (runS_ext π n n' _ _ h).2.2.2
  stable c σ n n' h hf := by
    have := (runS_ext π n n' (push c [] []) (initU σ) h).1 hf
    show ({ ev := _, lk := _, cost := _, out := _ } : LCore.Beh) = { ev := _, lk := _, cost := _, out := _ }
    rw [this]
  diverge c := ⟨0, fun n σ h =>
    runS_diverge π n (push c [] []) (initU σ) (push_noSeq c [] [] (by simp [NoSeq])) h⟩

/-- **The report adds an observer and changes nothing else.** -/
theorem ucmdLangH_strip (P : Partition) (π : MedPolicy) (n : Nat) (c : UCmd) (σ : Store) :
    ((ucmdLangH P π).run n c σ).lk = ((ucmdLangS P π).run n c σ).lk
  ∧ ((ucmdLangH P π).run n c σ).cost = ((ucmdLangS P π).run n c σ).cost
  ∧ ((ucmdLangH P π).run n c σ).out = ((ucmdLangS P π).run n c σ).out
  ∧ (((ucmdLangH P π).run n c σ).ev = ((ucmdLangS P π).run n c σ).ev
    ∨ ((ucmdLangH P π).run n c σ).ev = ((ucmdLangS P π).run n c σ).ev ++ [leakEv]) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show (urunS π n _ _).ev ++ exitReport _ = (urunS π n _ _).ev
    ∨ (urunS π n _ _).ev ++ exitReport _ = (urunS π n _ _).ev ++ [leakEv]
  unfold exitReport
  split
  · exact Or.inr rfl
  · exact Or.inl (List.append_nil _)

/-! ## No program can write the report itself -/

theorem stepT_no_leak (c : UCmd) (π : MedPolicy) (s : UState) : leakEv ∉ (stepT c π s).ev := by
  have hs : leakEv ∉ stepEv c s := by
    cases c with
    | sop op x e => cases op <;> simp [stepEv, leakEv]
    | _ => simp [stepEv, leakEv]
  unfold stepT
  split
  · simp only [List.mem_append, not_or]
    refine ⟨hs, ?_⟩
    split <;> simp [faultEv, leakEv]
  · simp

theorem runS_no_leak (π : MedPolicy) : ∀ (n : Nat) (k : List UFrame) (s : UState),
    leakEv ∉ (urunS π n k s).ev := by
  intro n
  induction n with
  | zero => intro k s; cases k <;> simp [urunS]
  | succ m ih =>
    intro k s
    cases k with
    | nil => simp [urunS]
    | cons f k =>
      obtain ⟨c, p⟩ := f
      by_cases hd : s.dead = true
      · simp [urunS, hd]
      cases c with
      | seq a b => simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte]; exact ih _ s
      | ite e a b =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte, TRun.tickS]; exact ih _ s
      | loop e b =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte]
        split <;> (simp only [TRun.tickS]; exact ih _ s)
      | _ =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte, TRun.atomS]
        split
        · simp only [List.mem_append, not_or]
          exact ⟨stepT_no_leak _ _ _, ih _ _⟩
        · exact stepT_no_leak _ _ _

/-! ## `lcheck` over the frame stack -/

/-- A frame stack `lcheck` accepts, ending with nothing outstanding. A later frame may track more than
    an earlier one ended with, which is what a loop or the arms of a branch need. -/
inductive LF : List String → List UFrame → Prop where
  | nil  : LF [] []
  | cons : ∀ {O O₁ O₂ : List String} {c : UCmd} {p : List Nat} {k : List UFrame},
      lcheck O c = some O₁ → (∀ x, memStr x O₁ = true → memStr x O₂ = true) → LF O₂ k →
      LF O ((c, p) :: k)

theorem Owned.mono {O O' : List String} {s₀ s : UState}
    (hsub : ∀ x, memStr x O = true → memStr x O' = true) (h : Owned O s₀ s) : Owned O' s₀ s := by
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun a ha => ?_
    rcases h a ha with h₀ | ⟨x, hx, hs⟩
    · exact Or.inl h₀
    · exact Or.inr ⟨x, hsub x hx, hs⟩

theorem push_lf : ∀ (c : UCmd) (p : List Nat) {O O₁ O₂ : List String} {k : List UFrame},
    lcheck O c = some O₁ → (∀ x, memStr x O₁ = true → memStr x O₂ = true) → LF O₂ k →
    LF O (push c p k)
  | .seq a b, p, O, O₁, O₂, k, hc, hsub, hk => by
    simp only [lcheck] at hc
    rcases ea : lcheck O a with _ | Oa
    · rw [ea] at hc; simp at hc
    · rw [ea, Option.bind_some] at hc
      exact push_lf a _ ea (fun _ h => h) (push_lf b _ hc hsub hk)
  | .skip, _, _, _, _, _, hc, hsub, hk | .assign _ _, _, _, _, _, _, hc, hsub, hk
  | .check _, _, _, _, _, _, hc, hsub, hk | .access _, _, _, _, _, _, hc, hsub, hk
  | .memop _ _, _, _, _, _, _, hc, hsub, hk | .sop _ _ _, _, _, _, _, _, hc, hsub, hk
  | .hop _ _ _, _, _, _, _, _, hc, hsub, hk | .ite _ _ _, _, _, _, _, _, hc, hsub, hk
  | .loop _ _, _, _, _, _, _, hc, hsub, hk => LF.cons hc hsub hk

theorem eqStr_left {A B : List String} (h : eqStr A B = true) (x : String) :
    memStr x A = true → memStr x B = true := by
  simp only [eqStr, Bool.and_eq_true] at h
  exact memStr_of_subStr h.1

theorem eqStr_right {A B : List String} (h : eqStr A B = true) (x : String) :
    memStr x B = true → memStr x A = true := by
  simp only [eqStr, Bool.and_eq_true] at h
  exact memStr_of_subStr h.2

/-- A finished atomic step is `uexec`'s, and the machine is still alive. -/
theorem stepT_done {c : UCmd} {π : MedPolicy} {s : UState} (h : (stepT c π s).out = .done) :
    (stepT c π s).st.dead = false ∧ ∃ k t, uexec 1 c π s = some ((stepT c π s).st, k, t) := by
  unfold stepT at h ⊢
  rcases e : uexec 1 c π s with _ | r
  · simp [e] at h
  · simp only [e] at h ⊢
    refine ⟨?_, r.2.1, r.2.2, rfl⟩
    cases hd : r.1.dead
    · rfl
    · simp [hd] at h

/-- **A finished run left nothing but what it started with.** -/
theorem runS_owned (π : MedPolicy) (s₀ : UState) : ∀ (n : Nat) (O : List String) (k : List UFrame)
    (s : UState), LF O k → Owned O s₀ s → s.dead = false → (urunS π n k s).out = .done →
    ∀ a, memInt a (urunS π n k s).st.live = true → memInt a s₀.live = true := by
  have hnil : ∀ (s : UState) (O : List String), LF O [] → Owned O s₀ s → s.dead = false →
      ∀ a, memInt a s.live = true → memInt a s₀.live = true := by
    intro s O hk hown hd a ha
    cases hk
    rcases hown with h | h
    · rw [hd] at h; cases h
    · rcases h a ha with h₀ | ⟨_, hx, _⟩
      · exact h₀
      · simp [memStr] at hx
  intro n
  induction n with
  | zero =>
    intro O k s hk hown hd hout a ha
    cases k with
    | nil => exact hnil s O hk hown hd a ha
    | cons f k => simp [urunS] at hout
  | succ m ih =>
    intro O k s hk hown hd hout a ha
    cases k with
    | nil => exact hnil s O hk hown hd a ha
    | cons f k =>
      obtain ⟨c, p⟩ := f
      obtain _ | ⟨hc, hsub, hk'⟩ := hk
      cases c with
      | seq x y =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte] at hout ha
        exact ih _ _ s (push_lf (.seq x y) p hc hsub hk') hown hd hout a ha
      | ite e x y =>
        simp only [lcheck] at hc
        rcases ex : lcheck O x with _ | Ox
        · rw [ex] at hc; simp at hc
        rw [ex, Option.bind_some] at hc
        rcases ey : lcheck O y with _ | Oy
        · rw [ey] at hc; simp at hc
        rw [ey, Option.bind_some] at hc
        split at hc
        · rename_i heq
          simp only [Option.some.injEq] at hc
          subst hc
          simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte, TRun.tickS] at hout ha
          by_cases hg : evalE e s.store ≠ 0
          · simp only [ite_eq_left hg] at hout ha
            exact ih _ _ s (push_lf x _ ex hsub hk') hown hd hout a ha
          · simp only [ite_eq_right hg] at hout ha
            exact ih _ _ s (push_lf y _ ey
              (fun z hz => hsub z (eqStr_right heq z hz)) hk') hown hd hout a ha
        · simp at hc
      | loop e b =>
        have hc0 := hc
        simp only [lcheck] at hc
        rcases eb : lcheck O b with _ | Ob
        · rw [eb] at hc; simp at hc
        rw [eb, Option.bind_some] at hc
        split at hc
        · rename_i heq
          simp only [Option.some.injEq] at hc
          subst hc
          simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte] at hout ha
          by_cases hg : evalE e s.store ≠ 0
          · simp only [ite_eq_left hg, TRun.tickS] at hout ha
            exact ih _ _ s (push_lf b _ eb (eqStr_left heq) (LF.cons hc0 hsub hk')) hown hd hout a ha
          · simp only [ite_eq_right hg, TRun.tickS] at hout ha
            exact ih _ _ s hk' (Owned.mono hsub hown) hd hout a ha
        · simp at hc
      | _ =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte, TRun.atomS] at hout ha
        split at hout
        · rename_i hdone
          simp only [hdone, ↓reduceIte] at hout ha
          obtain ⟨hd', k₁, t, hu⟩ := stepT_done hdone
          exact ih _ _ _ hk' (Owned.mono hsub (lcheck_owned 1 _ π _ _ s₀ s _ k₁ t hc hu hown))
            hd' hout a ha
        · rename_i hdone
          exact absurd hout hdone

/-! ## The certificate -/

/-- **Row 6 on L.** What `leakSafe` accepts never shows a leak in its exit report: a run that finishes
    has freed everything it allocated. It needs no `bcheck`, so loops need not be bounded. -/
theorem leakSafe_traceH {P : Partition} {c : UCmd} (h : leakSafe c = true) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangH P π) (fun evs => leakEv ∉ evs) c := by
  intro n σ _
  have hlc : lcheck [] c = some [] := by
    simp only [leakSafe] at h
    rcases lc : lcheck [] c with _ | O
    · rw [lc] at h; simp at h
    · rw [lc] at h
      cases O with
      | nil => rfl
      | cons y ys => simp [List.isEmpty] at h
  show leakEv ∉ (urunS π n _ _).ev ++ exitReport _
  simp only [List.mem_append, not_or]
  refine ⟨runS_no_leak π _ _ _, ?_⟩
  unfold exitReport
  split
  · rename_i hend
    obtain ⟨hdone, hne⟩ := hend
    exfalso
    have hown : Owned [] (initU σ) (initU σ) := Or.inr fun a ha => Or.inl ha
    have key := runS_owned π (initU σ) n [] _ (initU σ)
      (push_lf c [] hlc (fun _ h => h) LF.nil) hown rfl hdone
    cases hl : (urunS π n (push c [] []) (initU σ)).st.live with
    | nil => rw [hl] at hne; simp at hne
    | cons x xs =>
      have hx := key x (by rw [hl]; simp [memInt])
      simp [initU, memInt] at hx
  · simp

/-! ## Witnesses -/

/-- A store with `v` in the variable the programs below branch on. -/
def storeOf (x : String) (v : Int) : Store := fun y => if y == x then v else 0

/-- **Accepted**: both arms free. -/
theorem b06fixed_traceH (P : Partition) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangH P π) (fun evs => leakEv ∉ evs) b06fixed :=
  leakSafe_traceH b06fixed_accepted π

/-- **Accepted, and it may never finish**, so this is more than `bcheck` could reach. -/
theorem loop_balanced_traceH (P : Partition) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangH P π) (fun evs => leakEv ∉ evs)
      (.loop (.var "c") (.seq (.memop .alloc "x") (.memop .free "x"))) :=
  leakSafe_traceH loop_balanced_accepted π

/-- The accepted programs do reach the report's check: `b06fixed` finishes. -/
theorem b06fixed_finishes :
    ((ucmdLangH (fun _ => false) (fun _ => true)).run 20 b06fixed (storeOf "fail" 1)).out = .done := by
  decide

/-- **Refused, and it leaks**: CWE-401's error path, the program the map admitted was accepted. -/
theorem b06_leaks : ¬ LCore.Cert.trace (ucmdLangH (fun _ => false) (fun _ => true))
    (fun evs => leakEv ∉ evs) b06 := by
  intro h
  have : leakEv ∉ ((ucmdLangH (fun _ => false) (fun _ => true)).run 20 b06 (storeOf "fail" 1)).ev :=
    h 20 _ trivial
  exact this (by decide)

/-- An allocation in a loop body. -/
def loopAlloc : UCmd := .loop (.var "c") (.seq (.memop .alloc "x") (.assign "c" (.num 0)))

theorem loopAlloc_refused : leakSafe loopAlloc = false := by decide

theorem loopAlloc_leaks : ¬ LCore.Cert.trace (ucmdLangH (fun _ => false) (fun _ => true))
    (fun evs => leakEv ∉ evs) loopAlloc := by
  intro h
  have : leakEv ∉ ((ucmdLangH (fun _ => false) (fun _ => true)).run 20 loopAlloc (storeOf "c" 1)).ev :=
    h 20 _ trivial
  exact this (by decide)

/-- Overwriting the only handle. -/
def overwrite : UCmd := .seq (.memop .alloc "p") (.assign "p" (.num 0))

theorem overwrite_leaks : ¬ LCore.Cert.trace (ucmdLangH (fun _ => false) (fun _ => true))
    (fun evs => leakEv ∉ evs) overwrite := by
  intro h
  have : leakEv ∉ ((ucmdLangH (fun _ => false) (fun _ => true)).run 20 overwrite (storeOf "c" 0)).ev :=
    h 20 _ trivial
  exact this (by decide)

/-- **The limit.** `allocThenCheck` is accepted. When the policy refuses its `check`, the run aborts
    with memory still allocated, and the report says nothing. -/
theorem allocThenCheck_abort_unreported :
    leakSafe allocThenCheck = true
  ∧ (urunS (fun _ => false) 20 (push allocThenCheck [] []) (initU (storeOf "c" 0))).out = .abort
  ∧ (urunS (fun _ => false) 20 (push allocThenCheck [] []) (initU (storeOf "c" 0))).st.live ≠ []
  ∧ leakEv ∉ ((ucmdLangH (fun _ => false) (fun _ => false)).run 20 allocThenCheck (storeOf "c" 0)).ev := by
  decide

end ConfTyping.Leak
