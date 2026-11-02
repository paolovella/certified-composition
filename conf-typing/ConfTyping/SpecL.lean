/-
  Speculative execution on L (F5, row 9): `ucmdLangW`, and `bcheck`'s `Cert.rel` on it.

  `certified_trace_is_low` is about `uexecS`, a big-step machine with its own trace, so it is not an
  L `Lang`, and it needs `xcheck`, which is loop-free through `allcheck`. `urunW` is `urunS` plus one
  thing: at an `ite` the untaken branch runs for up to `w` commands on `transRun`. Its state is
  discarded; the addresses it touched join the leakage and its commands join the cost. At window 0 it
  is `ucmdLangS` (`ucmdLangW_zero`), so speculation adds an attacker and changes nothing else.

  **Attacker:** picks the window, and sees every channel and all leakage, including the addresses a
  mispredicted branch touches, and the real cost, including transient commands.

  **Limits**, the same as `SpecFused`'s: one global window, correctly predicted loop guards, no nested
  speculation (`flatten` runs a nested `ite` or `loop` as one step, touching nothing), and addresses
  and step counts only, so no cache lines, eviction, contention, v2 or v4. The `Cert.bound` of
  `bcheck` is not restated here, since real cost now grows with the window. `splitPass` is over
  `ucmdLangS`, so this certificate is not carried through a pass.
-/
import ConfTyping.Split
import ConfTyping.SpecFused

namespace ConfTyping.Spec

/-! ## The machine -/

/-- A transient window's addresses and commands, ahead of the rest of the run. -/
def specW (ts : List Int) (m : Nat) (r : TRun) : TRun :=
  ⟨r.st, m + r.cost, r.ev, ts.map .addr ++ r.lk, r.out⟩

/-- **`urunS` with a mispredicted `ite`**, for window `w`. Each `ite` first runs the branch it will
    not take. The loop guard is predicted correctly. -/
def urunW (π : MedPolicy) (w : Nat) : Nat → List UFrame → UState → TRun
  | _,     [],          s => ⟨s, 0, [], [], .done⟩
  | 0,     _ :: _,      s => ⟨s, 0, [], [], .fuel⟩
  | n + 1, (c, p) :: k, s =>
    if s.dead then ⟨s, 0, [], [], .abort⟩ else
    match c with
    | .seq a b => urunW π w n (push a (p ++ [0]) (push b (p ++ [1]) k)) s
    | .ite e a b =>
        if evalE e s.store ≠ 0 then
          TRun.tickS (.branch true) p
            (specW (transRun w (flatten b) π s) (transSteps w (flatten b) π s)
              (urunW π w n (push a (p ++ [0]) k) s))
        else
          TRun.tickS (.branch false) p
            (specW (transRun w (flatten a) π s) (transSteps w (flatten a) π s)
              (urunW π w n (push b (p ++ [1]) k) s))
    | .loop e b =>
        if evalE e s.store ≠ 0 then
          TRun.tickS (.branch true) p (urunW π w n (push b (p ++ [0]) ((.loop e b, p) :: k)) s)
        else TRun.tickS (.branch false) p (urunW π w n k s)
    | c => (stepT c π s).atomS p (fun t => urunW π w n k t)

/-- **UCmd under misprediction** as an L `Lang`. -/
def ucmdLangW (P : Partition) (π : MedPolicy) (w : Nat) : LCore.Lang where
  Prog  := UCmd
  In    := Store
  lowIn := lowEq P
  run n c σ :=
    let r := urunW π w n (push c [] []) (initU σ)
    { ev := r.ev, lk := r.lk, cost := r.cost, out := r.out }

/-! ## Lawful -/

theorem specW_ext {a a' : TRun} (ts : List Int) (m : Nat) (h : a.Ext a') :
    (specW ts m a).Ext (specW ts m a') := by
  refine ⟨fun hf => ?_, h.2.1, prefix_append_both _ h.2.2.1, Nat.add_le_add_left h.2.2.2 _⟩
  rw [h.1 hf]

theorem runW_ext (π : MedPolicy) (w : Nat) : ∀ (n n' : Nat) (k : List UFrame) (s : UState), n ≤ n' →
    (urunW π w n k s).Ext (urunW π w n' k s) := by
  intro n
  induction n with
  | zero =>
    intro n' k s _
    cases k with
    | nil => cases n' <;> exact TRun.Ext.refl _
    | cons f k => exact ⟨fun h => absurd rfl h, List.nil_prefix, List.nil_prefix, Nat.zero_le _⟩
  | succ m ih =>
    intro n' k s hle
    obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
    have hm : m ≤ m' := by omega
    cases k with
    | nil => exact TRun.Ext.refl _
    | cons f k =>
      obtain ⟨c, p⟩ := f
      by_cases hd : s.dead = true
      · simp only [urunW, hd, ↓reduceIte]; exact TRun.Ext.refl _
      cases c with
      | seq a b => simp only [urunW, hd, Bool.false_eq_true, ↓reduceIte]; exact ih m' _ s hm
      | ite e a b =>
        simp only [urunW, hd, Bool.false_eq_true, ↓reduceIte]
        split
        · exact TRun.tickS_ext _ _ (specW_ext _ _ (ih m' _ s hm))
        · exact TRun.tickS_ext _ _ (specW_ext _ _ (ih m' _ s hm))
      | loop e b =>
        simp only [urunW, hd, Bool.false_eq_true, ↓reduceIte]
        split
        · exact TRun.tickS_ext _ _ (ih m' _ s hm)
        · exact TRun.tickS_ext _ _ (ih m' _ s hm)
      | _ =>
        simp only [urunW, hd, Bool.false_eq_true, ↓reduceIte]
        exact TRun.atomS_ext _ _ (fun _ => ih m' _ _ hm)

theorem runW_diverge (π : MedPolicy) (w : Nat) : ∀ (n : Nat) (k : List UFrame) (s : UState), NoSeq k →
    (urunW π w n k s).out = .fuel → n ≤ (urunW π w n k s).cost := by
  intro n
  induction n with
  | zero => intro _ _ _ _; exact Nat.zero_le _
  | succ m ih =>
    intro k s hk hf
    cases k with
    | nil => simp [urunW] at hf
    | cons f k =>
      obtain ⟨c, p⟩ := f
      have hk' : NoSeq k := fun x hx => hk x (List.mem_cons_of_mem _ hx)
      by_cases hd : s.dead = true
      · simp [urunW, hd] at hf
      cases c with
      | seq a b => exact absurd rfl (hk _ (List.mem_cons_self) a b)
      | ite e a b =>
        simp only [urunW, hd, Bool.false_eq_true, ↓reduceIte] at hf ⊢
        split at hf
        · rename_i hg; rw [ite_eq_left hg]; simp only [TRun.tickS, specW] at hf ⊢
          have := ih _ s (push_noSeq _ _ _ hk') hf; omega
        · rename_i hg; rw [ite_eq_right hg]; simp only [TRun.tickS, specW] at hf ⊢
          have := ih _ s (push_noSeq _ _ _ hk') hf; omega
      | loop e b =>
        simp only [urunW, hd, Bool.false_eq_true, ↓reduceIte] at hf ⊢
        split at hf
        · rename_i hg; rw [ite_eq_left hg]; simp only [TRun.tickS] at hf ⊢
          have hk2 : NoSeq ((UCmd.loop e b, p) :: k) := by
            intro x hx a' b'; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp
            · exact hk' x hx a' b'
          have := ih _ s (push_noSeq _ _ _ hk2) hf
          omega
        · rename_i hg; rw [ite_eq_right hg]; simp only [TRun.tickS] at hf ⊢
          have := ih _ s hk' hf; omega
      | _ =>
        simp only [urunW, hd, Bool.false_eq_true, ↓reduceIte, TRun.atomS] at hf ⊢
        split at hf
        · rename_i hdone; simp only [hdone, ↓reduceIte] at hf ⊢
          have := ih _ _ hk' hf
          rw [stepT_cost_one _ rfl]; omega
        · rename_i hdone; simp only [hdone, ↓reduceIte] at hf ⊢
          exact absurd hf (stepT_ne (by simp [uexec]))

theorem ucmdLangW_lawful (P : Partition) (π : MedPolicy) (w : Nat) : (ucmdLangW P π w).Lawful where
  ev_mono c σ n n' h := (runW_ext π w n n' _ _ h).2.1
  lk_mono c σ n n' h := (runW_ext π w n n' _ _ h).2.2.1
  cost_mono c σ n n' h := (runW_ext π w n n' _ _ h).2.2.2
  stable c σ n n' h hf := by
    have := (runW_ext π w n n' (push c [] []) (initU σ) h).1 hf
    show ({ ev := _, lk := _, cost := _, out := _ } : LCore.Beh) = { ev := _, lk := _, cost := _, out := _ }
    rw [this]
  diverge c := ⟨0, fun n σ h =>
    runW_diverge π w n (push c [] []) (initU σ) (push_noSeq c [] [] (by simp [NoSeq])) h⟩

/-! ## At window 0 it is `ucmdLangS` -/

theorem specW_zero (r : TRun) : specW [] 0 r = r := by
  cases r; simp [specW]

theorem runW_zero (π : MedPolicy) : ∀ (n : Nat) (k : List UFrame) (s : UState),
    urunW π 0 n k s = urunS π n k s := by
  intro n
  induction n with
  | zero => intro k s; cases k <;> rfl
  | succ m ih =>
    intro k s
    cases k with
    | nil => rfl
    | cons f k =>
      obtain ⟨c, p⟩ := f
      by_cases hd : s.dead = true
      · simp only [urunW, urunS, hd, ↓reduceIte]
      have hk : (fun t => urunW π 0 m k t) = (fun t => urunS π m k t) := funext (ih k)
      cases c with
      | seq a b => simp only [urunW, urunS, hd, Bool.false_eq_true, ↓reduceIte]; exact ih _ s
      | ite e a b =>
        have ht : ∀ cs, transRun 0 cs π s = [] := fun _ => rfl
        have hn : ∀ cs, transSteps 0 cs π s = 0 := fun _ => rfl
        simp only [urunW, urunS, hd, Bool.false_eq_true, ↓reduceIte, ht, hn, specW_zero, ih]
        by_cases hg : evalE e s.store ≠ 0
        · simp [hg]
        · simp [hg]
      | loop e b =>
        simp only [urunW, urunS, hd, Bool.false_eq_true, ↓reduceIte, ih]
      | _ => simp only [urunW, urunS, hd, Bool.false_eq_true, ↓reduceIte, hk]

/-- **Speculation adds an attacker and changes nothing else.** -/
theorem ucmdLangW_zero (P : Partition) (π : MedPolicy) (n : Nat) (c : UCmd) (σ : Store) :
    (ucmdLangW P π 0).run n c σ = (ucmdLangS P π).run n c σ := by
  show ({ ev := _, lk := _, cost := _, out := _ } : LCore.Beh) = { ev := _, lk := _, cost := _, out := _ }
  rw [runW_zero]

/-! ## A transient window cannot tell two related states apart -/

/-- A sequence of commands typed by a chain of `JSecTy` judgments. -/
inductive JList (P : Partition) : List String → List UCmd → Prop where
  | nil  : ∀ V, JList P V []
  | cons : ∀ {V V₁ c cs}, JSecTy P V c V₁ → JList P V₁ cs → JList P V (c :: cs)

theorem jlist_flatten {P : Partition} : ∀ (c : UCmd) {V V₁ : List String} {cs : List UCmd},
    JSecTy P V c V₁ → JList P V₁ cs → JList P V (flatten c ++ cs)
  | .seq a b, _, _, cs, hj, hl => by
    cases hj with
    | seq h₁ h₂ =>
      rw [show flatten (.seq a b) = flatten a ++ flatten b from rfl, List.append_assoc]
      exact jlist_flatten a h₁ (jlist_flatten b h₂ hl)
  | .skip, _, _, _, hj, hl | .assign _ _, _, _, _, hj, hl | .check _, _, _, _, hj, hl
  | .access _, _, _, _, hj, hl | .memop _ _, _, _, _, hj, hl | .sop _ _ _, _, _, _, hj, hl
  | .hop _ _ _, _, _, _, hj, hl | .ite _ _ _, _, _, _, hj, hl | .loop _ _, _, _, _, hj, hl =>
    JList.cons hj hl

/-- `touched_agrees` for the judgment, which `bcheck`'s counted loops inhabit and `jcheck` does not. -/
theorem touched_agreeJ {P : Partition} {V V' : List String} {c : UCmd} {s s' : UState}
    (hj : JSecTy P V c V') (hd : s.dead = s'.dead) (hp : AddrEq V s s') :
    touched c s = touched c s' := by
  by_cases hdd : s.dead = true
  · rw [touched_dead hdd, touched_dead (hd ▸ hdd)]
  have hd0 : s.dead = false := by simpa using hdd
  rw [touched_live hd0, touched_live (hd ▸ hd0)]
  cases hj with
  | deref _ x hm => show [s.store x] = [s'.store x]; rw [hp hd0 x (memStr_mem hm)]
  | free => rfl
  | loadL _ _ q hm _ => show [s.store q] = [s'.store q]; rw [hp hd0 q (memStr_mem hm)]
  | loadH _ _ q hm _ => show [s.store q] = [s'.store q]; rw [hp hd0 q (memStr_mem hm)]
  | storeL _ q _ hm _ _ => show [s.store q] = [s'.store q]; rw [hp hd0 q (memStr_mem hm)]
  | storeH _ q _ hm _ => show [s.store q] = [s'.store q]; rw [hp hd0 q (memStr_mem hm)]
  | _ => rfl

/-- Two finished `uexec` runs of a typed command end related. -/
theorem jrel_uexec {P : Partition} {V V' : List String} {c : UCmd} (hj : JSecTy P V c V')
    {n : Nat} {π : MedPolicy} {s s' : UState} {r r' : UState × Nat × List Bool}
    (hr : JRel P V s s') (f : uexec n c π s = some r) (f' : uexec n c π s' = some r') :
    JRel P V' r.1 r'.1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  have hlow := jsecTy_sound n c V V' hj π s s' h1 h2 h3 h4 h5
  have hadd := jsecTy_addrEq n c V V' hj π s s' h1 h2 h3 h4 h5 h6
  rw [f, f'] at hlow hadd
  exact ⟨hj.toSepCert.safe n π s _ h1 f, hj.toSepCert.safe n π s' _ h2 f',
    hj.toLabInv n π s _ h1 h3 f, hj.toLabInv n π s' _ h2 h4 f', hlow.1, hadd⟩

/-- **A transient window shows the same on related states**: the same addresses, the same commands. -/
theorem transW_agree {P : Partition} {π : MedPolicy} : ∀ (w : Nat) (cs : List UCmd) (V : List String),
    JList P V cs → ∀ (s s' : UState), JRel P V s s' →
      transRun w cs π s = transRun w cs π s' ∧ transSteps w cs π s = transSteps w cs π s' := by
  intro w
  induction w with
  | zero => intro _ _ _ _ _ _; exact ⟨rfl, rfl⟩
  | succ w ih =>
    intro cs V hl s s' hr
    cases hl with
    | nil => exact ⟨rfl, rfl⟩
    | @cons _ V₁ c cs hj hl =>
      have ht := touched_agreeJ hj hr.2.2.2.2.1.2.2.1 hr.2.2.2.2.2
      obtain ⟨h1, h2, h3, h4, h5, _⟩ := id hr
      have hlow := jsecTy_sound 30 c V V₁ hj π s s' h1 h2 h3 h4 h5
      rcases uOptLowEqA_split hlow with ⟨hn, hn'⟩ | ⟨r, r', f, f', _⟩
      · simp only [transRun, transSteps, hn, hn', ht, and_self]
      · obtain ⟨a, b⟩ := ih cs V₁ hl r.1 r'.1 (jrel_uexec hj hr f f')
        simp only [transRun, transSteps, f, f', ht, a, b, and_self]

/-! ## Noninterference at every window -/

theorem specW_same {a a' : TRun} (ts : List Int) (m : Nat) (h : a.Same a') :
    (specW ts m a).Same (specW ts m a') :=
  ⟨h.1, by simp only [specW, h.2.1], by simp only [specW, h.2.2.1], h.2.2.2⟩

theorem runW_same {P : Partition} (π : MedPolicy) (w : Nat) : ∀ (n : Nat) (V : List String)
    (k : List UFrame) (s s' : UState), FTy P V k → JRel P V s s' →
      (urunW π w n k s).Same (urunW π w n k s') := by
  intro n
  induction n with
  | zero =>
    intro V k s s' _ _
    cases k <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | succ m ih =>
    intro V k s s' hk hr
    cases k with
    | nil => exact ⟨rfl, rfl, rfl, rfl⟩
    | cons f k =>
      obtain ⟨c, p⟩ := f
      have hdd : s.dead = s'.dead := hr.2.2.2.2.1.2.2.1
      by_cases hd : s.dead = true
      · have hd' : s'.dead = true := hdd ▸ hd
        simp only [urunW, hd, hd', ↓reduceIte]; exact ⟨rfl, rfl, rfl, rfl⟩
      have hd0 : s.dead = false := by simpa using hd
      have hd' : s'.dead = false := hdd ▸ hd0
      obtain _ | ⟨hj, hw, hk'⟩ := hk
      have hj0 := hj
      cases hj with
      | seq h₁ h₂ =>
        simp only [urunW, hd0, hd', Bool.false_eq_true, ↓reduceIte]
        exact ih _ _ s s' (push_fty h₁ (fun x h => h) (push_fty h₂ hw hk')) hr
      | @iteL _ V₁ V₂ a b e he h₁ h₂ =>
        have hg : evalE e s.store = evalE e s'.store := evalE_lowEq e he hr.2.2.2.2.1.1
        obtain ⟨ta, na⟩ := transW_agree (π := π) w (flatten a) V
          (by simpa using jlist_flatten a (cs := []) h₁ (JList.nil _)) s s' hr
        obtain ⟨tb, nb⟩ := transW_agree (π := π) w (flatten b) V
          (by simpa using jlist_flatten b (cs := []) h₂ (JList.nil _)) s s' hr
        simp only [urunW, hd0, hd', Bool.false_eq_true, ↓reduceIte, hg, ta, na, tb, nb]
        split
        · apply TRun.tickS_same; apply specW_same
          exact ih _ _ s s' (push_fty h₁ (fun x hx => interStr_left (hw x hx)) hk') hr
        · apply TRun.tickS_same; apply specW_same
          exact ih _ _ s s' (push_fty h₂ (fun x hx => interStr_right (hw x hx)) hk') hr
      | whileW e he hWV hc hWW =>
        have hg : evalE e s.store = evalE e s'.store := evalE_lowEq e he hr.2.2.2.2.1.1
        simp only [urunW, hd0, hd', Bool.false_eq_true, ↓reduceIte, hg]
        have hrW := JRel.mono hWV hr
        split
        · apply TRun.tickS_same
          exact ih _ _ s s' (push_fty hc (fun x h => h)
            (FTy.cons (JSecTy.whileW e he hWW hc hWW) hw hk')) hrW
        · apply TRun.tickS_same
          exact ih _ _ s s' hk' (JRel.mono hw hrW)
      | _ =>
        simp only [urunW, hd0, hd', Bool.false_eq_true, ↓reduceIte]
        exact TRun.atomS_same p (stepT_same hj0 hr hd0)
          (fun hdone => ih _ _ _ _ hk' (JRel.mono hw (jrel_step hj0 rfl hr hd0 hd' hdone
            ((stepT_same hj0 hr hd0).2.2.2 ▸ hdone))))

/-- **Row 9 on L.** What `bcheck` accepts shows the same on low-equivalent inputs at every window and
    every fuel, including the addresses a mispredicted branch touches and the commands it ran. -/
theorem bcheck_relW {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) (w : Nat) :
    LCore.Cert.rel (ucmdLangW P π w) c := by
  intro n σ σ' _ _ hσ
  have hf := bcheck_sound c [] [] A' V' k h
  have hr : JRel P [] (initU σ) (initU σ') :=
    ⟨SepInv.initU, SepInv.initU, LabInv.initU, LabInv.initU,
     ⟨hσ, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
     fun _ x hx => by simp at hx⟩
  obtain ⟨he, hl, hc, ho⟩ := runW_same π w n [] (push c [] []) _ _
    (push_fty hf.joint (W := []) (fun x hx => by simp at hx) (FTy.nil _)) hr
  show ({ ev := _, lk := _, cost := _, out := _ } : LCore.Beh) = { ev := _, lk := _, cost := _, out := _ }
  rw [he, hl, hc, ho]

/-! ## Witnesses -/

/-- **Accepted, and the window is not empty.** `brWitness` is `bcheck`-clean, and at window 1 its run
    shows an address it does not show at window 0. -/
theorem brWitness_bcheck : (bcheck Psec [] [] brWitness).isSome = true := by decide

theorem brWitness_relW (π : MedPolicy) (w : Nat) : LCore.Cert.rel (ucmdLangW Psec π w) brWitness := by
  cases h : bcheck Psec [] [] brWitness with
  | none => have := brWitness_bcheck; rw [h] at this; cases this
  | some r => exact bcheck_relW (A' := r.1) (V' := r.2.1) (k := r.2.2) h π w

theorem brWitness_window_matters :
    (ucmdLangW Psec (fun _ => true) 0).run 20 brWitness σlo
      ≠ (ucmdLangW Psec (fun _ => true) 1).run 20 brWitness σlo := by
  decide

/-- The secret `s`, and the variables allowed to hold it. -/
def secS : Partition := fun x => x == "s" || x == "p" || x == "x" || x == "y"

/-- A store holding `v` in the secret. -/
def storeS (v : Int) : Store := fun x => if x == "s" then v else 0

theorem storeS_low (v v' : Int) : lowEq secS (storeS v) (storeS v') := by
  intro x hx
  have h : (x == "s") = false := by
    simp only [secS, Bool.or_eq_false_iff] at hx; exact hx.1.1.1
  simp [storeS, h]

/-- **The secret as an address, in a branch that never runs.** -/
def transientUse : UCmd := .ite (.num 0) (.memop .deref "s") .skip

/-- **Refused**, although the command is never executed. -/
theorem transientUse_refused : bcheck secS [] [] transientUse = none := by decide

/-- Architecturally it reveals nothing, so a machine without speculation would call this safe. -/
theorem transientUse_silent_at_zero :
    (ucmdLangW secS (fun _ => true) 0).run 20 transientUse (storeS 1)
      = (ucmdLangW secS (fun _ => true) 0).run 20 transientUse (storeS 2) := by
  decide

/-- **At window 1 it leaks the secret.** -/
theorem transientUse_leaks :
    ¬ LCore.Cert.rel (ucmdLangW secS (fun _ => true) 1) transientUse := by
  intro h
  have := h 20 _ _ trivial trivial (storeS_low 1 2)
  revert this; decide

/-- The secret stored behind a secret-named pointer, then a branch that never runs. -/
def gadgetWith (body : UCmd) : UCmd :=
  .seq (.memop .allocS "p") (.seq (.hop .store "p" "s") (.ite (.num 0) body .skip))

/-- **The bounds-check-bypass gadget**, built from L's own inputs: a loaded value becomes an address
    in a branch that never runs. -/
def gadget : UCmd := gadgetWith (.seq (.hop .load "x" "p") (.hop .load "y" "x"))

theorem gadget_refused : bcheck secS [] [] gadget = none := by decide

/-- **What the refusal is about**: the same program without the second load is accepted, so the only
    refused step is the loaded value used as an address. -/
theorem gadget_first_load_checks :
    (bcheck secS [] [] (gadgetWith (.hop .load "x" "p"))).isSome = true := by decide

/-- **The leak needs a window of two**: one to load the secret, one to use it as an address. -/
theorem gadget_silent_at_one :
    (ucmdLangW secS (fun _ => true) 1).run 20 gadget (storeS 1)
      = (ucmdLangW secS (fun _ => true) 1).run 20 gadget (storeS 2) := by
  decide

theorem gadget_leaks : ¬ LCore.Cert.rel (ucmdLangW secS (fun _ => true) 2) gadget := by
  intro h
  have := h 20 _ _ trivial trivial (storeS_low 1 2)
  revert this; decide

end ConfTyping.Spec
