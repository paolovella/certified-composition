/-
  Tenant isolation on L (F5, row 7b), a `Cert.relView` on `ucmdLangI`.

  **Attacker:** tenant B. It reads its own channels and measures every side channel `Beh` records:
  leakage, cost and outcome. It sees neither tenant A's channels nor A's data.

  **Why it splits in two.** `urunS` branches only on `evalE`, which reads the integer store, and
  addresses come from there too, so a string cannot change timing, addresses, cost or outcome
  (`runS_blind`). A's integers are `bcheck`'s noninterference with the strings fixed
  (`bcheck_relI`). A's strings can leak only through a payload on a channel B reads, which is all
  `tenantCheck` looks at.

  **Limits.** A program must pass `bcheck`, so its loops are bounded and A's code is constant-time
  in A's integers. `tenantCheck` is flow-insensitive, so a variable reused across tenants is
  refused. `splitPass` is over `ucmdLangS`, so this certificate is not yet carried through a pass
  on `ucmdLangI`. It speaks about the leakage `Beh` records, not hardware L does not model.
-/
import ConfTyping.InjectionL
import ConfTyping.SplitView

namespace ConfTyping

/-! ## The checker -/

/-- **A's strings reach only A's variables and channels `f` does not read.** `A` names tenant A's
    string variables. `san` removes quotes, not secrets, so `sexprLow` looks through it. -/
def tenantCheck (A : Partition) (f : LCore.Observer) : UCmd → Bool
  | .seq a b => tenantCheck A f a && tenantCheck A f b
  | .ite _ a b => tenantCheck A f a && tenantCheck A f b
  | .loop _ b => tenantCheck A f b
  | .sop .set x e => A x || sexprLow A e
  | .sop .emit q e => !f (.emit q) || sexprLow A e
  | _ => true

namespace Tenant

open Split (obsV tickS_obs atomS_obs)

/-- Two inputs that differ at most in tenant A's data: its integers, by `P`, and its strings, by `A`. -/
def sameExceptA (P A : Partition) (i i' : Store × (String → UStr)) : Prop :=
  lowEq P i.1 i'.1 ∧ ∀ x, A x = false → i.2 x = i'.2 x

/-! ## A's integers: `bcheck`'s noninterference, with the strings fixed -/

theorem SepInv.initI {σ : Store} {τ : String → UStr} : SepInv [] (initI σ τ) :=
  ⟨rfl, fun _ =>
    ⟨by intro x hx; simp at hx, by intro x hx; simp at hx,
     by intro a ha; have h0 : memInt a ([] : List Int) = true := ha; simp [memInt] at h0,
     by intro a ha; have h0 : memInt a ([] : List Int) = true := ha; simp [memInt] at h0,
     by intro a ha; have h0 : memInt a ([] : List Int) = true := ha; simp [memInt] at h0⟩⟩

/-- **`bcheck`'s noninterference on `ucmdLangI`.** -/
theorem bcheck_relI {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.rel (ucmdLangI P π) c := by
  intro n i i' _ _ hi
  obtain ⟨hσ, hτ⟩ := hi
  have hf := bcheck_sound c [] [] A' V' k h
  have hr : JRel P [] (initI i.1 i.2) (initI i'.1 i'.2) :=
    ⟨SepInv.initI, SepInv.initI, fun _ x hx => by simp at hx, fun _ x hx => by simp at hx,
     ⟨hσ, rfl, rfl, rfl, fun x _ => congrFun hτ x, rfl, rfl, rfl, fun _ _ => rfl⟩,
     fun _ x hx => by simp at hx⟩
  obtain ⟨he, hl, hc, ho⟩ := runS_same π n [] (push c [] []) _ _
    (push_fty hf.joint (W := []) (fun x hx => by simp at hx) (FTy.nil _)) hr
  show ({ ev := _, lk := _, cost := _, out := _ } : LCore.Beh) = { ev := _, lk := _, cost := _, out := _ }
  rw [he, hl, hc, ho]

/-! ## A's strings: a run is blind to them -/

theorem evalS_agree {A : Partition} {τ τ' : String → UStr} (h : ∀ x, A x = false → τ x = τ' x) :
    ∀ e, sexprLow A e = true → evalS τ e = evalS τ' e
  | .lit _, _ => rfl
  | .var x, he => h x (by simpa [sexprLow] using he)
  | .cat a b, he => by
    simp only [sexprLow, Bool.and_eq_true] at he
    simp only [evalS, evalS_agree h a he.1, evalS_agree h b he.2]
  | .san a, he => by
    simp only [sexprLow] at he
    simp only [evalS, evalS_agree h a he]

/-- Two states the same except for the sink and A's strings. -/
def SRel (A : Partition) (s s' : UState) : Prop :=
  s.store = s'.store ∧ s.auth = s'.auth ∧ s.reads = s'.reads ∧ s.dead = s'.dead ∧
  s.heap = s'.heap ∧ s.live = s'.live ∧ s.fresh = s'.fresh ∧ s.err = s'.err ∧
  s.freed = s'.freed ∧ s.hlab = s'.hlab ∧ ∀ x, A x = false → s.sstore x = s'.sstore x

set_option hygiene false in
local macro "blind_tac" : tactic =>
  `(tactic| (simp only [stepT, uexec, uaddrs, stepEv, Bool.false_eq_true, ↓reduceIte] <;>
     (repeat' split) <;> simp_all [obsV, SRel]))

/-- **One live atomic step is blind to A's strings**, for what `f` can see. -/
theorem step_blind {A : Partition} {f : LCore.Observer} {c : UCmd} {π : MedPolicy} {s s' : UState}
    (hc : atomic c = true) (ht : tenantCheck A f c = true) (hr : SRel A s s') (hd : s.dead = false) :
    obsV f (stepT c π s) = obsV f (stepT c π s') ∧ SRel A (stepT c π s).st (stepT c π s').st := by
  obtain ⟨st, au, re, de, he, li, fr, er, fd, hl, ss, si⟩ := s
  obtain ⟨st', au', re', de', he', li', fr', er', fd', hl', ss', si'⟩ := s'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hs⟩ := hr
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hs hd
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hd
  cases c with
  | sop op x e =>
    cases op with
    | set =>
      simp only [tenantCheck, Bool.or_eq_true] at ht
      refine ⟨by simp [stepT, uexec, uaddrs, stepEv, obsV], ?_⟩
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      intro y hy
      simp only [stepT, uexec, uaddrs, Bool.false_eq_true, ↓reduceIte, updSU]
      by_cases hyx : y = x
      · subst hyx
        have hlow : sexprLow A e = true := by
          rcases ht with h | h
          · rw [hy] at h; cases h
          · exact h
        simp [evalS_agree hs e hlow]
      · simp [hyx, hs y hy]
    | emit =>
      simp only [tenantCheck, Bool.or_eq_true, Bool.not_eq_true'] at ht
      constructor
      · simp only [stepT, uexec, uaddrs, stepEv, Bool.false_eq_true, ↓reduceIte, obsV]
        rcases ht with h | h
        · simp [LCore.Ev.chan, h]
        · simp [evalS_agree hs e h]
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs⟩
  | seq | ite | loop => simp [atomic] at hc
  | memop op x => cases op <;> blind_tac
  | hop op x y => cases op <;> blind_tac
  | _ => blind_tac

/-- Every frame on the stack passes the check. -/
def FramesOk (A : Partition) (f : LCore.Observer) (k : List UFrame) : Prop :=
  ∀ x ∈ k, tenantCheck A f x.1 = true

theorem push_ok {A : Partition} {f : LCore.Observer} : ∀ (c : UCmd) (p : List Nat) (k : List UFrame),
    tenantCheck A f c = true → FramesOk A f k → FramesOk A f (push c p k)
  | .seq a b, p, k, hc, hk => by
    simp only [tenantCheck, Bool.and_eq_true] at hc
    exact push_ok a _ _ hc.1 (push_ok b _ k hc.2 hk)
  | .skip, _, _, hc, hk | .assign _ _, _, _, hc, hk | .check _, _, _, hc, hk
  | .access _, _, _, hc, hk | .memop _ _, _, _, hc, hk | .hop _ _ _, _, _, hc, hk
  | .sop _ _ _, _, _, hc, hk | .ite _ _ _, _, _, hc, hk | .loop _ _, _, _, hc, hk => by
    intro x hx
    simp only [push, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact hk x hx

/-- **A run is blind to A's strings**, for what `f` can see: the same events on `f`'s channels,
    and the same leakage, cost and outcome. -/
theorem runS_blind {A : Partition} {f : LCore.Observer} (π : MedPolicy) :
    ∀ (n : Nat) (k : List UFrame) (s s' : UState), FramesOk A f k → NoSeq k → SRel A s s' →
      obsV f (urunS π n k s) = obsV f (urunS π n k s') := by
  intro n
  induction n with
  | zero => intro k s s' _ _ _; cases k <;> rfl
  | succ m ih =>
    intro k s s' hok hns hr
    cases k with
    | nil => rfl
    | cons fr k' =>
      obtain ⟨c, p⟩ := fr
      have hc : tenantCheck A f c = true := hok _ List.mem_cons_self
      have hok' : FramesOk A f k' := fun x hx => hok x (List.mem_cons_of_mem _ hx)
      have hns' : NoSeq k' := fun x hx => hns x (List.mem_cons_of_mem _ hx)
      have hst : s.store = s'.store := hr.1
      have hdd : s.dead = s'.dead := hr.2.2.2.1
      by_cases hd : s.dead = true
      · have hd' : s'.dead = true := hdd ▸ hd
        simp [urunS, hd, hd', obsV]
      have hd0 : s.dead = false := by simpa using hd
      have hd0' : s'.dead = false := hdd ▸ hd0
      cases c with
      | seq a b => exact absurd rfl (hns _ List.mem_cons_self a b)
      | ite e a b =>
        simp only [tenantCheck, Bool.and_eq_true] at hc
        simp only [urunS, hd0, hd0', Bool.false_eq_true, ↓reduceIte, ← hst]
        by_cases hg : evalE e s.store ≠ 0
        · simp only [ite_eq_left hg]
          exact tickS_obs (ih _ _ _ (push_ok a _ _ hc.1 hok') (push_noSeq _ _ _ hns') hr)
        · simp only [ite_eq_right hg]
          exact tickS_obs (ih _ _ _ (push_ok b _ _ hc.2 hok') (push_noSeq _ _ _ hns') hr)
      | loop e b =>
        have hb : tenantCheck A f b = true := hc
        have hns2 : NoSeq ((UCmd.loop e b, p) :: k') := by
          intro x hx a' b'; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp
          · exact hns' x hx a' b'
        simp only [urunS, hd0, hd0', Bool.false_eq_true, ↓reduceIte, ← hst]
        by_cases hg : evalE e s.store ≠ 0
        · simp only [ite_eq_left hg]
          exact tickS_obs (ih _ _ _ (push_ok b _ _ hb hok) (push_noSeq _ _ _ hns2) hr)
        · simp only [ite_eq_right hg]
          exact tickS_obs (ih _ _ _ hok' hns' hr)
      | _ =>
        rw [runS_atomic rfl p m π k' hd0, runS_atomic rfl p m π k' hd0']
        obtain ⟨h1, h2⟩ := step_blind (π := π) rfl hc hr hd0
        exact atomS_obs h1 (fun _ => ih _ _ _ hok' hns' h2)

/-! ## The certificate -/

/-- **Row 7b on L.** If `bcheck` accepts a program and `tenantCheck` passes it for observer `f`, then
    `f` sees the same at every fuel on inputs that differ only in A's data: the same events on its
    channels, and the same leakage, cost and outcome. A's own channels may still depend on A's data. -/
theorem tenantCheck_relView {P A : Partition} {f : LCore.Observer} {c : UCmd} {A' V' : List String}
    {k : Nat} (hb : bcheck P [] [] c = some (A', V', k)) (ht : tenantCheck A f c = true)
    (π : MedPolicy) : LCore.Cert.relView (ucmdLangI P π) (sameExceptA P A) f c := by
  intro n i i' _ _ hi
  obtain ⟨hσ, hτ⟩ := hi
  -- First the integers, with A's strings fixed.
  have h₁ := congrArg (LCore.Beh.view f)
    (bcheck_relI hb π n (i.1, i.2) (i'.1, i.2) trivial trivial ⟨hσ, rfl⟩)
  -- Then the strings, on the other run's integers.
  have hr : SRel A (initI i'.1 i.2) (initI i'.1 i'.2) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hτ⟩
  have h₂ := runS_blind (A := A) (f := f) π n (push c [] []) _ _
    (push_ok c [] [] ht (fun x hx => by simp at hx)) (push_noSeq c [] [] (by simp [NoSeq])) hr
  simp only [obsV, Prod.mk.injEq] at h₂
  refine h₁.trans ?_
  simp only [ucmdLangI, LCore.Beh.view, LCore.Beh.mk.injEq]
  exact h₂

/-! ## Witnesses -/

/-- Tenant A's integer variable. -/
def intsA : Partition := fun x => x == "ax"
/-- Tenant A's string variables. -/
def strsA : Partition := fun x => x == "ain" || x == "at"
/-- Tenant B's string variables. -/
def strsB : Partition := fun x => x == "bin"
/-- B's observer: its own channel. -/
def seesB : LCore.Observer
  | .emit "b" => true
  | _ => false
/-- A's observer: its own channel. -/
def seesA : LCore.Observer
  | .emit "a" => true
  | _ => false

/-- Each tenant's data on its own channel. -/
def twoTenants : UCmd :=
  .seq (.sop .set "at" (.cat (.lit [.ord]) (.var "ain")))
    (.seq (.sop .emit "a" (.var "at"))
      (.seq .skip (.sop .emit "b" (.var "bin"))))

theorem twoTenants_checks_B : tenantCheck strsA seesB twoTenants = true := by decide
theorem twoTenants_checks_A : tenantCheck strsB seesA twoTenants = true := by decide
theorem twoTenants_bcheck : (bcheck intsA [] [] twoTenants).isSome = true := by decide

/-- A `bcheck` result, for the certificates below. -/
theorem twoTenants_bcheck' : ∃ A' V' k, bcheck intsA [] [] twoTenants = some (A', V', k) := by
  cases h : bcheck intsA [] [] twoTenants with
  | none => have := twoTenants_bcheck; rw [h] at this; cases this
  | some r => exact ⟨r.1, r.2.1, r.2.2, rfl⟩

/-- **Accepted, B's direction**: B sees nothing of A, side channels included. -/
theorem twoTenants_isolates_B (π : MedPolicy) :
    LCore.Cert.relView (ucmdLangI intsA π) (sameExceptA intsA strsA) seesB twoTenants := by
  obtain ⟨_, _, _, h⟩ := twoTenants_bcheck'
  exact tenantCheck_relView h twoTenants_checks_B π

/-- **Accepted, A's direction**: A sees nothing of B. -/
theorem twoTenants_isolates_A (π : MedPolicy) :
    LCore.Cert.relView (ucmdLangI intsA π) (sameExceptA intsA strsB) seesA twoTenants := by
  obtain ⟨_, _, _, h⟩ := twoTenants_bcheck'
  exact tenantCheck_relView h twoTenants_checks_A π

/-- Two runs' inputs: A's string varies, everything else is the same. -/
def inA₁ : Store × (String → UStr) := (fun _ => 0, fun y => if y == "ain" then [.ord] else [])
def inA₂ : Store × (String → UStr) := (fun _ => 0, fun y => if y == "ain" then [.ord, .ord] else [])

theorem inA_related : sameExceptA intsA strsA inA₁ inA₂ := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro x hx
  have hne : (x == "ain") = false := by
    simp only [strsA, Bool.or_eq_false_iff] at hx; exact hx.1
  show (if (x == "ain") = true then _ else _) = (if (x == "ain") = true then _ else _)
  rw [hne]; rfl

/-- **The all-channels observer fails on the same program**: A's own output depends on A's data, so
    this certificate says what `rel` cannot. -/
theorem twoTenants_all_fails :
    ¬ LCore.Cert.relView (ucmdLangI intsA (fun _ => true)) (sameExceptA intsA strsA)
        LCore.Observer.all twoTenants := by
  intro h
  have := h 20 inA₁ inA₂ trivial trivial inA_related
  revert this; decide

/-- A's data on B's channel. -/
def crossed : UCmd := .sop .emit "b" (.var "ain")
theorem crossed_refused : tenantCheck strsA seesB crossed = false := by decide
theorem crossed_leaks :
    ¬ LCore.Cert.relView (ucmdLangI intsA (fun _ => true)) (sameExceptA intsA strsA) seesB crossed := by
  intro h
  have := h 20 inA₁ inA₂ trivial trivial inA_related
  revert this; decide

/-- The same through an assignment: the rule for `set` is load-bearing. -/
def laundered : UCmd := .seq (.sop .set "bt" (.var "ain")) (.sop .emit "b" (.var "bt"))
theorem laundered_refused : tenantCheck strsA seesB laundered = false := by decide
theorem laundered_leaks :
    ¬ LCore.Cert.relView (ucmdLangI intsA (fun _ => true)) (sameExceptA intsA strsA) seesB laundered := by
  intro h
  have := h 20 inA₁ inA₂ trivial trivial inA_related
  revert this; decide

/-- The same through `san`: sanitising removes quotes, not secrets. -/
def sanitised : UCmd := .sop .emit "b" (.san (.var "ain"))
theorem sanitised_refused : tenantCheck strsA seesB sanitised = false := by decide
theorem sanitised_leaks :
    ¬ LCore.Cert.relView (ucmdLangI intsA (fun _ => true)) (sameExceptA intsA strsA) seesB sanitised := by
  intro h
  have := h 20 inA₁ inA₂ trivial trivial inA_related
  revert this; decide

/-- A branch on A's integer: B's channel is untouched, but the leakage and cost differ. -/
def timing : UCmd := .ite (.var "ax") .skip (.seq .skip .skip)

/-- **Both checks are load-bearing.** `tenantCheck` passes this, because no string is involved, and
    `bcheck` refuses it. -/
theorem timing_checks : tenantCheck strsA seesB timing = true := by decide
theorem timing_refused : bcheck intsA [] [] timing = none := by decide

theorem timing_leaks :
    ¬ LCore.Cert.relView (ucmdLangI intsA (fun _ => true)) (sameExceptA intsA strsA) seesB timing := by
  intro h
  have hrel : sameExceptA intsA strsA (fun _ => 0, fun _ => []) (fun x => if x == "ax" then 1 else 0, fun _ => []) := by
    refine ⟨?_, fun _ _ => rfl⟩
    intro x hx
    have hne : (x == "ax") = false := hx
    show (0 : Int) = (if (x == "ax") = true then 1 else 0)
    rw [hne]; rfl
  have := h 20 _ _ trivial trivial hrel
  revert this; decide

end Tenant

end ConfTyping
