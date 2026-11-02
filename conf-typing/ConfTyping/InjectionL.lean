/-
  Injection on L (F5, row 3): the first row that needed L to take untrusted strings.

  `ucmdLangS` takes an integer `Store`, and `initU` starts the string store empty. So on it the
  vulnerable query of `TaintCert.lean` is safe, because no attacker can reach it
  (`vulnQuery_empty_shows_two`). `ucmdLangI` is the same language and the same run, with the
  initial strings as part of the input; on empty strings the two are equal (`ucmdLangI_empty`).

  **Attacker:** controls every initial string variable. **Observer:** the sink. Side channels play
  no part: this row is the integrity of a query's shape, not secrecy.

  **Shape:** `Cert.trace`. `TaintCert` says every emitted string's delimiter count is one the
  analysis predicted, which is a property of one run.

  **Limits.** "Injection" here means the delimiter count over `UCh`'s two symbols, and `san` only
  removes quotes (EXPR-04). `tcheck` has no loop rule, so `tcheck_traceI` covers loop-free programs.
  `tcheckW` has one but is not on L: `TaintCert` says nothing about a run that never finishes.
-/
import ConfTyping.Split
import ConfTyping.TaintCert

namespace ConfTyping

/-! ## The language -/

/-- The initial state with the attacker's strings. -/
def initI (σ : Store) (τ : String → UStr) : UState := { initU σ with sstore := τ }

/-- **`ucmdLangS` with string inputs.** -/
def ucmdLangI (P : Partition) (π : MedPolicy) : LCore.Lang where
  Prog  := UCmd
  In    := Store × (String → UStr)
  lowIn i i' := lowEq P i.1 i'.1 ∧ i.2 = i'.2
  run n c i :=
    let r := urunS π n (push c [] []) (initI i.1 i.2)
    { ev := r.ev, lk := r.lk, cost := r.cost, out := r.out }

theorem ucmdLangI_lawful (P : Partition) (π : MedPolicy) : (ucmdLangI P π).Lawful where
  ev_mono c i n n' h := (runS_ext π n n' _ _ h).2.1
  lk_mono c i n n' h := (runS_ext π n n' _ _ h).2.2.1
  cost_mono c i n n' h := (runS_ext π n n' _ _ h).2.2.2
  stable c i n n' h hf := by
    have := (runS_ext π n n' (push c [] []) (initI i.1 i.2) h).1 hf
    show ({ ev := _, lk := _, cost := _, out := _ } : LCore.Beh) = { ev := _, lk := _, cost := _, out := _ }
    rw [this]
  diverge c := ⟨0, fun n i h =>
    runS_diverge π n (push c [] []) (initI i.1 i.2) (push_noSeq c [] [] (by simp [NoSeq])) h⟩

/-- **On empty strings it is `ucmdLangS`**: the new input adds an attacker and changes nothing else. -/
theorem ucmdLangI_empty (P : Partition) (π : MedPolicy) (n : Nat) (c : UCmd) (σ : Store) :
    (ucmdLangI P π).run n c (σ, fun _ => []) = (ucmdLangS P π).run n c σ := rfl

/-! ## The property -/

/-- The delimiters in an emitted payload. `uchCode` writes the delimiter as 1. -/
def dcount : List Nat → Nat
  | [] => 0
  | 1 :: r => 1 + dcount r
  | _ :: r => dcount r

theorem dcount_code : ∀ t : UStr, dcount (t.map uchCode) = qcount t
  | [] => rfl
  | .quote :: r => by simp only [List.map, uchCode, dcount, qcount, dcount_code r]
  | .ord :: r => by simp only [List.map, uchCode, dcount, qcount, dcount_code r]

/-- **Every emitted payload carries a delimiter count in `Ks`.** -/
def injectionFree (Ks : List Nat) (evs : List LCore.Ev) : Prop :=
  ∀ q d, LCore.Ev.emit q d ∈ evs → dcount d ∈ Ks

theorem injectionFree_prefixClosed (Ks : List Nat) : LCore.PrefixClosed (injectionFree Ks) :=
  fun _ _ hab hb q d hm => hb q d (hab.subset hm)

/-! ## From `tcheck` to the events of a run -/

/-- Only `sop .emit` emits, and it emits what the string store evaluates to. -/
theorem stepT_emit {c : UCmd} {π : MedPolicy} {s : UState} {q : String} {d : List Nat}
    (h : LCore.Ev.emit q d ∈ (stepT c π s).ev) :
    ∃ e, c = .sop .emit q e ∧ d = (evalS s.sstore e).map uchCode := by
  unfold stepT at h
  split at h
  · cases c with
    | sop op x e =>
      cases op
      · simp [stepEv, faultEv] at h
      · simp [stepEv, faultEv] at h
        exact ⟨e, by rw [h.1], h.2⟩
    | _ => simp [stepEv, faultEv] at h
  · simp at h

theorem atomic_emit {c : UCmd} (hc : atomic c = true) {n : Nat} {π : MedPolicy} {s : UState}
    {q : String} {d : List Nat} (h : LCore.Ev.emit q d ∈ (uexecT n c π s).ev) :
    s.dead = false ∧ ∃ e, c = .sop .emit q e ∧ d = (evalS s.sstore e).map uchCode := by
  rcases n with _ | n
  · simp [uexecT] at h
  by_cases hd : s.dead = true
  · simp [uexecT, hd] at h
  cases c with
  | seq | ite | loop => simp [atomic] at hc
  | _ =>
    simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte] at h
    exact ⟨by simpa using hd, stepT_emit h⟩

/-- **A checked program's run emits only predicted counts, at every fuel.** -/
theorem evs_tcheck : ∀ (c : UCmd) (C C' : TaintEnv) (Ks : List Nat), tcheck C c = some (C', Ks) →
    ∀ (n : Nat) (π : MedPolicy) (s : UState), TaintInv C s →
      injectionFree Ks (uexecT n c π s).ev
  | .seq a b, C, C', Ks, h, n, π, s, hs => by
    cases h1 : tcheck C a with
    | none => simp [tcheck, h1] at h
    | some p1 =>
      cases h2 : tcheck p1.1 b with
      | none => simp [tcheck, h1, h2] at h
      | some p2 =>
        simp only [tcheck, h1, h2, Option.bind_some, Option.map_some, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        intro q d hm
        rcases n with _ | n
        · simp [uexecT] at hm
        by_cases hd : s.dead = true
        · simp [uexecT, hd] at hm
        simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.seqT] at hm
        by_cases ha : (uexecT n a π s).out = .done
        · simp only [ha, ↓reduceIte, List.mem_append] at hm
          rcases hm with hm | hm
          · exact List.mem_append_left _ (evs_tcheck a C p1.1 p1.2 h1 n π s hs q d hm)
          · have henv := (tcheck_sound a C p1.1 p1.2 h1).env n π s _ hs
              (uexecT_done_agree n a π s ha).1
            exact List.mem_append_right _ (evs_tcheck b p1.1 p2.1 p2.2 h2 n π _ henv q d hm)
        · simp only [ha, ↓reduceIte] at hm
          exact List.mem_append_left _ (evs_tcheck a C p1.1 p1.2 h1 n π s hs q d hm)
  | .ite e a b, C, C', Ks, h, n, π, s, hs => by
    cases h1 : tcheck C a with
    | none => simp [tcheck, h1] at h
    | some p1 =>
      cases h2 : tcheck C b with
      | none => simp [tcheck, h1, h2] at h
      | some p2 =>
        simp only [tcheck, h1, h2, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        intro q d hm
        rcases n with _ | n
        · simp [uexecT] at hm
        by_cases hd : s.dead = true
        · simp [uexecT, hd] at hm
        simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.tick] at hm
        by_cases hg : evalE e s.store ≠ 0
        · simp only [hg, ↓reduceIte, ne_eq, not_false_eq_true] at hm
          exact List.mem_append_left _ (evs_tcheck a C p1.1 p1.2 h1 n π s hs q d hm)
        · simp only [hg, ↓reduceIte] at hm
          exact List.mem_append_right _ (evs_tcheck b C p2.1 p2.2 h2 n π s hs q d hm)
  | .loop _ _, _, _, _, h, _, _, _, _ => by simp [tcheck] at h
  | .sop .emit x e, C, C', Ks, h, n, π, s, hs => by
    cases hk : scount C e with
    | none => simp [tcheck, hk] at h
    | some k =>
      simp only [tcheck, hk, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      intro q d hm
      obtain ⟨hd, e', he, rfl⟩ := atomic_emit rfl hm
      cases he
      rw [dcount_code, scount_sound (hs hd) e k hk]
      exact List.mem_singleton.mpr rfl
  | .sop .set _ _, _, _, _, _, _, _, _, _ => fun _ _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .skip, _, _, _, _, _, _, _, _ => fun _ _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .assign _ _, _, _, _, _, _, _, _, _ => fun _ _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .check _, _, _, _, _, _, _, _, _ => fun _ _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .access _, _, _, _, _, _, _, _, _ => fun _ _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .memop _ _, _, _, _, _, _, _, _, _ => fun _ _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .hop _ _ _, _, _, _, _, _, _, _, _ => fun _ _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he

/-- `tcheck` accepts only loop-free programs, and those finish from every state. -/
theorem tcheck_finishes : ∀ (c : UCmd) (C C' : TaintEnv) (Ks : List Nat),
    tcheck C c = some (C', Ks) → ∀ (π : MedPolicy) (s : UState), ∃ f, (uexecT f c π s).out ≠ .fuel
  | .seq a b, C, C', Ks, h, π, s => by
    cases h1 : tcheck C a with
    | none => simp [tcheck, h1] at h
    | some p1 =>
      cases h2 : tcheck p1.1 b with
      | none => simp [tcheck, h1, h2] at h
      | some p2 =>
        by_cases hd : s.dead = true
        · exact ⟨1, by simp [uexecT, hd]⟩
        obtain ⟨fa, hfa⟩ := tcheck_finishes a C p1.1 p1.2 h1 π s
        by_cases ha : (uexecT fa a π s).out = .done
        · obtain ⟨fb, hfb⟩ := tcheck_finishes b p1.1 p2.1 p2.2 h2 π (uexecT fa a π s).st
          refine ⟨max fa fb + 1, ?_⟩
          have ea := (uexecT_ext fa (max fa fb) a π s (Nat.le_max_left _ _)).1 hfa
          have eb := (uexecT_ext fb (max fa fb) b π _ (Nat.le_max_right _ _)).1 hfb
          simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.seqT, ← ea, ha, ← eb]
          exact hfb
        · refine ⟨fa + 1, ?_⟩
          simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.seqT, ha]
          exact hfa
  | .ite e a b, C, C', Ks, h, π, s => by
    cases h1 : tcheck C a with
    | none => simp [tcheck, h1] at h
    | some p1 =>
      cases h2 : tcheck C b with
      | none => simp [tcheck, h1, h2] at h
      | some p2 =>
        by_cases hd : s.dead = true
        · exact ⟨1, by simp [uexecT, hd]⟩
        by_cases hg : evalE e s.store ≠ 0
        · obtain ⟨f, hf⟩ := tcheck_finishes a C p1.1 p1.2 h1 π s
          refine ⟨f + 1, ?_⟩
          simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.tick, hg, ne_eq,
            not_false_eq_true]
          exact hf
        · obtain ⟨f, hf⟩ := tcheck_finishes b C p2.1 p2.2 h2 π s
          refine ⟨f + 1, ?_⟩
          simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.tick, hg]
          exact hf
  | .loop _ _, _, _, _, h, _, _ => by simp [tcheck] at h
  | .sop op x e, _, _, _, _, π, s => atomic_finishes rfl π s
  | .skip, _, _, _, _, π, s => atomic_finishes rfl π s
  | .assign _ _, _, _, _, _, π, s => atomic_finishes rfl π s
  | .check _, _, _, _, _, π, s => atomic_finishes rfl π s
  | .access _, _, _, _, _, π, s => atomic_finishes rfl π s
  | .memop _ _, _, _, _, _, π, s => atomic_finishes rfl π s
  | .hop _ _ _, _, _, _, _, π, s => atomic_finishes rfl π s
where
  atomic_finishes {c : UCmd} (hc : atomic c = true) (π : MedPolicy) (s : UState) :
      ∃ f, (uexecT f c π s).out ≠ .fuel := by
    refine ⟨1, ?_⟩
    by_cases hd : s.dead = true
    · simp [uexecT, hd]
    have : (uexecT 1 c π s).out = (stepT c π s).out := by
      cases c with
      | seq | ite | loop => simp [atomic] at hc
      | _ => simp [uexecT, hd]
    rw [this]
    rcases Split.stepT_out_cases hc π s with h | h <;> simp [h]

/-! ## The certificate -/

/-- **Row 3 on L.** A program `tcheck` accepts emits only predicted delimiter counts, on every
    input the attacker can choose and at every fuel. `tcheck []` assumes nothing about any string. -/
theorem tcheck_traceI {P : Partition} {c : UCmd} {C' : TaintEnv} {Ks : List Nat}
    (h : tcheck [] c = some (C', Ks)) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangI P π) (injectionFree Ks) c := by
  intro n i _
  obtain ⟨f, hf⟩ := tcheck_finishes c [] C' Ks h π (initI i.1 i.2)
  have hrun := evs_tcheck c [] C' Ks h f π (initI i.1 i.2) (by intro _ p hp; simp at hp)
  exact injectionFree_prefixClosed Ks _ _ (runS_within (s := initI i.1 i.2) rfl hf n).1 hrun

/-! ## Witnesses -/

/-- **Accepted**: the sanitised query carries the certificate on every input. -/
theorem safeQuery_traceI (P : Partition) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangI P π) (injectionFree [2]) safeQuery :=
  tcheck_traceI sanitised_query_checks π

/-- The attack payload, as an input. -/
def attackInput : String → UStr := fun y => if y == "input" then [.quote] else []

/-- **Refused**: on the malicious input the vulnerable query emits three delimiters, so the
    certificate fails, and it fails on `ucmdLangI`, where the attacker has an entry point. -/
theorem vulnQuery_traceI_fails :
    ¬ LCore.Cert.trace (ucmdLangI Psec (fun _ => true)) (injectionFree [2]) vulnQuery := by
  intro h
  have hm : LCore.Ev.emit "db" [0, 1, 1, 1] ∈
      ((ucmdLangI Psec (fun _ => true)).run 20 vulnQuery (fun _ => 0, attackInput)).ev := by
    decide
  exact absurd (h 20 (fun _ => 0, attackInput) trivial "db" [0, 1, 1, 1] hm) (by decide)

/-- **Why the input is needed.** On `ucmdLangS`, whose strings start empty, the same vulnerable
    query shows only the two delimiters its author wrote: L had no entry point for this attacker. -/
theorem vulnQuery_empty_shows_two :
    ((ucmdLangS Psec (fun _ => true)).run 20 vulnQuery (fun _ => 0)).ev = [.emit "db" [0, 1, 1]] := by
  decide

end ConfTyping
