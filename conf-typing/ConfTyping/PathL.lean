/-
  Path traversal on L (F5, row 14), on `ucmdLangI`, the language whose input includes the attacker's
  strings (`InjectionL.lean`).

  **Attacker:** controls every initial string variable. **Observer:** the sink `fs`. Side channels
  play no part.

  **Shape:** `Cert.trace`. `PathCert` says every string sent to `fs` walks without popping above
  its root, which is a property of one run. It is per-sink by design: a program `pcheck "fs"`
  accepts can send anything to another sink (`dbProg_fs_holds`, `dbProg_db_fails`).

  **Limits.** The alphabet has two symbols, `ord` a segment and `quote` the parent segment `..`, and
  `pcheck` has no loop rule, so `pcheck_traceI` covers loop-free programs. `pcheckW` has one but is
  not on L, for the same reason as `tcheckW`.
-/
import ConfTyping.InjectionL
import ConfTyping.PathCert

namespace ConfTyping

/-! ## The property -/

/-- Reads an emitted payload back as a string. `uchCode` writes the delimiter as 1. -/
def decodeCh : Nat → UCh
  | 1 => .quote
  | _ => .ord

theorem decode_code : ∀ t : UStr, (t.map uchCode).map decodeCh = t
  | [] => rfl
  | .quote :: r => congrArg (UCh.quote :: ·) (decode_code r)
  | .ord :: r => congrArg (UCh.ord :: ·) (decode_code r)

/-- **Every payload emitted to `fs` stays inside its root.** -/
def pathSafe (fs : String) (evs : List LCore.Ev) : Prop :=
  ∀ d, LCore.Ev.emit fs d ∈ evs → safePath (d.map decodeCh) = true

theorem pathSafe_prefixClosed (fs : String) : LCore.PrefixClosed (pathSafe fs) :=
  fun _ _ hab hb d hm => hb d (hab.subset hm)

/-! ## From `pcheck` to the events of a run -/

/-- **A checked program's run sends only safe paths to `fs`, at every fuel.** -/
theorem evs_pcheck (fs : String) : ∀ (c : UCmd) (C C' : TaintEnv), pcheck fs C c = some C' →
    ∀ (n : Nat) (π : MedPolicy) (s : UState), TaintInv C s → pathSafe fs (uexecT n c π s).ev
  | .seq a b, C, C', h, n, π, s, hs => by
    cases h1 : pcheck fs C a with
    | none => simp [pcheck, h1] at h
    | some C₁ =>
      have h2 : pcheck fs C₁ b = some C' := by simpa [pcheck, h1] using h
      intro d hm
      rcases n with _ | n
      · simp [uexecT] at hm
      by_cases hd : s.dead = true
      · simp [uexecT, hd] at hm
      simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.seqT] at hm
      by_cases ha : (uexecT n a π s).out = .done
      · simp only [ha, ↓reduceIte, List.mem_append] at hm
        rcases hm with hm | hm
        · exact evs_pcheck fs a C C₁ h1 n π s hs d hm
        · have henv := (pcheck_sound fs a C C₁ h1).env n π s _ hs (uexecT_done_agree n a π s ha).1
          exact evs_pcheck fs b C₁ C' h2 n π _ henv d hm
      · simp only [ha, ↓reduceIte] at hm
        exact evs_pcheck fs a C C₁ h1 n π s hs d hm
  | .ite e a b, C, C', h, n, π, s, hs => by
    cases h1 : pcheck fs C a with
    | none => simp [pcheck, h1] at h
    | some C₁ =>
      cases h2 : pcheck fs C b with
      | none => simp [pcheck, h1, h2] at h
      | some C₂ =>
        intro d hm
        rcases n with _ | n
        · simp [uexecT] at hm
        by_cases hd : s.dead = true
        · simp [uexecT, hd] at hm
        simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.tick] at hm
        by_cases hg : evalE e s.store ≠ 0
        · simp only [hg, ↓reduceIte, ne_eq, not_false_eq_true] at hm
          exact evs_pcheck fs a C C₁ h1 n π s hs d hm
        · simp only [hg, ↓reduceIte] at hm
          exact evs_pcheck fs b C C₂ h2 n π s hs d hm
  | .loop _ _, _, _, h, _, _, _, _ => by simp [pcheck] at h
  | .sop .emit x e, C, C', h, n, π, s, hs => by
    intro d hm
    obtain ⟨hd, e', he, rfl⟩ := atomic_emit rfl hm
    cases he
    simp only [pcheck, beq_self_eq_true, ↓reduceIte] at h
    cases hk : spath C 0 e with
    | none => simp [hk] at h
    | some k =>
      obtain ⟨dd, hw, _⟩ := spath_sound (hs hd) e 0 k hk
      rw [decode_code]
      simp [safePath, hw]
  | .sop .set _ _, _, _, _, _, _, _, _ => fun _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .skip, _, _, _, _, _, _, _ => fun _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .assign _ _, _, _, _, _, _, _, _ => fun _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .check _, _, _, _, _, _, _, _ => fun _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .access _, _, _, _, _, _, _, _ => fun _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .memop _ _, _, _, _, _, _, _, _ => fun _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he
  | .hop _ _ _, _, _, _, _, _, _, _ => fun _ hm => by
    obtain ⟨_, _, he, _⟩ := atomic_emit rfl hm; cases he

/-- `pcheck` accepts only loop-free programs. -/
theorem pcheck_noLoop (fs : String) : ∀ (c : UCmd) (C C' : TaintEnv),
    pcheck fs C c = some C' → noLoop c = true
  | .seq a b, C, C', h => by
    cases h1 : pcheck fs C a with
    | none => simp [pcheck, h1] at h
    | some C₁ =>
      have h2 : pcheck fs C₁ b = some C' := by simpa [pcheck, h1] using h
      simp only [noLoop, Bool.and_eq_true]
      exact ⟨pcheck_noLoop fs a C C₁ h1, pcheck_noLoop fs b C₁ C' h2⟩
  | .ite e a b, C, C', h => by
    cases h1 : pcheck fs C a with
    | none => simp [pcheck, h1] at h
    | some C₁ =>
      cases h2 : pcheck fs C b with
      | none => simp [pcheck, h1, h2] at h
      | some C₂ =>
        simp only [noLoop, Bool.and_eq_true]
        exact ⟨pcheck_noLoop fs a C C₁ h1, pcheck_noLoop fs b C C₂ h2⟩
  | .loop _ _, _, _, h => by simp [pcheck] at h
  | .sop _ _ _, _, _, _ => rfl
  | .skip, _, _, _ => rfl
  | .assign _ _, _, _, _ => rfl
  | .check _, _, _, _ => rfl
  | .access _, _, _, _ => rfl
  | .memop _ _, _, _, _ => rfl
  | .hop _ _ _, _, _, _ => rfl

/-! ## The certificate -/

/-- **Row 14 on L.** A program `pcheck fs` accepts sends only safe paths to `fs`, on every input the
    attacker can choose and at every fuel. `pcheck fs []` assumes nothing about any string. -/
theorem pcheck_traceI {P : Partition} {fs : String} {c : UCmd} {C' : TaintEnv}
    (h : pcheck fs [] c = some C') (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangI P π) (pathSafe fs) c := by
  intro n i _
  obtain ⟨f, hf⟩ := noLoop_finishes c (pcheck_noLoop fs c [] C' h) π (initI i.1 i.2)
  have hrun := evs_pcheck fs c [] C' h f π (initI i.1 i.2) (by intro _ p hp; simp at hp)
  exact pathSafe_prefixClosed fs _ _ (runS_within (s := initI i.1 i.2) rfl hf n).1 hrun

/-! ## Witnesses -/

/-- **Accepted**: the sanitised path carries the certificate on every input. -/
theorem safePathProg_traceI (P : Partition) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangI P π) (pathSafe "fs") safePathProg :=
  pcheck_traceI safe_path_checks π

/-- The traversal payload `../..`, as an input. -/
def escapeInput : String → UStr := fun y => if y == "input" then [.quote, .quote] else []

/-- **Refused**: on the traversal input the vulnerable program emits a path that pops above its
    root, so the certificate fails. -/
theorem vulnPath_traceI_fails :
    ¬ LCore.Cert.trace (ucmdLangI Psec (fun _ => true)) (pathSafe "fs") vulnPath := by
  intro h
  have hm : LCore.Ev.emit "fs" [0, 1, 1] ∈
      ((ucmdLangI Psec (fun _ => true)).run 20 vulnPath (fun _ => 0, escapeInput)).ev := by
    decide
  exact absurd (h 20 (fun _ => 0, escapeInput) trivial [0, 1, 1] hm) (by decide)

/-- **Why the input is needed.** On `ucmdLangS`, whose strings start empty, the vulnerable program
    sends only the segment its author wrote. -/
theorem vulnPath_empty_is_safe :
    ((ucmdLangS Psec (fun _ => true)).run 20 vulnPath (fun _ => 0)).ev = [.emit "fs" [0]] := by
  decide

/-- A program that sends the attacker's string to a sink other than `fs`. -/
def dbProg : UCmd := .sop .emit "db" (.cat (.lit [.ord]) (.var "input"))

/-- **The property is per-sink.** `pcheck "fs"` accepts this program, so `fs` is safe... -/
theorem dbProg_fs_holds (P : Partition) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangI P π) (pathSafe "fs") dbProg :=
  pcheck_traceI query_sink_untouched_by_path_checker π

/-- ...and the same program sends an escaping path to `db`, which the certificate does not cover. -/
theorem dbProg_db_fails :
    ¬ LCore.Cert.trace (ucmdLangI Psec (fun _ => true)) (pathSafe "db") dbProg := by
  intro h
  have hm : LCore.Ev.emit "db" [0, 1, 1] ∈
      ((ucmdLangI Psec (fun _ => true)).run 20 dbProg (fun _ => 0, escapeInput)).ev := by
    decide
  exact absurd (h 20 (fun _ => 0, escapeInput) trivial [0, 1, 1] hm) (by decide)

end ConfTyping
