/-
  **`bcheck`'s noninterference on every partial run** (F2 step 3, port 4 of 4). Not Ring 0.

  `jsecTy_sound` relates two runs `uexec` finishes (or two that both run out of fuel). On
  `ucmdLangT` the certificate is `Cert.rel`: two runs from Low-equal stores give the same
  record at every fuel, events, leakage (branch bits and addresses), cost and outcome, whether
  they finish, abort or run out of fuel. Proved by induction on fuel and on the `JSecTy`
  derivation (Low-guard `ite` and the widened loop rule `whileW` are the only control rules,
  so both runs always take the same branch). At each finished sub-run the bridge and the
  existing `jsecTy_sound`, `jsecTy_addrEq`, `SepCert` and `toLabInv` re-establish the joint
  relation (`jrel_done`); an atomic step is the same on both sides by those theorems at fuel 1
  (`stepT_same`).
-/
import ConfTyping.MemT

namespace ConfTyping

/-- What two runs keep in common while they stay in step: the memory and label invariants on
    both sides, Low-equality (`uLowEqA`), and the same addresses in the tracked variables. -/
def JRel (P : Partition) (V : List String) (s s' : UState) : Prop :=
  SepInv V s ∧ SepInv V s' ∧ LabInv P V s ∧ LabInv P V s' ∧ uLowEqA P s s' ∧ AddrEq V s s'

theorem JRel.mono {P : Partition} {V W : List String} {s s' : UState} (hsub : ∀ x ∈ W, x ∈ V)
    (h : JRel P V s s') : JRel P W s s' :=
  ⟨SepInv.mono hsub h.1, SepInv.mono hsub h.2.1, LabInv.mono hsub h.2.2.1,
   LabInv.mono hsub h.2.2.2.1, h.2.2.2.2.1, AddrEq.mono hsub h.2.2.2.2.2⟩

/-- Two finished runs of a typed command end related, by the bridge and the existing
    finished-run theorems. -/
theorem jrel_done {P : Partition} {V V' : List String} {c : UCmd} (hj : JSecTy P V c V')
    {n : Nat} {π : MedPolicy} {s s' : UState} (hr : JRel P V s s')
    (hd : (uexecT n c π s).out = .done) (hd' : (uexecT n c π s').out = .done) :
    JRel P V' (uexecT n c π s).st (uexecT n c π s').st := by
  obtain ⟨u, _⟩ := uexecT_done_agree n c π s hd
  obtain ⟨u', _⟩ := uexecT_done_agree n c π s' hd'
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  have hlow := jsecTy_sound n c V V' hj π s s' h1 h2 h3 h4 h5
  have hadd := jsecTy_addrEq n c V V' hj π s s' h1 h2 h3 h4 h5 h6
  rw [u, u'] at hlow hadd
  exact ⟨hj.toSepCert.safe n π s _ h1 u, hj.toSepCert.safe n π s' _ h2 u',
    hj.toLabInv n π s _ h1 h3 u, hj.toLabInv n π s' _ h2 h4 u', hlow.1, hadd⟩

/-- Two records an observer cannot tell apart. -/
def TRun.Same (a b : TRun) : Prop := a.ev = b.ev ∧ a.lk = b.lk ∧ a.cost = b.cost ∧ a.out = b.out

theorem TRun.seqT_same {a a' : TRun} {k k' : UState → TRun} (h : a.Same a')
    (hk : a.out = .done → (k a.st).Same (k' a'.st)) : (a.seqT k).Same (a'.seqT k') := by
  obtain ⟨he, hl, hc, ho⟩ := h
  unfold TRun.seqT
  by_cases ha : a.out = .done
  · have ha' : a'.out = .done := ho ▸ ha
    obtain ⟨he', hl', hc', ho'⟩ := hk ha
    simp only [ha, ha', ↓reduceIte]
    exact ⟨by rw [he, he'], by rw [hl, hl'], by rw [hc, hc'], ho'⟩
  · have ha' : ¬ a'.out = .done := ho ▸ ha
    simp only [ha, ha', ↓reduceIte]
    exact ⟨he, hl, hc, ho⟩

theorem TRun.tick_same {a a' : TRun} (l : LCore.Lk) (h : a.Same a') : (a.tick l).Same (a'.tick l) :=
  ⟨h.1, by simp only [TRun.tick, h.2.1], by simp only [TRun.tick, h.2.2.1], h.2.2.2⟩

/-! ## One atomic step -/

/-- **Two related live states take indistinguishable atomic steps**, by the existing theorems
    at fuel 1: `jsecTy_sound` (state, cost), `jsecTy_addrs` (addresses) and `SepCert` (no
    fault on either side). The emitted string is read off the two sinks, which agree. -/
theorem stepT_same {P : Partition} {V V' : List String} {c : UCmd} (hj : JSecTy P V c V')
    {π : MedPolicy} {s s' : UState} (hr : JRel P V s s') (hd : s.dead = false) :
    (stepT c π s).Same (stepT c π s') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  have hlow := jsecTy_sound 1 c V V' hj π s s' h1 h2 h3 h4 h5
  have hadd := jsecTy_addrs 1 c V V' hj π s s' h1 h2 h3 h4 h5 h6
  have hd' : s'.dead = false := h5.2.2.1 ▸ hd
  unfold stepT
  rcases e : uexec 1 c π s with _ | r <;> rcases e' : uexec 1 c π s' with _ | r' <;>
    rw [e, e'] at hlow
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact hlow.elim
  · exact hlow.elim
  obtain ⟨hst, hcost, _⟩ := hlow
  have herr : r.1.err = false := (hj.toSepCert.safe 1 π s r h1 e).1
  have herr' : r'.1.err = false := (hj.toSepCert.safe 1 π s' r' h2 e').1
  refine ⟨?_, by simp only [hadd], hcost, by simp only [hst.2.2.1]⟩
  simp only [herr, herr', Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  -- only an emit's event depends on the state, and the two sinks agree
  cases c with
  | sop op q x =>
    cases op with
    | emit =>
      have hs := hst.2.2.2.2.2.1
      simp only [uexec, hd, hd', Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at e e'
      rw [← e, ← e'] at hs
      simp only [List.cons.injEq, Prod.mk.injEq] at hs
      simp only [stepEv, hs.1.2]
    | set => rfl
  | _ => rfl

/-! ## Noninterference on every partial run -/

/-- **`JSecTy`'s noninterference on partial runs.** Two related states give indistinguishable
    records at every fuel: the same events, leakage, cost and outcome, whether the runs finish,
    abort or run out of fuel. -/
theorem jsecTy_sameT {P : Partition} (π : MedPolicy) : ∀ (n : Nat) (c : UCmd) (V V' : List String),
    JSecTy P V c V' → ∀ (s s' : UState), JRel P V s s' →
      (uexecT n c π s).Same (uexecT n c π s') := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _; exact ⟨rfl, rfl, rfl, rfl⟩
  | succ m ih =>
    intro c V V' hj s s' hr
    have hdd : s.dead = s'.dead := hr.2.2.2.2.1.2.2.1
    by_cases hd : s.dead = true
    · have hd' : s'.dead = true := hdd ▸ hd
      simp only [uexecT, hd, hd', ↓reduceIte]; exact ⟨rfl, rfl, rfl, rfl⟩
    have hd0 : s.dead = false := by simpa using hd
    have hd' : s'.dead = false := hdd ▸ hd0
    have hj0 := hj
    cases hj with
    | seq h1 h2 =>
      simp only [uexecT, hd0, hd', Bool.false_eq_true, ↓reduceIte]
      exact TRun.seqT_same (ih _ _ _ h1 s s' hr)
        (fun ha => ih _ _ _ h2 _ _ (jrel_done h1 hr ha ((ih _ _ _ h1 s s' hr).2.2.2 ▸ ha)))
    | iteL e he h1 h2 =>
      have hg : evalE e s.store = evalE e s'.store := evalE_lowEq e he hr.2.2.2.2.1.1
      simp only [uexecT, hd0, hd', Bool.false_eq_true, ↓reduceIte, hg]
      apply TRun.tick_same
      split
      · exact ih _ _ _ h1 s s' hr
      · exact ih _ _ _ h2 s s' hr
    | whileW e he hWV hc hWW =>
      have hg : evalE e s.store = evalE e s'.store := evalE_lowEq e he hr.2.2.2.2.1.1
      simp only [uexecT, hd0, hd', Bool.false_eq_true, ↓reduceIte, hg]
      by_cases hgc : evalE e s'.store ≠ 0
      · rw [ite_eq_left hgc, ite_eq_left hgc]
        have hrW := JRel.mono hWV hr
        apply TRun.tick_same
        exact TRun.seqT_same (ih _ _ _ hc s s' hrW)
          (fun ha => ih _ _ _ (JSecTy.whileW e he (fun x h => h) hc hWW) _ _
            (JRel.mono hWW (jrel_done hc hrW ha ((ih _ _ _ hc s s' hrW).2.2.2 ▸ ha))))
      · rw [ite_eq_right hgc, ite_eq_right hgc]; exact ⟨rfl, rfl, rfl, rfl⟩
    | _ =>
      simp only [uexecT, hd0, hd', Bool.false_eq_true, ↓reduceIte]
      exact stepT_same hj0 hr hd0

/-- **The noninterference certificate on the lawful language.** Two runs of a
    `bcheck`-accepted program from Low-equal stores are indistinguishable at every fuel:
    events, leakage (branch bits and addresses), cost and outcome. -/
theorem bcheck_relT {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.rel (ucmdLangT P π) c := by
  intro n σ σ' _ _ hσ
  have hf := bcheck_sound c [] [] A' V' k h
  have hr : JRel P [] (initU σ) (initU σ') :=
    ⟨SepInv.initU, SepInv.initU, LabInv.initU, LabInv.initU,
     ⟨hσ, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
     fun _ x hx => by simp at hx⟩
  obtain ⟨he, hl, hc, ho⟩ := jsecTy_sameT π n c [] V' hf.joint _ _ hr
  show ({ ev := _, lk := _, cost := _, out := _ } : LCore.Beh) = { ev := _, lk := _, cost := _, out := _ }
  rw [he, hl, hc, ho]

/-! ## Adequacy on the lawful language -/

/-- **Adequacy, on `ucmdLangT`** (F2). A program `bcheck` accepts carries, on the lawful
    language, the kernel's three shapes for its four guarantees: its budget is a `bound`, its
    mediation and its memory safety are `trace`s, and its noninterference (addresses in the
    leakage) is a `rel`. Unlike `bcheck_lcore` on `ucmdLang`, every run counts: finished,
    aborted, or out of fuel. -/
theorem bcheck_lcoreT {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.bound (ucmdLangT P π) k c
  ∧ LCore.Cert.trace (ucmdLangT P π) (mediated π) c
  ∧ LCore.Cert.trace (ucmdLangT P π) (fun evs => faultEv ∉ evs) c
  ∧ LCore.Cert.rel (ucmdLangT P π) c :=
  ⟨bcheck_boundT h π, bcheck_mediatedT h π, bcheck_memsafeT h π, bcheck_relT h π⟩

end ConfTyping
