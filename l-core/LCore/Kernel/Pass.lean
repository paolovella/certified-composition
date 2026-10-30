/-
  A certified pass, and why certificates never need per-pass proofs (PLAN-2026-10 §2,
  `Pass.lean`). Ring 0.

  A `PassCert S T` is a compiler from `S` to `T` with four facts about the pass, none of them
  about any certificate:
  - **events**: the compiled program's events at target fuel `m` are a prefix of the source's
    at `fuel m`;
  - **cost**: its cost at `m` is at most the (monotone) cost transformer of the source's;
  - **determinacy**: admissible inputs whose source observations agree at `fuel m` give equal
    target observations at `m`;
  - **progress**: a source run that finishes has a target run that finishes, with the same
    events and outcome. No transfer uses it; without it a compiler emitting a loop that does
    nothing would inherit every safety certificate.
  With coverage of the admissible inputs (F3), every certificate shape transfers to a
  certificate of the compiled program in its own language (`trace_transfer` for prefix-closed
  properties, `rel_transfer`, `bound_transfer`), and passes compose (`PassCert.seq`). So a new
  pass costs these four facts and no certificate proofs, and a new certificate costs nothing
  per pass (PLAN-2026-10 §6).

  F4 replaced a single equation (target run = source run at `fuel m`, leakage and cost
  rewritten) with these four, because a lowering where one source step becomes several target
  steps breaks the equation: its extra cost depends on which steps ran, and a run stopped
  between two target steps matches no source fuel exactly. The equation still implies all four
  (`PassCert.ofSim`), which is how lockstep passes such as P1 are built.

  The transformers travel with the compiled program, so `seq` composes the two `Xform`s it
  already holds and never re-runs an earlier stage (30f0720 recompiled, n²/2 times).
-/
import LCore.Kernel.Cert

namespace LCore

/-- How one compiled program's observation relates to its source's: the leakage transformer
    (used by lockstep passes, `PassCert.ofSim`), the cost transformer (monotone, so budgets carry
    over), and which source fuel a target fuel corresponds to. -/
structure Xform where
  lk    : List Lk → List Lk
  cost  : Nat → Nat
  fuel  : Nat → Nat
  costMono : ∀ (a b : Nat), a ≤ b → cost a ≤ cost b

/-- Nothing rewritten. -/
def Xform.id : Xform where
  lk l := l
  cost c := c
  fuel m := m
  costMono _ _ h := h

/-- `t` then `u`: leakage and cost go through `t` first; a target fuel goes back through `u`
    first. -/
def Xform.then (t u : Xform) : Xform where
  lk l := u.lk (t.lk l)
  cost c := u.cost (t.cost c)
  fuel m := t.fuel (u.fuel m)
  costMono a b h := u.costMono _ _ (t.costMono a b h)

structure PassCert (S T : Lang) where
  /-- The compiler, returning the compiled program and its transformers. A refusal carries a
      diagnostic, which is untrusted text. -/
  comp  : S.Prog → Except String (T.Prog × Xform)
  /-- How a source input is presented to the compiled program. -/
  enc   : S.In → T.In
  /-- **Coverage** (F3). Admissible source inputs encode to admissible target inputs; every
      admissible target input is the encoding of an admissible source input; and every Low-equal
      pair of admissible target inputs is the encoding of a Low-equal source pair. Without it a
      certificate would reach only the encodings, and an attacker picks an input that is not
      one. -/
  enc_adm   : ∀ i, S.Adm i → T.Adm (enc i)
  cover     : ∀ u, T.Adm u → ∃ i, S.Adm i ∧ enc i = u
  low_cover : ∀ u u', T.Adm u → T.Adm u' → T.lowIn u u' →
    ∃ i i', S.Adm i ∧ S.Adm i' ∧ S.lowIn i i' ∧ enc i = u ∧ enc i' = u'
  /-- **Events**: a prefix of the source's. -/
  ev_sim : ∀ (p : S.Prog) (p' : T.Prog) (t : Xform), comp p = .ok (p', t) →
    ∀ (m : Nat) (i : S.In), S.Adm i → (T.run m p' (enc i)).ev <+: (S.run (t.fuel m) p i).ev
  /-- **Cost**: bounded by the transformer of the source's. -/
  cost_sim : ∀ (p : S.Prog) (p' : T.Prog) (t : Xform), comp p = .ok (p', t) →
    ∀ (m : Nat) (i : S.In), S.Adm i →
      (T.run m p' (enc i)).cost ≤ t.cost (S.run (t.fuel m) p i).cost
  /-- **Determinacy**: the target observation is fixed by the source observation. -/
  det : ∀ (p : S.Prog) (p' : T.Prog) (t : Xform), comp p = .ok (p', t) →
    ∀ (m : Nat) (i i' : S.In), S.Adm i → S.Adm i' →
      S.run (t.fuel m) p i = S.run (t.fuel m) p i' → T.run m p' (enc i) = T.run m p' (enc i')
  /-- **Progress**: what the source finishes, the target finishes, alike. -/
  progress : ∀ (p : S.Prog) (p' : T.Prog) (t : Xform), comp p = .ok (p', t) →
    ∀ (n : Nat) (i : S.In), S.Adm i → (S.run n p i).out ≠ .fuel →
      ∃ m, (T.run m p' (enc i)).out = (S.run n p i).out ∧
           (T.run m p' (enc i)).ev = (S.run n p i).ev

/-- A property of event traces that holds of every prefix of a trace it holds of. On a lawful
    language every fuel reports a prefix, so these are the properties a `trace` certificate can
    meaningfully state. -/
def PrefixClosed (Φ : List Ev → Prop) : Prop := ∀ a b, a <+: b → Φ b → Φ a

namespace PassCert

variable {S T : Lang} (pc : PassCert S T) {p : S.Prog} {p' : T.Prog} {t : Xform}

/-- Every prefix-closed `trace` certificate transfers: the compiled program carries it in its
    own language, on every admissible input. -/
theorem trace_transfer (h : pc.comp p = .ok (p', t)) {Φ : List Ev → Prop} (hΦ : PrefixClosed Φ)
    (hc : Cert.trace S Φ p) : Cert.trace T Φ p' := by
  intro m u hu
  obtain ⟨i, hi, rfl⟩ := pc.cover u hu
  exact hΦ _ _ (pc.ev_sim p p' t h m i hi) (hc (t.fuel m) i hi)

/-- Every Low-equal pair of admissible target inputs comes from a Low-equal source pair, whose
    observations agree, so the target observations agree: the compiled program is
    noninterferent in its own language. -/
theorem rel_transfer (h : pc.comp p = .ok (p', t)) (hc : Cert.rel S p) : Cert.rel T p' := by
  intro m u u' hu hu' hl
  obtain ⟨i, i', hi, hi', hii, rfl, rfl⟩ := pc.low_cover u u' hu hu' hl
  exact pc.det p p' t h m i i' hi hi' (hc (t.fuel m) i i' hi hi' hii)

/-- A budget transfers through the (monotone) cost transformer. -/
theorem bound_transfer (h : pc.comp p = .ok (p', t)) {k : Nat} (hc : Cert.bound S k p) :
    Cert.bound T (t.cost k) p' := by
  intro m u hu
  obtain ⟨i, hi, rfl⟩ := pc.cover u hu
  exact Nat.le_trans (pc.cost_sim p p' t h m i hi) (t.costMono _ _ (hc (t.fuel m) i hi))

end PassCert

/-- Unfold a composed compilation into its two stages. -/
theorem PassCert.seq_comp_ok {S T U : Lang} {pc : PassCert S T} {qc : PassCert T U} {p : S.Prog}
    {p'' : U.Prog} {tu : Xform}
    (h : (match pc.comp p with
      | .error e => .error e
      | .ok (p', t) => match qc.comp p' with
        | .error e => .error e
        | .ok (p'', u) => .ok (p'', t.then u) : Except String (U.Prog × Xform)) = .ok (p'', tu)) :
    ∃ p' t u, pc.comp p = .ok (p', t) ∧ qc.comp p' = .ok (p'', u) ∧ tu = t.then u := by
  cases hp : pc.comp p with
  | error e => rw [hp] at h; cases h
  | ok r =>
    obtain ⟨p', t⟩ := r
    cases hq : qc.comp p' with
    | error e => rw [hp] at h; dsimp only at h; rw [hq] at h; cases h
    | ok r' =>
      obtain ⟨p₂, u⟩ := r'
      rw [hp] at h; dsimp only at h; rw [hq] at h; cases h
      exact ⟨p', t, u, rfl, hq, rfl⟩

/-- **Passes compose.** Each stage compiles once; the transformers compose (`Xform.then`), and
    each of the four obligations is the two stages' chained. A pipeline of certified passes is
    a certified pass. -/
def PassCert.seq {S T U : Lang} (pc : PassCert S T) (qc : PassCert T U) : PassCert S U where
  comp p := match pc.comp p with
    | .error e => .error e
    | .ok (p', t) => match qc.comp p' with
      | .error e => .error e
      | .ok (p'', u) => .ok (p'', t.then u)
  enc i := qc.enc (pc.enc i)
  enc_adm i hi := qc.enc_adm _ (pc.enc_adm i hi)
  cover u hu := by
    obtain ⟨j, hj, rfl⟩ := qc.cover u hu
    obtain ⟨i, hi, rfl⟩ := pc.cover j hj
    exact ⟨i, hi, rfl⟩
  low_cover u u' hu hu' hl := by
    obtain ⟨j, j', hj, hj', hjj, rfl, rfl⟩ := qc.low_cover u u' hu hu' hl
    obtain ⟨i, i', hi, hi', hii, rfl, rfl⟩ := pc.low_cover j j' hj hj' hjj
    exact ⟨i, i', hi, hi', hii, rfl, rfl⟩
  ev_sim p _ _ h m i hi := by
    obtain ⟨p', t, u, hp, hq, rfl⟩ := PassCert.seq_comp_ok h
    exact (qc.ev_sim p' _ u hq m (pc.enc i) (pc.enc_adm i hi)).trans
      (pc.ev_sim p p' t hp (u.fuel m) i hi)
  cost_sim p _ _ h m i hi := by
    obtain ⟨p', t, u, hp, hq, rfl⟩ := PassCert.seq_comp_ok h
    exact Nat.le_trans (qc.cost_sim p' _ u hq m (pc.enc i) (pc.enc_adm i hi))
      (u.costMono _ _ (pc.cost_sim p p' t hp (u.fuel m) i hi))
  det p _ _ h m i i' hi hi' he := by
    obtain ⟨p', t, u, hp, hq, rfl⟩ := PassCert.seq_comp_ok h
    exact qc.det p' _ u hq m _ _ (pc.enc_adm i hi) (pc.enc_adm i' hi')
      (pc.det p p' t hp (u.fuel m) i i' hi hi' he)
  progress p _ _ h n i hi hf := by
    obtain ⟨p', t, u, hp, hq, rfl⟩ := PassCert.seq_comp_ok h
    obtain ⟨m₁, ho₁, he₁⟩ := pc.progress p p' t hp n i hi hf
    obtain ⟨m₂, ho₂, he₂⟩ := qc.progress p' _ u hq m₁ (pc.enc i) (pc.enc_adm i hi)
      (by rw [ho₁]; exact hf)
    exact ⟨m₂, ho₂.trans ho₁, he₂.trans he₁⟩

/-- **A lockstep pass from one equation.** If the compiled run *is* the source run at `fuel m`
    with leakage and cost rewritten, and every source fuel is some target fuel's image, the four
    obligations follow. P1 and the toy passes are built this way. -/
def PassCert.ofSim {S T : Lang} (comp : S.Prog → Except String (T.Prog × Xform))
    (enc : S.In → T.In)
    (enc_adm : ∀ i, S.Adm i → T.Adm (enc i))
    (cover : ∀ u, T.Adm u → ∃ i, S.Adm i ∧ enc i = u)
    (low_cover : ∀ u u', T.Adm u → T.Adm u' → T.lowIn u u' →
      ∃ i i', S.Adm i ∧ S.Adm i' ∧ S.lowIn i i' ∧ enc i = u ∧ enc i' = u')
    (sim : ∀ (p : S.Prog) (p' : T.Prog) (t : Xform), comp p = .ok (p', t) →
      ∀ (m : Nat) (i : S.In),
      T.run m p' (enc i) =
        { (S.run (t.fuel m) p i) with
            lk   := t.lk (S.run (t.fuel m) p i).lk,
            cost := t.cost (S.run (t.fuel m) p i).cost })
    (fuel_onto : ∀ (p : S.Prog) (p' : T.Prog) (t : Xform), comp p = .ok (p', t) →
      ∀ n, ∃ m, t.fuel m = n) : PassCert S T where
  comp := comp
  enc := enc
  enc_adm := enc_adm
  cover := cover
  low_cover := low_cover
  ev_sim p p' t h m i _ := by rw [sim p p' t h m i]; exact List.prefix_refl _
  cost_sim p p' t h m i _ := by rw [sim p p' t h m i]; exact Nat.le_refl _
  det p p' t h m i i' _ _ he := by rw [sim p p' t h m i, sim p p' t h m i', he]
  progress p p' t h n i _ _ := by
    obtain ⟨m, hm⟩ := fuel_onto p p' t h n
    exact ⟨m, by rw [sim p p' t h m i, hm], by rw [sim p p' t h m i, hm]⟩

end LCore
