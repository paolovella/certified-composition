/-
  BOUND-01, checked before planning: the budget shape the user chose on 2026-11-06, proved against the real kernel in a scratch file.
  Not part of any library. From l-core/: lake env lean -D autoImplicit=false ../research/2026-11/BoundRSketch.lean
  `boundR_late_vacuous` is why VS-2-RESEARCH's first sketch was wrong: a budget chosen after the fuel can always be the cost itself.
-/
import LCore.Kernel.Pass
open LCore

/-- The candidate seventh shape (the kernel has six; a first draft of this comment said sixth): one budget per input, chosen before the fuel, from the relation `R`. -/
def boundR (L : Lang) (R : L.In → Nat → Prop) (p : L.Prog) : Prop :=
  ∀ (i : L.In), L.Adm i → ∃ k, R i k ∧ ∀ (n : Nat), (L.run n p i).cost ≤ k

/-- The budget on the target: some source input encodes to it, with a budget of its own, transformed. -/
def liftR {S T : Lang} (pc : PassCert S T) (t : Xform) (R : S.In → Nat → Prop) : T.In → Nat → Prop :=
  fun u k => ∃ i k', S.Adm i ∧ pc.enc i = u ∧ R i k' ∧ k = t.cost k'

theorem boundR_transfer {S T : Lang} (pc : PassCert S T) {p : S.Prog} {p' : T.Prog} {t : Xform}
    (h : pc.comp p = .ok (p', t)) {R : S.In → Nat → Prop} (hc : boundR S R p) : boundR T (liftR pc t R) p' := by
  intro u hu
  obtain ⟨i, hi, rfl⟩ := pc.cover u hu
  obtain ⟨k, hR, hk⟩ := hc i hi
  exact ⟨t.cost k, ⟨i, k, hi, rfl, hR, rfl⟩, fun m => Nat.le_trans (pc.cost_sim p p' t h m i hi) (t.costMono _ _ (hk (t.fuel m)))⟩

/-- **It generalises `bound`**: a constant budget is the relation `k = c`. -/
theorem bound_iff_boundR (L : Lang) (c : Nat) (p : L.Prog) : Cert.bound L c p ↔ boundR L (fun _ k => k = c) p :=
  ⟨fun h i hi => ⟨c, rfl, fun n => h n i hi⟩, fun h n i hi => by obtain ⟨k, rfl, hk⟩ := h i hi; exact hk n⟩

/-- **And on a constant budget the transfer gives `bound_transfer`'s budget**, so nothing is lost. -/
theorem liftR_const {S T : Lang} (pc : PassCert S T) (t : Xform) (c : Nat) (u : T.In) (k : Nat) :
    liftR pc t (fun _ k => k = c) u k → k = t.cost c := by
  rintro ⟨i, k', _, _, rfl, rfl⟩; rfl

/-- **Not vacuous: a run whose cost grows without bound has no such budget, whatever `R` is.** Even `R` = anything. -/
theorem no_budget_if_unbounded (L : Lang) (R : L.In → Nat → Prop) (p : L.Prog) (i : L.In) (hi : L.Adm i)
    (hgrow : ∀ k, ∃ n, k < (L.run n p i).cost) : ¬ boundR L R p := by
  intro h
  obtain ⟨k, _, hk⟩ := h i hi
  obtain ⟨n, hn⟩ := hgrow k
  exact absurd (hk n) (by omega)

/-- **The first sketch, budget after fuel, is vacuous**: with `R` = anything it holds for every program. -/
def boundR_late (L : Lang) (R : L.In → Nat → Prop) (p : L.Prog) : Prop :=
  ∀ (n : Nat) (i : L.In), L.Adm i → ∃ k, R i k ∧ (L.run n p i).cost ≤ k

theorem boundR_late_vacuous (L : Lang) (p : L.Prog) : boundR_late L (fun _ _ => True) p :=
  fun _ _ _ => ⟨_, trivial, Nat.le_refl _⟩

/-- **A budget that depends only on public input**: `R` respects `lowIn`. Through a pass, `low_cover` keeps that true of the lifted relation's
    witnesses: two Low-equal target inputs come from Low-equal source inputs. -/
def LowR (L : Lang) (R : L.In → Nat → Prop) : Prop := ∀ i i' k, L.lowIn i i' → R i k → R i' k

