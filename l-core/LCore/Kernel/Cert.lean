/-
  Four certificate shapes, their meaning defined once (PLAN-2026-10 §2, `Cert.lean`). Ring 0.

  Every certificate L carries is an instance of one of these, over any `Lang` (a fourth,
  `live`, for what must happen, is below):
  - `trace Φ`: every run's events satisfy `Φ`. Mediation, memory safety, taint and path
    properties, and the absence of leaks are all `trace` instances.
  - `rel`: inputs the attacker cannot tell apart give the same observation. Since `Beh` is all
    observable (events, leakage, cost, outcome), this is fuel-indexed termination-sensitive
    noninterference with leakage and cost included, in one equation.
  - `bound k`: every run costs at most `k`.
  "Every run" means every fuel and every admissible input (`Lang.Adm`, F3; by default every
  input). On a lawful language (`Lang.Lawful`, F2) the run
  at fuel `n` is a prefix of every run with more fuel, so "every fuel" covers every prefix of
  the run, and `bound` forces the run to finish (`Lang.Lawful.bound_finishes`). Not every
  `Lang` is lawful: `ucmdLang` is not yet (F2 step 2), so on it these shapes can still hold
  vacuously (`ConfTyping.Vacuity.vacProg_vacuous`).

  Correction of record (2026-10-29, F0). From 30f0720 to now this docstring said:
  ~~a fuelled run that stops early is a prefix, and each shape must hold of it too~~.
  Nothing checked it, and it is false: `Lang` has no fuel laws, so `run` need not extend with
  more fuel, and `ucmdLang` reports an out-of-fuel run as an empty record. So a program that
  never finishes satisfies every `trace` and every `bound` vacuously. Fuel laws, and shapes
  that speak about every prefix, are item F2 (research/2026-10/FOUNDATION-2026-10-29.md).
  check-claims guard (n) refuses the claim while the kernel has no fuel law.
-/
import LCore.Kernel.Lang

namespace LCore

namespace Cert

def trace (L : Lang) (Φ : List Ev → Prop) (p : L.Prog) : Prop :=
  ∀ (n : Nat) (i : L.In), L.Adm i → Φ (L.run n p i).ev

def rel (L : Lang) (p : L.Prog) : Prop :=
  ∀ (n : Nat) (i i' : L.In), L.Adm i → L.Adm i' → L.lowIn i i' → L.run n p i = L.run n p i'

def bound (L : Lang) (k : Nat) (p : L.Prog) : Prop :=
  ∀ (n : Nat) (i : L.In), L.Adm i → (L.run n p i).cost ≤ k

end Cert

/-- **A run as a whole**: the chain of its observations at every fuel. On a lawful language it
    only grows, and its limit is the run's complete behaviour, finite or infinite. -/
abbrev Chain := Nat → Beh

/-- Two runs with the same limit: each reaches every event prefix the other reaches, and each
    finishes exactly when the other does, with the same events and outcome. Leakage and cost are
    not part of a run's limit: they are what `rel` and `bound` are about. -/
def Chain.Equiv (r r' : Chain) : Prop :=
  (∀ n, ∃ m, (r n).ev <+: (r' m).ev) ∧ (∀ m, ∃ n, (r' m).ev <+: (r n).ev) ∧
  (∀ n, (r n).out ≠ .fuel → ∃ m, (r' m).out = (r n).out ∧ (r' m).ev = (r n).ev) ∧
  (∀ m, (r' m).out ≠ .fuel → ∃ n, (r n).out = (r' m).out ∧ (r n).ev = (r' m).ev)

/-- A property of a run's limit: runs with the same limit both have it or both lack it. -/
def LimitInv (Ψ : Chain → Prop) : Prop := ∀ r r', Chain.Equiv r r' → Ψ r → Ψ r'

namespace Cert

/-- **The fourth shape: liveness** (the user's decision of 2026-10-30). Every admissible run, as a
    whole, satisfies `Ψ`: "eventually emits X", "if it finishes, it ended with a reply", "emits
    X infinitely often". `Ψ` must depend only on the run's limit (`LimitInv`) to transfer through
    a pass. `trace` covers the properties every prefix keeps ("never X"); `live` the ones a
    prefix may not have reached yet. -/
def live (L : Lang) (Ψ : Chain → Prop) (p : L.Prog) : Prop :=
  ∀ (i : L.In), L.Adm i → Ψ (fun n => L.run n p i)

end Cert


/-- **A budget forces termination** on a lawful language: `bound k` is not satisfied by a
    program that never finishes. -/
theorem Lang.Lawful.bound_finishes {L : Lang} (hL : L.Lawful) {k : Nat} {p : L.Prog}
    (h : Cert.bound L k p) (i : L.In) (hi : L.Adm i) : ∃ n, (L.run n p i).out ≠ .fuel := by
  obtain ⟨d, hd⟩ := hL.diverge p
  refine ⟨k + d + 1, fun hf => ?_⟩
  have h1 := hd (k + d + 1) i hf
  have h2 := h (k + d + 1) i hi
  exact Nat.lt_irrefl (k + d)
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans h1 (Nat.add_le_add_right h2 d)))

end LCore
