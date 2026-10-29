/-
  Three certificate shapes, their meaning defined once (PLAN-2026-10 §2, `Cert.lean`). Ring 0.

  Every certificate L carries is an instance of one of these, over any `Lang`:
  - `trace Φ`: every run's events satisfy `Φ`. Mediation, memory safety, taint and path
    properties, and the absence of leaks are all `trace` instances.
  - `rel`: inputs the attacker cannot tell apart give the same observation. Since `Beh` is all
    observable (events, leakage, cost, outcome), this is fuel-indexed termination-sensitive
    noninterference with leakage and cost included, in one equation.
  - `bound k`: every run costs at most `k`.
  "Every run" means every fuel and every input.

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
  ∀ (n : Nat) (i : L.In), Φ (L.run n p i).ev

def rel (L : Lang) (p : L.Prog) : Prop :=
  ∀ (n : Nat) (i i' : L.In), L.lowIn i i' → L.run n p i = L.run n p i'

def bound (L : Lang) (k : Nat) (p : L.Prog) : Prop :=
  ∀ (n : Nat) (i : L.In), (L.run n p i).cost ≤ k

end Cert

end LCore
