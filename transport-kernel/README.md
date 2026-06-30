# transport-kernel — the genus, instantiated against mathlib

Companion to the mathlib-free `transport-calculus` repo (which states the genus
and proves `Bridge.comp` with **zero axioms**). This repo does the thing a
mathlib-free abstraction cannot do for itself: **plug the interface into objects
someone else built**, and see whether it receives them.

Requires the mathlib olean cache (`lake exe cache get`); needs Lean 4.31.0.

## The three-tier cost ledger (so it isn't rediscovered mid-session)

| tier | what | cost | status |
|---|---|---|---|
| 1 | olean cache | multi-GB infra; gates *importing anything* | **done** (5.8G, 8542 oleans) |
| 2a | `LipschitzWith` receive | cache only — no new math | **done**, this repo |
| 2b | `HolderWith` receive | cache only — non-scalar certificate | **done**, this repo |
| 3 | Dobrushin / TV instance | cache **+** from-scratch data-processing inequality | deferred (Paper-2 brick) |

## Tier 2 — the result (`TransportKernel/LipschitzReceive.lean`)

The genus receives mathlib's actual contractive morphisms:

- `lipGA : GradedAction ℝ≥0 ℝ≥0∞` — contraction constants (`ℝ≥0`) acting on
  extended distances (`ℝ≥0∞`) by coerced multiplication. **Grade ≠ distance** —
  the `M ≠ D` separation the eighth catch forced, now carried by the real types
  mathlib uses, with the coercion `ℝ≥0 ↪ ℝ≥0∞` as the action.
- `Bridge.ofLipschitz hf` — a `LipschitzWith K f` hypothesis lands *directly* in
  the `contracts` slot, no proof work: `edist (f x) (f y) ≤ K * edist x y` is
  exactly the certificate the interface asks for.
- `comp_reconstructs_lipschitz` — **the reception, as a theorem**: the generic
  `Bridge.comp` applied to two Lipschitz bridges is, definitionally, a proof of
  `LipschitzWith (Kf * Kg) (f ∘ g)`. The interface reproduces mathlib's own
  `LipschitzWith.comp` from generic certificate accumulation.

So the abstraction read off one toy proof (`Nat`, the degenerate `M = D` slice)
**receives an independently-built instance** (ℝ≥0 acting on ℝ≥0∞) and recovers
its composition law. That is reuse evidence of the only kind that counts:
survival of contact with an object not designed to fit.

## Tier 2b — a *different certificate algebra* (`TransportKernel/HolderReceive.lean`)

Lipschitz is a scalar certificate (`ℝ≥0`) accumulating by multiplication. Hölder
continuity is the harder test: the certificate is a **pair** `(C, r) : ℝ≥0 × ℝ≥0`
and `HolderWith.comp` accumulates it by a *semidirect-product* law

```
(Cg, rg) ⋄ (Cf, rf) = (Cg · Cf ^ rg,  rg · rf)      acting on distance by  C · d ^ r
```

- `holderGA : GradedAction (ℝ≥0 × ℝ≥0) ℝ≥0∞` — the non-scalar grade monoid; the
  `act_mul` field is real `rpow` algebra (`mul_rpow_of_nonneg`, `rpow_mul`,
  `coe_rpow_of_nonneg`), and it closes.
- `comp_reconstructs_holder` — the **same** generic `Bridge.comp` reconstructs
  `HolderWith.comp`, definitionally, no extra proof work.

This is the instance that settles the review's "certificate need not be numeric":
the grade monoid here is `ℝ≥0 × ℝ≥0` with a twisted multiplication, not a number.
Two takeaways:

- **The interface is reusable across accumulation *algebras*, not just objects.**
  Lipschitz (scalar) and Hölder (pair, semidirect) are *different monoids*, and
  the same `Bridge.comp` serves both. (Note `HolderWith C 1 = LipschitzWith C`,
  so Lipschitz is the `r = 1` slice — same object, but a genuinely different
  grade algebra, which is the point.)
- **It retroactively justifies keeping the name `GradedAction`.** A "grade" need
  not be numeric — a grading by *any* monoid qualifies, and `ℝ≥0 × ℝ≥0` with the
  semidirect law is exactly such a monoid. So the review's suggested rename to
  `CertifiedAction` would have been lateral, not corrective; declining it (as
  naming ahead of an instance) was right, and this instance shows why.
- **The interface asks only for `act_mul`, not standalone monoid associativity.**
  The Hölder `⋄` *is* associative, but the existence proof never needed that —
  composition of two bridges requires only the action-compatibility `act_mul`.
  Leaner than a monoid action.

## What this is *not* (kept honest)

- Not "the genus is correct" — one external instance is one data point, not a
  characterization. The right next move (per review) is *more* mathlib
  composition theorems of the same morphism/certificate/accumulated-certificate
  shape, before any heavy formalization.
- Not the Dobrushin instance. mathlib has kernels and TV pieces but **not** the
  data-processing inequality or the Dobrushin coefficient (confirmed by grep), so
  that contraction lemma is a genuine from-scratch formalization — century-old,
  non-novel probability, multi-session. Deferred. The interface only has to
  *receive* it; accumulation is already proved generically.

## Naming note

The structure is `GradedAction` and `cert` is its grade. The certificate need
not be numeric — the math requires only an associative composition, an action,
and monotonicity — so a non-numeric certificate (a policy, an effect) could
inhabit it. It is *not* renamed to `CertifiedAction` preemptively: that would be
naming ahead of an instance that forces it. Rename when one lands, not before.
