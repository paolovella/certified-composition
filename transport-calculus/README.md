# Transport calculus — a common interface for transport theorems

Lean 4, **mathlib-free**, no `sorry`. A small interface abstracted
from the confidentiality-typing work: a transport morphism is a map *bundled
with its certificate*, and composition **accumulates** certificates (multiplies
grades, threads the contraction proofs) — never discharges silently.

```
lean TransportCalculus.lean    # compiles instantly, no dependencies
```

## The object

- `GradedAction M D` — a **grade monoid `M` acting on a distance order `D`**:
  grade composition `mul : M → M → M`, an order `le : D → D → Prop`, and a
  monotone action `act : M → D → D` with `act (m₁*m₂) d = act m₁ (act m₂ d)`.
- `Bridge X M D GA d` — a map on `X`, a grade `cert : M`, and a proof
  `contracts` that the map contracts the distance `d : X → X → D` by the
  *action* of `cert`.
- `Bridge.comp g f` — the **composition law**: the composite carries grade
  `g.cert * f.cert` (in `M`), and its contraction proof is *threaded from* the
  two inputs' via `act_mul` + `act_mono`. Drop the multiplication and
  `contracts` no longer type-checks.

## What the axiom footprint settles

| theorem | axioms |
|---|---|
| `Bridge.comp` (accumulation) | **none** |
| `Bridge.comp_cert` (grade = product, by `rfl`) | **none** |

`Bridge.comp` depends on **no axioms and no mathlib** — the interface is *incidental
to* reals and measure theory **by construction of the repo**, not by post-hoc
inspection.

## The eighth catch — corrected by a real instance, not by me

v1 used a *single* type `G` for both grade and distance, with one
`mul : G → G → G`. That was over-identification. mathlib's actual `LipschitzWith`
carries grades in `ℝ≥0` and distances (`edist`) in `ℝ≥0∞` — **two types**, the
certificate a scalar *action*, with composition `LipschitzWith (Kf * Kg) (f ∘ g)`
multiplying grades in `ℝ≥0`. My only prior instance, `Nat`, *coincided* grade and
distance (`M = D`), which hid the conflation.

Stated at the right precision (the discipline cuts here too): the real instance
does **not refute** the single-type version — it fits, via the coercion
`ℝ≥0 ↪ ℝ≥0∞`. What it reveals is the *conflation*. The faithful structure
separates the grade monoid `M` from the distance carrier `D`; `Nat` is recovered
as the degenerate `M = D` case. This is the first correction in the whole arc
delivered by **contact with an object I did not design** — exactly the test of
whether an abstraction read off one's own proof survives reality.

## The earned abstraction (corrected)

`Bridge.comp` uses exactly `GradedAction` and no more: `mul`, `le`, `act`,
`le_trans`, `act_mul`, `act_mono`. No addition, no triangle inequality, no
symmetry, no identity, no commutativity, **no `M = D`**. The interface lives over a
**grade monoid acting monotonically on a distance order** — the lean core of an
"`ℝ≥0`-enriched category of contractive morphisms," now with grade and carrier
correctly distinct.

## The lineage (same accountancy, made primitive)

The certificate-accumulation discipline is the invariant of the confidentiality
work, ported: `Discharge.pol` carried `(φ, proof)` not membership;
`confidential_transport` accumulated both strata across the gate; the assumption
ledger tracked which theorem used which condition. Here the certificate is a
grade and accumulation is multiplication. The **degenerate slice** — bare
non-expansiveness, grade `≤ 1` for everything, the empty/constant certificate —
is `noPolicy` one level up: nothing to accumulate, so it tests nothing.

## Concrete inhabitant — the degenerate `M = D` case (mathlib-free)

`natGA : GradedAction Nat Nat`, `double : Bridge Nat Nat Nat natGA dist` — the
doubling map, Lipschitz-2, with `Nat` playing *both* grade and distance (the
coincidence that hid the conflation). Two compose to Lipschitz-4:
`(double.comp double).cert = 4` by `rfl`. Accumulation witnessed.

## Status of the instances (see the `transport-kernel/` companion)

- **`LipschitzWith` (`M = ℝ≥0`, `D = ℝ≥0∞`) — received.** The real instance that
  *forced* the `M`/`D` separation. `comp_reconstructs_lipschitz` shows the generic
  `Bridge.comp` reconstructs mathlib's `LipschitzWith.comp`.
- **`HolderWith` (`M = ℝ≥0 × ℝ≥0`, `D = ℝ≥0∞`) — received.** A *non-scalar*
  certificate `(C, r)` with a semidirect-product law `(Cg·Cf^rg, rg·rf)`;
  `comp_reconstructs_holder` reconstructs `HolderWith.comp`. Two different
  accumulation *algebras*, one `Bridge.comp`.
- **Markov-kernel / Dobrushin (`M = ℝ≥0`, `D = ℝ≥0∞` = TV) — deferred.** Needs the
  data-processing inequality / Dobrushin coefficient, which mathlib lacks — a
  genuine from-scratch formalization (century-old probability, *not* the novel
  part). The interface only has to *receive* it; accumulation is already proved.
