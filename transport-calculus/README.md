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

## Scope — the boundary, and what it is *not*

Three fitting instances (`Nat`, `Lipschitz`, `Hölder`) and zero counterexamples
is **not** "the interface is correct" — it is "not yet refuted." Correctness for
an abstraction is the absence of a counterexample you have not found; the content
is the boundary, not the catalogue of things that fit. A fourth fitting instance
buys almost nothing.

**The load-bearing assumption is one line:** `Bridge.comp` sets
`cert := mul g.cert f.cert` — the composite's certificate is a function of the two
component certificates *alone*. So `GradedAction` captures exactly **functorial
accumulation**: the certificate must be a *composable invariant* (a monoid acting
on the distance). This is the transport-side restatement of **separability** from
`../conf-typing`: `mul`-existence here ≙ "`J` of the join is determined by `J` of
the parts" there.

**Differential privacy — two rows, not one.** DP must be filed under *two*
certificates, because filing it flatly as "inside via Rényi" buries the half that
does not fit:

- **f-DP / privacy-loss distribution — inside.** The trade-off function is a
  *composable invariant*: it tensors associatively (Dong–Roth–Su), and advanced
  composition is a corollary. Advanced composition's `√k` bound is *uniform over
  all `(ε,δ)` mechanisms* — it depends on the count and the certificates, **not**
  on the maps — so it factors through this invariant. Rényi / zCDP are the same
  invariant in additive coordinates (`ρ` adds; `√k` is `ε ≈ √ρ`).
- **`(ε, δ)` — a lossy projection that does not compose.** Two mechanisms with
  equal `(ε,δ)` but different privacy-loss distributions compose to different
  `(ε',δ')`, so `(ε,δ)` admits **no** `mul`. This is not a non-example of the
  *interface* (the invariant, f-DP, fits) — it is a non-example of "`(ε,δ)` is a
  composable invariant," the precise analog of the non-separable per-channel
  summary `J_ε` exposed. Advanced composition is **not** the boundary; it factors.
  The boundary it *seems* to be is an artifact of choosing the lossy summary.

`summary_not_composable` proves this in miniature, mathlib-free: a composable
monoid (`ℕ×ℕ, +`) whose lossy summary (product of coordinates) provably admits no
`mul` — `(1,2)` and `(2,1)` share summary `2` but compose to summaries `4 ≠ 3`.
That is the located transport-side `Rbad`: the genuine non-example is a **lossy
summary**, not a phenomenon, and it sits one level down from `GradedAction`.

**The non-associativity hunt resolves negatively — with a proof, not a search.**
A natural guess for "what falls outside" is *non-associative* accumulation. It is
malformed: `GradedAction.act_assoc` shows that for **any** `mul`, the two
bracketings of a triple act identically on every distance, because `act_mul`
makes `act` a homomorphism into `(D → D, ∘)` and function composition is
associative. A non-associative `mul` is *unobservable* through any `Bridge`, and
`mul_assoc_of_faithful` shows a faithful action forces `mul` associative outright
— you cannot even *construct* a witnessing instance (the `act_mul` obligation
would be unprovable). So non-associativity is not a place a counterexample can
live. (This corrects an earlier framing here that paired "non-associative" with
"non-functorial" as if both were available; only the latter is.)

`mul_assoc_of_faithful` is the strongest result here: not "we tried instances and
they fit" but **faithfulness forces associativity** — the headline characterization,
the transport-side `simA3_iff_respectsCoarsening`.

**So the boundary is non-*factorization*, and it lives in the certificate, not the
phenomenon.** The located non-example is `summary_not_composable`: a lossy summary
of a composable invariant that admits no `mul`. The `(ε,δ)`-DP case is exactly
this, one level up. So the transport `Rbad` is *not* empty — but what fills it is a
**lossy summary**, not a phenomenon outside the interface; the invariant always
fits. A phenomenon with **no** composable invariant at all (not even f-DP-style)
would be the stronger object, and **none is proved here** — the obstruction is real
(anything with a genuine per-map contraction bound composes soundly,
`L_{f∘g} ≤ L_f · L_g`), so an escapee must lack a per-map bound entirely, at which
point it is arguably not contraction-transport. *That* slot stays empty, with
non-associativity *proved* empty rather than merely unsearched. The honest claim
stays the one the top-level README makes: a common interface that several
independent theorems instantiate — earned by instances, not by naming.
