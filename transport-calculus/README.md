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
It is **not** the interface's `Rbad` — the invariant (`ℕ×ℕ, +`) fits fine; the
summary was *built* outside by projecting away the structure that composes. What
it proves is sharper and more useful: it explains *why the search for an interface
`Rbad` keeps coming up empty* — every candidate so far is a lossy summary of a
phenomenon that itself factors, and lossiness is **optional**. When a summary does
not compose, the fix is "don't summarize," not "the interface failed."

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

**The headline: factorization is *forced*, via a universal instance — the
transport Cayley theorem.** The monotone self-maps of `D` under composition form a
`GradedAction` (`universalGA`, `act_mul` definitional), and **every** `GradedAction`'s
`act` is a monoid homomorphism into it (`repr`, `repr_mul`). So the certificates of
any instance are a *representation* of monotone-self-map monoids, and the two prior
results fall out as standard facts about a representation:

- `act_assoc` = the representation lands in an associative monoid (`∘`);
- `mul_assoc_of_faithful` = a *faithful* representation is injective (Cayley).

And `Bridge.ofModulus`: any map carrying a monotone `D`-bound on its distance
effect is a `Bridge` in `universalGA`. The modulus of continuity is such a bound by
construction, so **every monotone-bounded contraction-transport phenomenon factors**
— the interface's `Rbad` is empty *as a theorem on this class*, not as a search
result. (`universalGA` and `Bridge.ofModulus` are **axiom-free**; `repr_mul` uses
only `Quot.sound`.)

**The non-monotone frontier: case (a) is now a theorem.** A map factors iff it has
a *monotone* dominator, and the canonical one is the modulus of continuity
`ω_f(t) = ⨆ {dist(fx,fy) : dist x y ≤ t}` — monotone and dominating *whenever the
sup exists*. So the whole question collapses to: does `D` have the suprema?
`factors_of_completeness` (**axiom-free**) settles it for complete lattices: if `D`
has `sSup` with the two universal laws, `ω_f` always exists and **every** map
factors. `ℝ≥0∞`, `ℕ∞`, every standard extended-metric codomain *is* a complete
lattice — so the non-monotone escapee **cannot live in any standard metric space**;
there the frontier dissolves into Cayley outright.

**Case (b) is inhabited — the `Rbad` is no longer empty.** `escapee_no_monotone_dominator`
(`propext` only) exhibits a map `fP` over a 3-element distance `D3` (`dB ≤ dP`,
with `dP`, `dQ` incomparable and **no common upper bound**) that has a sound
non-monotone bound yet **no monotone dominator** — so it is a `Bridge` in *no*
`GradedAction` (`escapee_not_in_universalGA`). The obstruction is exactly the
missing join: `fP` expands the `dB`-pair to `dP` and the `dP`-pair to `dQ`, and
`dB ≤ dP` forces `φ dP ≥ dP ∧ φ dP ≥ dQ`, which `D3` forbids. So the transport
`Rbad` is *genuinely inhabited*, finitely, no exotic infinitary `D` needed.

**But the witness locates the boundary precisely, and it is honest about it.**
`D3` is not a distance *monoid*: a positively-ordered monoid gives `dP`, `dQ` the
common upper bound `dP + dQ`, restoring directedness and killing this (finite)
obstruction. So the escapee inhabits the interface **as formalized** — where `D`
is only a preorder — and pinpoints the missing hypothesis: **directedness** (which
a genuine `+`-distance supplies for free). The map of the three branches is now
exact:

- **(a) proved** — over any *complete lattice* `D`, every map factors
  (`factors_of_completeness`).
- **(b) inhabited** — over a *non-directed* preorder `D`, an escapee exists
  (`escapee_no_monotone_dominator`).
- **(c) the live residual** — does *directedness* (a `+`-distance monoid, which
  gives finite joins but not down-set suprema) force factorization, or does an
  *infinite* obstruction survive it? `D3` shows finite ones die under directedness;
  the infinite case is open. This is the sharp question the whole frontier reduces
  to, and the one genuinely-open object of the transport line.

So the interface's reach is now bracketed from both sides: complete-lattice `D` ⇒
always factors; non-directed `D` ⇒ can fail; the boundary runs through
*directedness*, and where exactly is the open frontier.

**Strengthening the interface — require a directed distance.** A `Directed D le`
is a chosen common upper bound `cub a b` for any two elements; a positively-ordered
monoid supplies it for free (`cub a b := a + b`, with `a, b ≤ a + b`), so every
genuine `+`-distance is directed. The strengthening does exactly what was asked:

- **It excludes the escapee by fiat** — `no_directed_on_D3` (`propext` only):
  `(D3, le3)` admits *no* `Directed` structure, since `cub dP dQ` would be the
  common upper bound `no_common_ub` forbids. The `(b)` witness cannot instantiate
  a directed interface.
- **It buys factorization for bounded maps** — `factors_of_global_bound`
  (axiom-free): a single global upper bound `T` on all output distances makes the
  map factor via the *constant* modulus `φ ≡ T`. A directed `D` supplies such a
  `T` whenever the output range is finite (iterated `cub`). The escapee precisely
  lacked a global bound; directedness restores it for bounded maps.

**What directedness does *not* close — the honest residual (c).** It kills *finite*
obstructions (a single `cub`, or iterated `cub` over a finite range) but not
*down-set suprema*, which the modulus needs in general. So an **unbounded-output**
map over a **non-complete directed** `D` — bounded on each down-set but with no
global bound and no down-set sups — is not covered by `factors_of_global_bound`,
and whether such an infinite escapee exists is **open**. Single ascending chains
are safe (iterated `cub` tracks them); the danger, if any, is infinite *branching*
whose limit sup is missing. That lone question is now the entire residual of the
transport line:

- complete-lattice `D` ⇒ factors (`factors_of_completeness`);
- directed `D` + bounded output ⇒ factors (`factors_of_global_bound`);
- non-directed `D` ⇒ escapee (`escapee_no_monotone_dominator`);
- directed `D` + unbounded output, `D` incomplete ⇒ **open**.

The interface, strengthened to a directed distance, has no known escapee; the only
gap between it and a full completeness theorem is the infinite-branching case over
an incomplete directed `D`.

**The right hypothesis is image-family sups, not completeness (c-i, proved).**
`ofModulus` never needed *all* suprema. It needs only that each **image-family** —
the image distances over a down-set of `t` — has a *least upper bound*.
`factors_of_image_sups` (**axiom-free**) proves factorization from exactly that,
with leastness alone supplying the modulus's monotonicity. It **subsumes** both
earlier theorems: a complete lattice gives every image-family a sup, and a global
bound is the constant image-sup. So the sharpest factorization theorem is now
"the distance is directed-complete *on image-families*," and complete-lattice /
bounded-output are its corollaries — the same way Cayley made the two associativity
results corollaries.

**But the escapee needs missing *joins*, not missing *sups* (c-ii, refuted).** The
tempting witness — the rationals bounded by an irrational cut (directed, non-dcpo)
— is **not** an escapee: in a total order you *overshoot* the missing sup, e.g.
`φ(t) = ⌈h(t)⌉` is a monotone rational dominator. Non-dcpo is *not sufficient*. What
made `D3` escape was a missing **join** — `dP`, `dQ` incomparable, *no common upper
bound to overshoot to* — a partial-order phenomenon, and directedness is exactly
what kills the finite version. So the escapee needs an image-family whose cub-closure
is directed and bounded yet has **no sup and no monotone overshoot**, sustained
*infinitely under directedness*. That is strictly stronger than "non-dcpo," and the
rationals cannot carry it.

**So the residual is sharper — and more open — than a four-row table.** I have no
escapee witness even as a *preorder* under directedness (the rationals candidate is
refuted, not "almost certainly works"), let alone as a `+`-monoid. The line's last
question is exact: **can a directed order — still more, a genuine positively-ordered
`+`-distance monoid — carry an infinite image-family with no monotone upper-bound
selection, or does the algebra of `+` force the completeness the modulus needs?**
Directedness was the finite shadow; the real hypothesis is image-family sups; and
whether `+` entails them over its own order is the one place on this line where I
have neither a proof nor a witness.
