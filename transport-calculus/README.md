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
- **Markov-kernel / Dobrushin (`M = ℝ≥0`, `D` = TV) — built, finite AND measure-theoretic.**
  mathlib has no data-processing inequality, so it is proved from scratch in
  `transport-kernel/`: `dpi` (finite state spaces, coupling/overlap argument),
  `tvDist_comp_le` (arbitrary measurable spaces, Hahn decomposition + additive coupling),
  `Bridge.ofKernel` / `Bridge.ofMarkovKernel` (kernels are certified bridges),
  `comp_reconstructs_dobrushin` / `comp_reconstructs_dobrushin_measure` (advanced
  composition = certificate accumulation), and the discretization consistency lemma
  (`tvDist_toMeasure`, `dpi_via_measure`: the two developments provably agree, the finite
  DPI a corollary of the measure one). Axiom-clean, no `sorry`.

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

**Tried to build the monoid escapee — the finite half is closed, the infinite half
resisted.** `directed_finite_factors` (`propext` only) proves that if the output
distances are *finite* (all in `seed :: L`), a directed distance factors — fold
`cub` over the list into a global bound, no completeness needed. So **no finite
obstruction escapes a directed distance**: the monoid's `cub` (its `+`) defeats
every one. That kills the whole finite half of the frontier, and it kills it with
directedness *alone*.

The infinite half I could **not** build, and could not close either — every
avenue collapsed:

- a single ascending chain of inputs → iterated `cub` tracks it (increasing `φ`);
- finite branching → one `cub` per branch resolves it;
- a bounded infinite image-family → it has an upper bound (contraction), so the
  *constant* modulus at that bound dominates (`factors_of_global_bound`);
- unbounded output over an ascending chain → not contraction, excluded.

An escapee would need infinite *branching* whose limit join is missing **and**
unovershootable — the `D3` mechanism (missing join, not missing sup) sustained
infinitely under directedness. I have no such witness, and no proof it is
impossible. So the honest state of the transport line is: **factorization ⟺
image-family sups (proved); complete-lattice, bounded-output, directed-finite all
factor (proved); the finite escapee needs non-directedness (proved, `D3`); and the
sole open question is whether a positively-ordered `+`-monoid can carry an
infinite missing-join image-family — the point where the algebra of distances
might, or might not, force the order-completeness the modulus needs.** First
question in the whole arc with neither proof nor counterexample, now with its
finite neighbourhood entirely closed off around it.

**Tried to prove "positive monoid forces factorization" — cannot, and here is the
honest reason (not a hedge).** In attempting it, the frontier's framing corrected
itself: the `D3` escapee is **unbounded** (`escapee_unbounded`) — `dP`, `dQ` are
output distances with no common upper bound, so its image-family has *no* upper
bound and `fP` is not bounded-distortion at all. It is the trivial *non-contraction*
case. So what excluded it from a directed distance was never directedness; it was
**boundedness**. The operative hypothesis is that image-families are bounded — and
the clean sufficient condition for factoring is **dcpo** (directed *and*
directed-complete): then an image-family's `cub`-closure is directed, has a sup,
and that sup is the monotone modulus — precisely `factors_of_image_sups` with the
sups supplied.

A positive monoid gives **directed** (via `+`) but **not** directed-*complete*:
`+` builds finite joins, not the suprema of infinite directed sets. So
directedness / `+` **does not** force factorization; the hypothesis that does is
dcpo, which a monoid need not satisfy. I could neither close the gap (prove that
the specific structure of image-families rescues a non-dcpo monoid) nor inhabit it
(build a *bounded* escapee — every avenue resolves via a constant bound or iterated
`cub`, yet no general proof follows). So the claim "positive monoid forces
factorization" is one I **cannot prove**, and will not assert. The proved
characterization stands: **factorization ⟸ image-family sups** (`factors_of_image_sups`),
with dcpo the clean order-theoretic hypothesis supplying them — and whether a
positive monoid, lacking dcpo, nonetheless always factors on *image-families
specifically* is the genuine open problem, with neither proof nor witness. The
honest ceiling of the transport line is: dcpo forces it; `+` alone does not; the
gap between them is open.

**Directed ⇏ dcpo, mechanized — and not-dcpo is still not an escapee.** `Dm` is a
mathlib-free directed order (`⊤` bounds everything, so `cub ≡ ⊤` gives `Directed`,
`dirM`) whose chain `fin 0 ≤ fin 1 ≤ ⋯` is directed and bounded yet has **no least
upper bound** (`Dm_chain_no_sup`: `L`, `R` are incomparable minimal ubs). So
directedness — what a `+`-monoid supplies — is *strictly weaker* than the dcpo
that factorization's clean hypothesis needs. `ℚ≥0` under `+` is the standard
monoid witness of the same fact. **But `Dm` still factors** (`Dm_factors`): `⊤`
overshoots every family. So *not-dcpo is necessary but not sufficient for an
escapee* — the missing sup here is overshootable, exactly as the totally-ordered
`ℚ≥0` gap is.

**The *greedy* overshoot does not close — but it mislocated why.** The reduction
"directed + bounded ⇒ a monotone *overshooting* selection" fails as a **greedy**
construction: assigning `φ(t)` an ub of `S(t)` dominating `{φ(s) : s ≤ t}`
accumulates, and each `φ(s)` — *some* ub of `S(s)`, possibly far above the later
bound of `S(t)` — can blow the accumulation up, with the future bound unknowable
when the earlier choice is made. Controlling it that way requires `φ(s)` = *least*
ub = sup, i.e. dcpo. But this is an obstruction to *greedy accumulation*, not to
overshooting as such. Replace the running accumulation with a **fixed external
scale** and it dissolves — which is exactly what closes the `ℚ≥0` case below.

**Image-family sups are not even necessary (`image_sups_not_necessary`, proved).**
Over `Dm` — directed, not-dcpo — the identity map under `distMax a b = fin (max a b)`
factors (through the `⊤` overshoot), yet the `factors_of_image_sups` hypothesis is
*unsatisfiable*: at threshold `L` its image-family is the whole sup-less chain
`{fin n}`, whose least upper bound does not exist. The least-ub modulus the theorem
demands provably does not exist here, and the map factors anyway. So image-family
sups are the *canonical* sufficient condition, now witnessed **non-minimal** — a
non-least dominator does the entire job.

**The fixed-scale overshoot that closes `ℚ≥0` — a cofinal ℕ-ruler
(`ruler_defeats_bounded_escapee`, proved).** The scale greedy accumulation lacked is
a monotone **cofinal ℕ-ruler** `k : ℕ → D` (`Ruler`): a coarse countable skeleton
with every element below some `k n`. Given one, send each threshold `t` to
`k (least n whose ruler value bounds the family at t)` — leastness makes the index
monotone (larger down-set ⟹ superset ⟹ least bounding index not smaller), cofinality
makes it dominate. Nothing accumulates (the scale is fixed, not running), no sups, no
dcpo. So **every bounded-image map over a ruler-carrying distance factors** — and
`ℚ≥0` carries such a ruler (`k n = n`, cofinal by Archimedean-ness) while having a
*bounded family with no sup* (the `√2` gap). The `ℚ≥0` escapee the frontier feared
**cannot exist**. (The least-witness search is mathlib-free — Lean core has no
`Nat.find` — and `exists_least` is *choice-free* (`propext`/`Quot.sound`): the search
*is* the monotone selection dcpo was standing in for. The full theorem uses
`Classical.choice` only to select the per-threshold least index.)

**The honest framing is *incomparable*, not "dcpo dethroned."** A cofinal ω-ruler and
directed-completeness are **two incomparable sufficient conditions**: `ℚ≥0` has the
ruler and not dcpo; an uncountable dcpo has completeness and no ω-ruler. dcpo is *not*
necessary for ruler-carrying distances. And the ruler hypothesis is milder than it
first appears — which shrinks the residual sharply.

**The residual is not "rulerless" — it is *singular cofinality*
(`countable_cofinal_factors`, `Ruler.ofCofinalSeq`).** Directedness makes the ruler's
monotonicity *free*: any cofinal ℕ-**sequence** `c` — no order on it assumed — becomes a
monotone ruler by running the directed `cub` through it (`cofChain`, `Ruler.ofCofinalSeq`,
**axiom-free**). So the operative hypothesis is not "monotone cofinal chain" but plain
**countable cofinality**, and `countable_cofinal_factors` factors every bounded-image map
from a bare cofinal sequence — `ℚ≥0` qualifies via `ℕ ↪ ℚ≥0`, no Archimedean rounding done
by hand. **But this is specific to `ω`, and does not generalize for free** — the
transfinite analogue is an *open proof with a real hypothesis gap*, not a formalization
deferral. Monotonizing a cofinal ℕ-sequence uses only **finite** joins, exactly what
directedness supplies (`cofChain` is a finite `cub`-fold). To run the same selection along a
cofinal `κ`-chain for uncountable `κ`, the limit step needs *upper bounds of `<κ`-sized
prefixes* — i.e. **`κ`-directedness** (every subset of size `<κ` is bounded). Regular
cofinality does **not** give this: a `<κ`-sized subset is non-cofinal, but *non-cofinal ≠
bounded* in a merely directed order (`ℕ` is directed yet unbounded). So "regular cofinality ⇒
factors" has a hole at exactly that step; the hypothesis the argument really needs is
`κ`-directedness, strictly stronger — and under it the transfinite selection was first called
"only plausible — unchecked, and unformalizable here", which the next paragraph corrects:
it is now *proved*, in this file.

So the honest residual is the **whole uncountable-cofinality** directed non-dcpo realm — not
the smaller "singular cofinality" (an earlier overstatement of mine), since even the
regular-uncountable case is open absent `κ`-directedness. It has **neither a witness nor an
impossibility proof**.

**The transfinite theorem, formalized — "unformalizable" was wrong
(`prefix_bounded_cofinal_factors`, proved).** Neither cardinals nor — for half the argument —
transfinite recursion was actually needed, and the mistake was load-bearing for how open the
residual looked. Split the ω-argument in two and each half generalizes, mathlib-free:

- **Selection is not transfinite** (`wruler_defeats_bounded_escapee`, `Classical.choice`
  only). Over *any* well-ordered index — `WellIndex`, an order with a least witness for every
  inhabited predicate, `ℕ`'s `exists_least` abstracted — a monotone cofinal chain defeats
  every bounded-image escapee by the same per-threshold least-index selection as at `ω`.
  **No limit steps exist in this argument at all**; what looked transfinite never was.
- **Monotonization is where recursion lives** (`WRuler.ofCofinalFamily`): turning a bare
  cofinal `W`-family into a monotone chain runs `WellFounded.fix` (Lean core;
  well-foundedness derived from least witnesses, `WellIndex.wf`) under the real hypothesis:
  **`PrefixBounded`** — every family indexed by an initial segment `{v // v ≤ w}` is bounded.
  That is `κ`-directedness stated *without cardinals*, and weakened to segment-indexed
  families — sharper than what the prose version asked for.
- `prefixBounded_of_directed` proves plain directedness supplies `PrefixBounded` at `W = ℕ`
  (segments are finite; `cub`-folds bound them) — "κ-directedness is free at ω" as a theorem
  — and `countable_cofinal_factors'` re-derives the whole countable case from the general
  machinery, confirming the subsumption end-to-end.

**The residual, restated at its true width: one hypothesis.** `PrefixBounded ⇒ factors` is
proved at every cofinality; `Directed ⇒ PrefixBounded` is proved at `ω` and is *not* a theorem
uncountably (finite `cub`-folds cannot bound infinite segments). The open question is whether
that gap is **inhabited**: can a directed-only distance of uncountable cofinality defeat every
monotone selection, or does some further structure always close the gap? Neither witness nor
impossibility proof — but the frontier is no longer "the whole uncountable realm"; it is
exactly the strip between `Directed` and `PrefixBounded`.

**The hunt — candidates die informatively, and the strip narrows from both walls.** The
natural first candidates all factor: `ω₁ × ℕ` (directed, not σ-directed, uncountable
cofinality, *no* cofinal chain) has coordinatewise bounded-family sups, so
`factors_of_image_sups` kills it; ideal-of-sets orders die by unions; chain-shaped designs
die by automatic prefix-boundedness and self-domination; gap encodings pointed at the
shrinking side die because dominator constraints are *lower* constraints only — nothing can
force `φ` under the top side of a Hausdorff gap. Two of the deaths are theorems now:

- **Wall one moved up (`sigma_directed_cofinal_factors`).** σ-directedness (`SigmaDirected`
  — every ℕ-family bounded) supplies `PrefixBounded` along any cofinal well-ordered family
  with countable segments (`CountableSegments` — the cardinal-free "ω₁-like").
  Contrapositive: an escapee carrying an ω₁-like cofinal family must contain a *countable
  unbounded family* while staying pairwise-directed.
- **Wall two holds (`lists_not_sigma_directed`, `lists_bounded_factors`).** Failing
  σ-directedness is not sufficient: `List Nat` under membership-inclusion is directed
  (append), provably not σ-directed (singletons `[n]` have no common bound — lists are
  finite), yet every bounded-image map factors: filter the bounding list down to the
  family's members and you have a *least* upper bound. Conditional completeness, not
  σ-directedness, is what an escapee must break.

**The quarry's profile.** It must (1) fail σ-directedness, (2) fail conditional completeness
on bounded image-families *unovershootably* (total-order gaps overshoot — the `ℚ≥0` lesson),
and (3) fail only globally: every finite subsystem is satisfiable
(`directed_finite_factors`) and every principal down-set is satisfied by a constant (that is
the `bounded` hypothesis itself) — an Aronszajn-style "all levels nonempty, no branch"
shape. Coherent sequences and gaps are the known ZFC engines of that shape, and their
selection problems are notoriously axiom-sensitive — so the escapee's existence may be
**independent of ZFC**, not merely open. No capture; two walls proved; the profile now
points at genuine set-theoretic combinatorics.

**The coherent-sequence encoding — the profile is realizable, up to a set-theory question.**
For a coherent sequence `⟨e_α : α < ω₁⟩` (`e_α : α → ω`, `e_α =* e_β↾α`; nontrivial ones
exist in ZFC by Todorcevic's walks), the **fiber order**
`D_coh(e) := Σ_α {s : α → ω ∣ s =* e_α}`, ordered *pointwise* on the smaller domain, is —
on paper, since ω₁ is not formalizable mathlib-free —

- **directed with finite joins**: pointwise max stays in the fiber, because coherence keeps
  deviations finite;
- **not σ-directed**: spikes to `e_{α*}(ξ_n) + n` at points `ξ_n → α*` defeat every bound,
  since coherence forces any bound to agree with `e_{α*}` cofinitely;
- **incomplete in the join sense**: a bounded family whose pointwise sup dips below the
  floor infinitely has upper bounds but **no minimal upper bound** — every bound can dip at
  one more coordinate. The `D3` missing-join mechanism, sustained infinitely under
  directedness — the first structure found that passes every wall.

Whether an escapee actually lives on it reduces to a **uniformization question**: the
canonical overshoot dominator is monotone except at coherence defects, and repairing them
globally means choosing fiber representatives pointwise-monotonically in the level — but
*level-monotone bounded coherent sequences are trivial* (per-coordinate values stabilize;
coherence turns the stable function into a trivialization — provable on paper). Over a
nontrivial sequence the canonical dominator is genuinely obstructed; whether some
non-canonical one always exists is a coherent-sequence uniformization principle, exactly
the class of statement that MA and ◊ split. The design space is pinned by a **two-order
tension**: mod-finite fibers make the requirement chain self-dominate by coherence;
pointwise fibers make raw `e`-requirements slice-unbounded; every viable design lives in
the finite-modification freedom between the two.

**The ◊-side attempt (see `NOTES-coherent-escapee.md`) — and its ZFC collapse: canonical
dominators die over every nontrivial sequence.** Working the diamond construction produced
two ZFC lemmas — *level-preserving systems always factor* (`φ(t) := t ∨ sup S(t)`), and
*representative systems (level-monotone fiber representatives) make every legal system
factor* — plus a ◊ theorem building a coherent sequence with no reps. Then checking
whether the walk sequences already lack reps in ZFC **retired the ◊ machinery entirely**:

> **Theorem (ZFC): a coherent sequence admits a representative system iff it is trivial.**

The proof's engine: coherence transfers to any rep system and pins pairwise differences
finite; level-monotonicity then concentrates countably many movement-witnesses at a single
countable level, so only finitely many coordinates below any `α` ever move after `α`; the
escape set therefore has finite initial segments, hence is bounded; and bounded escape
stabilizes into a trivializing function. Corollary: **canonical dominators exist iff the
sequence is trivial — a ZFC dichotomy**, with the walks' `ρ₁` a concrete rep-less witness.
The independence suspicion retreats accordingly: whatever axiom-sensitivity remains lives
only in *non-canonical* (dip-assembled) dominators. What still did not close is the bridge
from rep-death to an actual escapee — pressure needs infinite boundable threshold
families, legality makes their requirements mod-finite-satisfiable, fibers absorb finite
defects, and every coherence-extraction from a dominator needs exactly a rep chain. The
open core, now a pure ZFC question: **does "every legal system over `D_coh(ρ₁)` factors"
imply triviality?** If yes, the transport escapee exists in ZFC. The legal pressure system
`Σ_succ` and the decisive follow-ups are in the note.

**The dip-side attempt (note §6) — a correction, a chain-freeness theorem, and a flipped
verdict.** Attempting the dip-side argument corrected the record twice and settled the
direction of evidence. First, `Σ_succ` *factors* — the uniform one-level shift
`φ((α,s)) := (α+1, (s∨1)⌢⟨1⟩)` is a dominator, so the "pressure system" exerted none; real
pressure needs limit-level raising, and there the limit-push system is legal exactly over
*block-tame* sequences, whose tameness hands the block-diagonal dominator its
monotonicity — the absorption pattern, for the fourth time: **whatever coherence makes a
system legal builds its dominator.** Second, a new ZFC theorem: **`D_coh(e)` contains an
ω₁-chain with cofinal levels iff `e` is trivial** — a chain is a club-indexed rep system
and the reps proof runs verbatim. So over nontrivial sequences the fiber order is provably
chain-free (Aronszajn-type as an order), which retroactively explains every failed
chain-mediated kill and extraction at once. Third, the kill-side analysis closes into a
circle at every entry point: dominator correction budgets are per-*element* (not
per-level), each level has infinitely many elements, greedy assembly accumulates only at
countable unions, and stage-wise floor sabotage makes the pressuring slices illegal at the
same stroke. **Verdict flipped: the evidence now favors ZFC-factoring** — plausibly every
legal system over every coherent sequence has a dominator, and the escapee, if it exists,
needs a different species of directed order. The one missing lemma for a proof: global
coordination of per-element finite gap-fill corrections — a transfinite amalgamation
question with no surviving obstruction, chain-freeness having removed the known one.

**The coordination lemma attempted (note §7) — the residue isolated; the verdict
oscillates back.** The direct attempt yields: a recursion along an ω₁-enumeration
refining `⊑` with a finite-ledger invariant; a ZFC lemma that *requirement*-excess
inherits uniformly (all past `M`-contributions land in the single finite set `F_u`) — the
wall was never the requirements; and the exact residue: past floor values baked into gap
regions, `∪_{t ∈ ↓u} (D⁺(μ_t, γ_u) \ X_t)`, with level-overshoot provably useless (high
floors are pairwise =*-equivalent) and dips committed once against moving targets. The
sufficient condition is named — a **uniformizing dip system** `{X_μ}` with
`∪_{μ<γ}(D⁺(μ,γ) \ X_μ)` finite for all `γ` — which trivial sequences have, and which
almost-extracts a representative system (`H_γ := sup(e_μ off X_μ)`; one fiber-control gap
remains). The Bridge is now squeezed between "per-`u` finite absorption" (necessary for a
dominator) and "uniform dips" (sufficient), one **Fodor step** and one extraction repair
apart: if both close, dominator ⇒ trivial and **the escapee exists in ZFC**, reversing
the previous lean; if either fails, the failure should exhibit the dip-assembly that
factors everything. Narrowest state the question has reached.

**The Fodor step attempted (note §8) — the circle proves itself; the core goes
Aronszajn; third flip, toward independence.** Pressing down is sound but its input is
unobtainable: probe systems forcing cofinal floor-pressure are legal *iff* sup-coherence
already holds — the circle is now an equivalence. Three ZFC lemmas fell out: single-target
dips are free; bounded families are never obstructions (their dips uniformize against all
targets); and the **chain-continuation lemma** — dips against a chain's own sup serve
every continuation (`D⁺(μ_n,γ) \ D⁺(μ_n,δ*) ⊆ D⁺(δ*,γ)`, one finite set) — the moving
target is fake for single chains. But the reduction is self-similar (per-element targets
reproduce sup-coherence at the target level; club-valued targets die over the ◊-sequence,
whose kill-set is stationary), and §7's "level-overshoot is useless" is corrected:
overshooting past kill-points parks values on the post-kill low floor, so a dominator is
in total a `D`-indexed rep-like selection — and the reps kill needs ω₁-chains in the
index, which chain-freeness forbids. Both directions thus lose their closing weapon at
the last step. The hard core, isolated: *a monotone fiber-valued selection with
pairwise-finite deviations on the chain-free order itself* — an Aronszajn-type
uniformization, the exact family where ◊ kills and MA/PFA saves. Current lean, third
revision: **independent of ZFC**, with one named gap per side (◊: make the dominator need
the killed coordinates despite overshoot; MA: tame the self-similar ledger).

**The ◊-side gap attempted (note §9) — a no-go theorem; fourth flip.** The attempt closed
the ◊ route instead of the gap. Single-level kills are structurally *thin* (coherence
forces it: finite below every lower level, inherited by every higher floor), so they never
accumulate; staggered kills would make two fixed levels differ infinitely — impossible;
committed-value forcing needs img-families cofinal in the kill stage, which legality
forbids (unbounded slices), marker-isolation blocks (infinitely many markers is not a
fiber element), and delayed-level construction cannot reach (coherence caps late
deviations at finite). The template no-go in three lines: **legal forcing is
bounded-family forcing; bounded families are absorbable; kills need unabsorbable
forcing** — covering all five kill designs attempted across the notes. First genuinely
one-sided evidence in the arc. Current lean, fourth revision: **ZFC-factoring**, with the
MA-side amalgamation now read as a candidate ZFC proof and its missing piece named
(*forcing-locality*: every cross-element floor-inversion accumulation traces back to some
slice's forcing — if true, "legality ⇒ absorbability ⇒ dominator" becomes a theorem and
the fiber-order residual is empty in ZFC).

**Forcing-locality proved; the Bridge becomes a game on `e` alone (note §10).**
Forcing-locality holds: the one pattern the no-go missed (the *anti-kill* — floors raised
above their ladders at cofinally many points, forcing values high by fiberhood rather
than requirements) breaks nothing, since forced highs hurt only where higher floors are
low, and raised-then-killed on one infinite set contradicts pairwise coherence. So
nothing legal ever forces values above the eventual floors. With that, systems and
dominators are eliminable: down-sets have ⊑-cofinal ω-chains, requirement-sups are
legality-bounded, and the only surviving obstruction is *floor-baking along chains* —
finite per pair, fractally self-similar across overlapping chains. The whole Bridge
reduces to a two-quantifier combinatorial game `G(e)`: adversary plays a monotone
level-assignment `μ`; dominator plays a schedule `γ ≥ μ` with finite dip-sets; dominator
wins iff every down-set's leftover union is finite. **Factors-everything(`e`) ⟺
dip-schedulable(`e`)** (both directions argued), and the entire seven-session hunt ends
at one line: **is every dip-schedulable coherent sequence trivial?** — a self-contained
uniformization invariant of coherent sequences, handed to set theory in final form.

**The problem statement for set theorists: `PROBLEM-dip-schedulability.md`.** Fully
self-contained (no transport calculus needed): definitions, the game, the implication
diagram `trivial ⟹ strong-schedulable ⟹ Φ ⟹ weak-schedulable` with rigor grading on
every arrow, four numbered questions (the main one; the realizability/fractal gap; the
◊-sequence and walks instances; the MA/PFA consistency route with the schedule-forcing's
ccc-ness as the crux), a toolbox of four proved ZFC lemmas with proofs
(chain-continuation, single-target, representative systems ⟺ trivial, chain-freeness of
the fiber order), the thinness remark explaining why naive ◊-attacks fail, and the
independence-boundary discussion. Questions 1–4 are pure ω₁ combinatorics.

**The reps theorem, machine-checked in shadow (`reps_implies_trivial`).** The
set-theoretic hunt's four-step engine is now formalized: over an abstract index carrying
exactly the three properties of ω₁ the proof uses — least witnesses (`WellIndex`),
σ-directedness (`SigmaDirected`, where regularity enters), countable segments
(`CountableSegments`) — a coherent sequence (`CoherentSeq`, finiteness as
list-coverage) admitting a level-monotone representative system (`Reps`) is trivial.
Axioms: `propext, Classical.choice, Quot.sound`; no `sorry`; supporting lemmas include a
mathlib-free pigeonhole (`no_injection_into_list`) and totality-from-least-witnesses
(`WellIndex.total`, axiom-free). Honesty about instances, per house style: the intended
model (ω₁) is not constructible here, and the pairing makes the hypotheses demonstrably
load-bearing — `nat_not_sigma_directed` shows ℕ fails σ-directedness, and
`omega_concentration_fails` shows the concentration step (the proof's heart) genuinely
fails at index ℕ: the coherent, level-monotone family `χ_{<n}` moves at every
coordinate. The shadow theorem is exactly why the argument works at ω₁ and not below.

**Theorem A and Lemma F, machine-checked (`thmA_schedulable`, `lemmaF_below_finite`).**
Two proved pillars of the dip-schedulability development (problem statement §1) are
index-agnostic and now formalized over the same `CoherentSeq` abstraction, in the
`DipSchedule` section: **Theorem A** — a trivial coherent sequence is strongly
schedulable, because the canonical trivialization dips route every surviving upward
defect (`upDefect`) at a top `t` into the single finite set where the global row
disagrees with row `t` (`thmA_leftover_subset`, then finiteness by `FiniteP.mono`); and
**Lemma F** — below an element's own level the fiber inequality `s_x ≤ s_u` transfers
through the floors, so the below-level leftover is covered by the two finite
fiber-deviation sets (`lemmaF_below_subset`/`lemmaF_below_finite`, the latter choice-free:
axioms `propext, Quot.sound`). These are exactly the results the contested open heart
(Question 5) rests on; machine-checking them hardens the proved skeleton while the heart
stays open. Axioms otherwise the standard `propext, Classical.choice, Quot.sound`; no
`sorry`.

**Theorem I forward, machine-checked and axiom-free (`EscapeeTheory` section).** The
escapee framework of notes §38: `Phi O` — *every legal constraint system on a directed
order has a monotone dominator* (its negation is the transport escapee) — follows from a
**monotone dominating retraction** of the constraint sets (`phi_of_domRetraction`,
**Theorem I forward**). The three sufficient routes are its instances: the top route
(`phi_of_top`, `Dm`'s `⊤`-overshoot) and the bounded-complete route (`phi_of_join`,
Theorem H / the join). All three are formalized abstractly (`DirOrder`, `LegalSystem`,
`Dominator`, `DomRetraction`) and **depend on no axioms whatsoever** — pure constructive
order theory. The converse (`Phi ⟹` retraction, notes §39) is an open uniformization and
is deliberately not formalized; what is machine-checked is exactly the proved,
one-directional core.

**The forcing bridge, machine-checked (`phi_of_generic`).** The PFA side of the escapee
independence goes through the realization poset `P(Σ)` (notes §25–§26): proving `P(Σ)`
*proper* is the open checkpoint and is **not** formalized (there is no proof). What is
proved and machine-checked is the *bridge* — a `GenericDom`, the covering, cross-monotone
family of partial dominators that a proper poset's generic filter provides, yields `Φ`
(`phi_of_generic`, axioms `Classical.choice`). This isolates the open part (existence of
the generic family = properness + forcing axiom) as the single structure hypothesis and
verifies everything downstream, so the PFA-side reduction is machine-checked *modulo* the
one honestly-open forcing step.

**The single-element ccc, machine-checked (ZFC) — the exact boundary.** Compatibility of
two conditions reduces exactly to cross-monotonicity (`PartialDom.compat_of_crossMono`,
machine-checked). For **single-element** conditions this is a ZFC theorem:
incomparable-domain conditions are compatible (`singletonDom_compat_of_incomp`), so a
pairwise-incompatible family of single-element conditions has pairwise-comparable domains —
a chain (`singleton_antichain_is_chain`). A nontrivial coherent sequence's fiber order has
no uncountable chain (`Lemma D`, the one cardinality fact left in prose), so the
single-element poset is ccc. This is *precisely* where ZFC stops: single-element conditions
are ccc for free, but the **multi-element** case is where cross-defects conspire, and that
is the axiom-dependent core (notes §40) whose proof is Todorcevic's oscillation lemma — not
formalized, because it is *not* a ZFC theorem (it fails under CH, which is the escapee). All
`Classical`-only or axiom-standard; no `sorry`.

**The fiber-control gap closes — Theorem B, and Question 1′ proved (note §11).** The §7
`H`-route is refuted by a counterexample (wasteful dips hide whole columns below an
ω-cofinality level), and the theorem is proved by the *honest-column* extraction instead:
values are monotone along honest levels, never-honest points are finite per level
automatically, unbounded columns die by witness-concentration, and the max honest value
trivializes. **A coherent sequence admits a uniformizing dip system iff it is trivial**
(ZFC, relativizes to cofinal level sets), and hence **level-factored strong
schedulability implies triviality** — a proved partial answer to the problem statement's
Question 1, whose open content is now exactly element-dependent schedules. Also landed:
`tools/check-claims.sh`, a drift guard for README/status claims.

**The formalizable shadow (`Fb`): profile item (2) is individually non-lethal.** The dip
pathology has a countable, mathlib-free witness: levels `ℕ ∪ {∞}` over a constant-`1` floor
with finite patches. `Fb` is directed (`dirF`), not σ-directed (`fb_not_sigma_directed`),
and carries a bounded family with **no minimal upper bound** (`fb_no_minimal_ub`, choice-free
— strictly worse than `Dm`'s two-incomparable-minimal-ubs gap), yet still factors
(`fb_factors`): an explicit ladder is a bare cofinal ℕ-sequence and the ruler machinery
overshoots every dip. So the dips alone don't kill factorization either — the quarry must
carry them at *uncountable* cofinality, where no ruler exists. That is `D_coh(e)` over a
nontrivial coherent sequence, and the question leaves this repo for set theory.

**And `ℕ` is not the shortcut it looks like.** `natRuler` (ℕ, `k = id`) proves `Ruler`
is inhabited by a genuine distance codomain — but *only* that. It is tempting to read
ℕ as the coveted "ruler-carrying, not-dcpo, factors anyway" witness, since ℕ fails
strict directed-completeness (its unbounded chain `0 ≤ 1 ≤ ⋯` has no sup). It is not:
**every *bounded* image-family in ℕ is finite, hence has a sup**, so
`factors_of_image_sups` already covers ℕ and the ruler adds nothing there. ℕ's
incompleteness lives in *unbounded* families — exactly the ones the `bounded`
hypothesis excludes. The interesting instance needs a *bounded* family with **no**
least upper bound (an order-gap), which ℕ lacks and `ℚ≥0` has — so `ℚ≥0`'s
not-dcpo-ness stays load-bearing, and stays prose (a mathlib-free `ℚ≥0` is
disproportionate). `natRuler` is non-vacuity, not the witness.

So the transport line's state, honestly: **factorization ⟸ image-family sups (proved),
but those sups are *not necessary* (`image_sups_not_necessary`); a cofinal ℕ-*sequence*
is enough (`countable_cofinal_factors`), so every directed distance of *countable*
cofinality factors — `ℚ≥0` included; and the transfinite theorem is now proved at every
cofinality (`prefix_bounded_cofinal_factors`): a cofinal well-ordered family on a
*prefix-bounded* distance factors every bounded-image map, with selection needing no limit
steps at all.** Five times the stated hypothesis — completeness, directedness,
boundedness-not-directedness, dcpo, "unformalizable transfinitely" — turned out not to be
operative or not to be true; what stands open is exactly one strip: whether `Directed`
without `PrefixBounded`, at uncountable cofinality, admits an escapee. Neither witness nor
impossibility proof — but the frontier is one hypothesis wide, with machine-checked
theorems on both of its shores.

**The quantitative centre — now built (finite case).** This whole line is *qualitative* — it
asks only whether a monotone dominator *exists*, never what it *is*. The interface was built
to host **quantitative** transport: the Dobrushin / strong-data-processing contraction of
total variation, the reason any of this connects to real contraction estimates. That instance
was the unbuilt centre, and it is now fully built in `transport-kernel/` — finite state
spaces (`dpi`, `comp_reconstructs_dobrushin`, `coeff_submul`), arbitrary measurable state
spaces (`tvDist`, `tvDist_comp_le`, `comp_reconstructs_dobrushin_measure`,
`tvDist_kernel_comp_le`), and the discretization consistency lemma joining them
(`tvDist_toMeasure`, `dpi_via_measure`). So the centre is no longer prose at any level of
generality: the interface demonstrably hosts a contraction theorem mathlib does not
contain, reproduces its composition law generically, and the finite and measure-theoretic
developments provably agree where they overlap. What remains open is only the qualitative
order-theory frontier above.
