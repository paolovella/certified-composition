# Dip-schedulability of coherent sequences — a problem statement

A self-contained combinatorial question about coherent sequences on ω₁, extracted from a
longer program in certified-composition theory (background in `NOTES-coherent-escapee.md`
in this repository; none of it is needed below). Rigor grading is explicit throughout:
**[proved]** means a complete argument at careful-prose rigor is given or cited here;
**[argued]** means derived in the notes at sketch rigor; **[open]** means open.

## 1. Definitions

Work in ZFC. Fix throughout a *coherent sequence*
`e = ⟨e_α : α < ω₁⟩`, `e_α : α → ω`, meaning: for all `α < β`,
`{ξ < α : e_α(ξ) ≠ e_β(ξ)}` is finite. Write `s =* t` for "equal off a finite set".
This is Bergfalk–Lambie-Hanson's Definition 2.10 (*The Cohomology of the Ordinals I*,
arXiv 1902.02736) with values in `ω` in place of an abelian group `A`; a ℤ-valued
trivialization of an ω-valued family is negative only on a set with finite initial
segments, hence bounded, hence patchable, so the two notions of triviality coincide
here. In their vocabulary: *trivial* is `[Φ] = 0` in `H¹(ω₁)`, and nontrivial families
exist in ZFC via the walk functions `ρ₁, ρ₂` (Todorcevic).

- `e` is **trivial** if there is `E : ω₁ → ω` with `E↾α =* e_α` for every `α`.
  Nontrivial coherent sequences exist in ZFC (Todorcevic; e.g. `e_α := ρ₁(·, α)` from
  walks).
- For `μ ≤ γ < ω₁`, the **upward defect** is
  `D⁺(μ, γ) := {ξ < μ : e_μ(ξ) > e_γ(ξ)}` — finite, by coherence.
- The **fiber order** `D(e)`: elements are pairs `x = (α, s)` with `s : α → ω`,
  `s =* e_α`; write `ℓ(x) := α`. Order: `(α, s) ⊑ (β, t)` iff `α ≤ β` and `s(ξ) ≤ t(ξ)`
  for all `ξ < α`. Basic facts **[proved]**: `D(e)` is directed with binary joins
  (pointwise max stays in the fiber, by coherence); every down-set `↓u` is countable and
  join-closed, hence has a `⊑`-cofinal ω-chain; `D(e)` contains an ω₁-chain whose levels
  are cofinal in ω₁ **iff** `e` is trivial (§4, Lemma D).

**The game.** A **pressure map** is a monotone `μ : D(e) → ω₁` with `μ(x) ≥ ℓ(x)`
(monotone: `x ⊑ y ⟹ μ(x) ≤ μ(y)`). A **schedule** for `μ` is a pair `(γ, X)` where
`γ : D(e) → ω₁` is monotone with `γ ≥ μ`, and `X : D(e) → [ω₁]^{<ω}`, such that

> for every `u ∈ D(e)`: (i) `⋃_{x ⊑ u} ( D⁺(γ(x), γ(u)) \ X(x) )` is finite, and
> (ii) `S_u(ξ) := sup{e_{γ(x)}(ξ) : x ⊑ u, ξ < γ(x), ξ ∉ X(x)}` is finite for every `ξ`
> and `≤ e_{γ(u)}(ξ)` off a finite set.

(Condition (ii) — the *value-form* — is needed for the intended application: (i) alone
bounds which coordinates leak but not the values there, and coherence permits unbounded
growth along levels at a fixed defect coordinate; see the notes, §12(b). All positive
results below prove the stronger (i)+(ii) form or need only (i); the questions are
equivalent-shaped under either reading, but (i)+(ii) is the official definition.)

- `e` is **strongly dip-schedulable** if every pressure map admits a schedule.
- `e` is **weakly dip-schedulable** if every pressure map of the form
  `μ(x) = sup{λ_p : p ∈ P, v_p ⊑ x}` for a *legal constraint family* admits a schedule —
  where a legal constraint family is a set `P` of pairs `(v_p, w_p) ∈ D(e)²` such that
  for every `u` the set `{w_p : v_p ⊑ u}` is bounded in `D(e)`, and `λ_p := ℓ(w_p)`.
  (Weak = the pressure is realizable by jointly-bounded fiber elements.)

Each per-pair set `D⁺(γ(x), γ(u))` is finite; the content of the game is whether finite
per-element corrections `X(x)`, chosen once, can absorb the *union* over every down-set
simultaneously. The order `D(e)` has no long chains when `e` is nontrivial (Lemma D), so
the union is over genuinely branching, overlapping countable directed families.

## 2. The implication diagram

```
trivial  ⟹[proved]  strongly schedulable  ⟹[proved†]  Φ(e)  ⟹[argued]  weakly schedulable
   ↑                                                    |
   └────────────────── ??? (Question 1) ────────────────┘
```

(† at careful-prose rigor, notes §12(c), for the value-form definition above.)
Here `Φ(e)` is the statement the program cares about ("every legal constraint system over
`D(e)` admits a monotone dominating selection" — the precise form is in the notes; it is
*not needed* to attack the questions below). The two horizontal **[argued]** arrows are
sketch-rigor reductions from the notes; the combinatorial questions stand on their own.

**Theorem B (uniformizing dip systems) [proved].** Call `{X_μ : μ < ω₁}` (finite
`X_μ ⊆ μ`) a *uniformizing dip system* for `e` if `U_γ := ⋃_{μ<γ}(D⁺(μ,γ) \ X_μ)` is
finite for every `γ`. Then **`e` admits a uniformizing dip system iff `e` is trivial**.
(⟸) `X_μ := {ξ : e_μ(ξ) ≠ E(ξ)}`. (⟹) Call `γ` *ξ-honest* if `γ > ξ` and
`ξ ∉ X_γ ∪ U_γ`. Values are nondecreasing along honest levels (else the offending point
lands in `U_γ`); never-honest points below `γ` lie in `X_γ ∪ U_γ`, hence are finite per
level automatically; columns with unbounded honest values are finite below every `α`
(concentrate distinct witnesses at one level `β*` above their sup — all but finitely many
survive `X_{β*} ∪ U_{β*}`, and the registered excess makes `e_{β*}` differ from `e_α`
infinitely, against coherence). Let `E(ξ)` be the maximum honest value; for any `γ`,
choosing `δ*` above `γ` and above countably many attainment stages sandwiches
`E(ξ) = e_{δ*}(ξ) = e_γ(ξ)` off four finite sets. ∎ The proof relativizes to dip systems
on any cofinal set of levels. *Warning:* the running sup `H_γ` of the dipped family does
**not** satisfy `H_γ =* e_γ` in general (dips can hide whole columns below an
ω-cofinality level); the honest-column extraction is the correct route.

**Corollary (Question 1′, the level-factored case) [proved].** A *level-factored*
schedule (`γ(x) = g(ℓ(x))`, `X(x) = Y_{ℓ(x)}`) for the identity pressure map, evaluated
on the probe elements `(α, min(e_α, s_u↾α)) ⊑ u`, induces a uniformizing dip system on
the cofinal level set `g[ω₁]`; hence **level-factored strong schedulability implies
triviality**. Question 1 is thereby rescoped: its open content is exactly
*element-dependent* schedules — whether the per-element freedom of the fiber order
(infinitely many elements per level) can absorb what no level-uniform assignment can.

**Theorem A (trivial ⟹ strongly schedulable) [proved].** Let `E` trivialize `e`. Given
any pressure map `μ`, set `γ := μ` and `X(x) := {ξ < γ(x) : e_{γ(x)}(ξ) ≠ E(ξ)}` (finite,
by triviality). If `ξ ∈ D⁺(γ(x), γ(u)) \ X(x)` then `e_{γ(x)}(ξ) = E(ξ)` and
`e_{γ(x)}(ξ) > e_{γ(u)}(ξ)`, so `E(ξ) > e_{γ(u)}(ξ)`, i.e.
`ξ ∈ {ζ : E(ζ) ≠ e_{γ(u)}(ζ)}` — a finite set depending only on `u`. ∎

*Positioning:* Theorem A says a trivialization is (canonically) a schedule; Theorem B
says level-indexed schedules are *nothing but* trivializations. Question 1 asks whether
the implication "trivialization ⟹ schedule" is secretly an equivalence — i.e. whether
the fiber order's per-element freedom (infinitely many elements per level) adds any
uniformization power at all over the level-indexed case.

**Lemma F (deviation-transfer) [proved].** For any pressure map, the schedule
`γ := μ`, `X(x) := {ξ : s_x(ξ) ≠ e_{ℓ(x)}(ξ)} ∪ dev(e_{ℓ(x)}, e_{γ(x)})` absorbs every
leftover coordinate *below the element's own level* into one finite `u`-set: at such
`ξ` off the dips, `e_{γ(x)}(ξ) = s_x(ξ) ≤ s_u(ξ) = e_{γ(u)}(ξ)` — the order relation
transfers function inequalities that floors do not carry. Consequently **the identity
pressure and every finite-raising pressure (`μ(x) < ℓ(x) + ω`) are schedulable over
every coherent sequence** [proved], and Question 1 reduces to the **gap-core**: only
leftovers at coordinates in `[ℓ(x), γ(x))` — above the element's level, under
limit-raising pressure — remain contested. Per-element freedom provably wins below the
element's level and is, by definition, patch-silent above it.

## 3. The questions

**Question 1 (main).** Is every strongly dip-schedulable coherent sequence trivial?
*(The level-factored case is proved — Corollary to Theorem B above — and by Lemma F the
question is equivalent to its gap-core: schedules win below each element's own level and
on all finite-raising pressures, over every coherent sequence; what is open is exactly
whether the gap regions `[ℓ(x), γ(x))` under limit-raising pressure can be scheduled
over a nontrivial sequence. Ladder-factored gap schedules collapse to Theorem B, like
level-factored ones.)*

**Question 2 (realizability / the fractal gap).** Does weak dip-schedulability imply
strong dip-schedulability? (The subtlety: realizing a given pressure map by a legal
constraint family requires the constraint elements `w_p` — fiber elements at levels
`λ_p` — to be *jointly bounded* on every down-set, and arranging their finite deviations
is itself a schedulability-type problem. The reduction reproduces itself one level down.)

**Question 3 (specific sequences).**
(a) Let `e` be built by the block-diagonal ◊-recursion (at stationarily many limits `δ`,
`e_δ` is the ladder-glue of its predecessors lowered to `0` at one point per ladder
block, the points chosen cofinally in `δ`). Is `e` strongly (weakly) dip-schedulable?
(b) Is `e_α := ρ₁(·, α)` (from walks) dip-schedulable? In the vocabulary of the
derived-limits literature: `[Φ_{ρ₁}] ≠ 0` in `H¹(ω₁)` witnesses nontriviality in ZFC;
the question is whether its class being nonzero already obstructs every element-dependent
schedule, or whether ρ₁'s finer structure (coherence mod finitely-supported functions;
for ρ₂, mod locally constant — Bergfalk–Lambie-Hanson, Cor 2.7) decides the game some
other way. By Lemma E the question may be attacked on any club.

**Question 4 (consistency).** Is "some nontrivial coherent sequence is strongly
dip-schedulable" consistent with ZFC? Natural candidate axioms: MA_{ω₁} or PFA, via a
forcing whose conditions are countable partial schedules; the ccc/properness of that
forcing over the ◊-sequence is precisely where the fractal regress of Question 2
reappears, and is open.

A negative answer to Question 1 with a ZFC witness would (via the argued arrows) refute
`Φ` in ZFC for that sequence; a positive answer makes `Φ(e) ⟺ e trivial` plausible; an
independence answer to Question 3(a)/4 would place `Φ` at the independence boundary.

## 4. Toolbox — short ZFC lemmas [all proved]

**Lemma A (chain-continuation).** For `μ ≤ δ ≤ γ`:
`D⁺(μ, γ) \ D⁺(μ, δ) ⊆ D⁺(δ, γ)`.
*Proof.* If `e_μ(ξ) > e_γ(ξ)` and `e_μ(ξ) ≤ e_δ(ξ)` then `e_δ(ξ) > e_γ(ξ)`. ∎
*Consequence:* along a single chain of levels `μ_1 < μ_2 < ⋯` with supremum `δ*`, the
schedule `X(x_n) := D⁺(μ_n, δ*)` absorbs every continuation `γ ≥ δ*` up to the single
finite set `D⁺(δ*, γ)`. Single chains are never the obstruction; overlap is.

**Lemma B (single target).** For any fixed `δ`, the sets `X_μ := D⁺(μ, δ)` (`μ < δ`) are
finite and absorb the union against the target `δ` completely. Schedulability is about
*all targets simultaneously*, not any one.

**Lemma C (representative systems).** `e` admits `⟨ρ_α : α < ω₁⟩` with `ρ_α =* e_α` and
`ρ_α(ξ) ≤ ρ_β(ξ)` for all `ξ < α ≤ β`, **iff** `e` is trivial.
*Proof.* (⟸) `ρ_α := max(e_α, E↾α)`. (⟹) Four steps. (1) Coherence transfers:
`ρ_β↾α =* e_β↾α =* e_α =* ρ_α`, so each `M(α,β) := {ξ < α : ρ_β(ξ) > ρ_α(ξ)}` is finite.
(2) `U_α := {ξ < α : ∃β, ρ_β(ξ) > ρ_α(ξ)}` is finite: given distinct `ξ_n ∈ U_α` with
witnesses `β_n`, let `β* := sup β_n < ω₁`; monotonicity puts all `ξ_n` into `M(α, β*)`,
contradicting (1). (3) `T := {ξ : sup_β ρ_β(ξ) = ∞}` satisfies `T ∩ α ⊆ U_α` for all
`α`, so `T` has finite initial segments, order type ≤ ω, hence is bounded, say `T ⊆ α₀`.
(4) Off `α₀`, each coordinate stabilizes at `E(ξ)`; for any `α`, taking
`γ(α) := sup` of countably many stabilization stages, `ρ_{γ(α)}` agrees with `E` on
`[α₀, α)` and `ρ_{γ(α)}↾α =* e_α`, so `E =* e_α` there; set `E := e_{α₀}` below `α₀`.
Then `E` trivializes `e`. ∎
*Machine-checked:* the four-step engine is formalized in shadow in
`TransportCalculus.lean` (`reps_implies_trivial`, axioms: `propext, Classical.choice,
Quot.sound`, no `sorry`) — over an abstract index carrying exactly the three properties
of ω₁ the proof uses (least witnesses, σ-directedness, countable segments), with "finite"
rendered as "covered by a list". The boundary is also machine-checked:
`omega_concentration_fails` shows step (2) fails at index ℕ, which lacks σ-directedness
(`nat_not_sigma_directed`) — the regularity hypothesis is load-bearing.
*Update:* the theorem is now also instantiated at **actual ω₁** — mathlib's `ω₁.ToType`
models the abstract index (regularity of ℵ₁ supplies σ-directedness), giving
`omega1_reps_implies_trivial` in `transport-kernel/TransportKernel/OmegaOneCoherent.lean`:
to our knowledge the first machine-checked theorem about coherent sequences on ω₁.

**Lemma D (chain-freeness of the fiber order).** *(This is the pointwise-≤ sibling of
a classical fact: for the coherent tree `T(e)` — Todorcevic, "Lipschitz maps on trees";
Moore's survey — a cofinal branch is exactly a trivialization, and nontrivial `e` gives
an Aronszajn tree. `D(e)` is `T(e)` closed under finite modifications, re-equipped with
the pointwise order; Lemma D is the branch fact for that order, by a different proof.)* `D(e)` contains a `⊑`-chain of order
type ω₁ with levels cofinal in ω₁ iff `e` is trivial.
*Proof.* Such a chain is a club-indexed system as in Lemma C (its functions are pointwise
increasing fiber representatives); the same four steps run verbatim, and coherence spreads
the conclusion from the club of levels to all levels. Conversely a trivializing `E` gives
the chain `(α, max(e_α, E↾α))`. ∎

**Lemma E (cofinal restriction).** If `e` is strongly dip-schedulable, so is its
restriction to any cofinal set of levels `C ⊆ ω₁` (elements, pressure, and schedule
values confined to `C`).
*Proof.* Extend a `C`-pressure map by least-`C`-element-above (down-sets are countable);
take a full schedule `(γ, X)`; push `γ_C(x) := min(C ∩ [γ(x), ω₁))` and absorb the push
into the dips, `X_C(x) := X(x) ∪ dev(e_{γ(x)}, e_{γ_C(x)})`. The triangle inclusion
`D⁺(a,c) ⊆ D⁺(a,b) ∪ D⁺(b,c)` routes every leftover point into the full game's finite
set at `u` or into the single finite set `dev(e_{γ(u)}, e_{γ_C(u)})`. ∎
*Use:* refuting schedulability of a specific sequence (Question 3) may be done on any
club, where e.g. the walk structure of `ρ₁` can be standardized first; nontriviality is
club-robust.

**Remark (thinness).** Coherence forces any single level's deviation from its
predecessors to be finite below every smaller ordinal — so "kills" (as in Question 3(a))
are ω-sequences cofinal in their level, and any fixed lower level sees only finitely many
of them. This is why naive ◊-diagonalizations against schedules fail: committed schedule
entries at levels below a kill see only finitely many killed points (absorbable by one
`X`), while values at levels above the kill inherit the killed floor and need no
correction at all. A successful adversary must exploit *overlap* of down-sets, not any
single level's structure. A template no-go covering five diagonalization designs is in
the notes, §9.

## 4½. Related work (adversarial pass, verified against the sources)

Bergfalk–Lambie-Hanson (arXiv 1902.02736) give the coherence/triviality definitions
(Def 2.10) and prove nontriviality of the walk families (their Thm 2.4) by pressing-down
on stationary sets (Claim 2.6) — a different engine from this note's
witness-concentration; no uniformization-implies-triviality statement appears there. The
derived-limits circle (Bergfalk–Hrušák–Lambie-Hanson; Bannister, arXiv 2302.07222;
arXiv 2411.15856) works over `ω^κ`-indexed systems with higher-dimensional Δ-systems and
partition hypotheses PHₙ; its triviality criteria are cofinality bounds
(`cf(ℐ,⊆*) < ω_n`) or structural Type I/II trivialities — none of dip shape. The
higher-walks introduction (arXiv 2410.00607) reviews ρ₁/ρ₂ coherence (mod
finitely-supported, mod locally-constant respectively) and contains no
monotonicity-after-finite-deletions machinery on the level index. To our knowledge the
schedule game, Theorem B's dip mechanism, and Lemma C's monotone-representatives
equivalence do not appear in this literature.

## 5. Why this may sit at the independence boundary

The game asks for a global choice of finite correction sets, coherent across all
countable directed families of a chain-free (Aronszajn-type) order — structurally between
ladder-system uniformization (◊ refutes, MA_{ω₁} proves, for 2-colorings) and the
triviality of coherent sequences (genuinely ZFC-nontrivial, by walks). Lemma C says the
*chain-indexed* version of the choice problem collapses to triviality; Lemma D says the
index order never contains long chains unless `e` is trivial; Lemma A says every single
chain is harmless. The entire content is the branching overlap — the same locus where
Aronszajn-tree uniformization problems bifurcate under ◊ versus MA/PFA. Against
independence: the per-pair finiteness caps (coherence) have so far defeated every
diagonalization template (§9 no-go), which is weak evidence that ZFC may prove strong
schedulability for *every* coherent sequence — which, note, would answer Question 1
negatively in the strongest way, since nontrivial sequences exist in ZFC.

## 6. Provenance

The question is the terminal reduction of a mechanized research program on certified
composition of contractive morphisms (this repository): the program's one remaining
qualitative question — whether a directed distance order of uncountable cofinality can
defeat every monotone modulus selection — reduces, through machine-checked order theory
(Lean, mathlib-free: `TransportCalculus.lean`) and ten sections of prose set theory
(`NOTES-coherent-escapee.md`), to the diagram of §2. Questions 1–4 are pure ω₁
combinatorics and can be attacked with no knowledge of the program.
