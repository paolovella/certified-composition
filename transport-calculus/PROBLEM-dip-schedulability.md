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
trivial  ⟹[proved]  strongly schedulable  ⟹[proved†]  Φ(e)  ⟺[proved‡]  every legally-induced pressure schedulable
   ↑                                                    |
   └────────────────── ??? (Question 1) ────────────────┘
```

(† at careful-prose rigor, notes §12(c), for the value-form definition above;
‡ both directions: notes §16 — a dominator induces a schedule with leftover inside the
single finite set `X(u)` — and notes §20, **Theorem E** — a schedule for the induced
least-absorption pressure rebuilds a monotone dominator. **The game is Φ-complete**:
`Φ(e)` holds iff every legally-induced pressure over `e` is schedulable. Consequently
tame legal systems (finite-raising induced pressure) have dominators over every
coherent sequence in ZFC, and the transport escapee question is exactly: can a legal
system induce an unschedulable pressure? — **Question 5**, the wildness cap.)

*(Localized, notes §22: against the official value-form, condition (ii) exceeds the
set-form (i) by only `|L_u|`-many pointwise-finiteness conditions — one per coordinate in
the finite set-form leftover `L_u`. With Lemma F's below-level dips these localize to
**gap-chain divergence**: (ii) fails at `(u,ξ)` iff the floor values `e_{γ(y_n)}(ξ)`
diverge along a cofinal ω-chain of `{x ⊑ u : ℓ(x) ≤ ξ < γ(x)}`. Since dipping only helps
and is free except for per-element finiteness, scheduling an induced pressure is exactly
a **finite-row covering** of the gap-chain-divergence incidence matrix — the §17–§19
rows/columns problem. Question 5 thereby unifies with the incidence machinery: block-wild
(Theorem F) and tame (§20 Cor. 2) pressures are the proved coverable cases; the ◊-lethal
pressure is the proved non-coverable case, but it is illegal, hence not an escapee.)*

*(Final form, notes §23: with `γ = μ` and Lemma F's dips, the value-form rider is killed
at `(u,ξ)` by dipping `dev(e_{γ(y_n)}, e_{γ(u)})`, finite at each chain level by
coherence (**level-spike finiteness**). A monotone `γ ≥ μ` schedules `μ` as soon as it
has the **finite-fan property** — `⋃_{u ⊒ x} dev(e_{γ(x)}, e_{γ(u)}) ∩ [ℓ(x),γ(x))`
finite for every `x` (**Theorem G [proved]**). *Tame* pressures have finite fan (finite
gaps); *block-wild* pressures are covered instead by block-diagonal domination
(Theorem F), a separate sufficient route — over nontrivial `e` their infinite gap
intervals give infinite fans (notes §24, correcting a §23 slip). So coverability is a
union of incomparable sufficient conditions — tame, BD, finite-fan — and a
non-schedulable induced pressure must defeat all of them. The sharpest reformulation
(notes §24): a legal `Σ` schedules iff its **profile diagonal** `Ψ_Σ(ξ) :=
e_{β_{B(ξ)}}(ξ)` (the splice of block legality-witness floors, `≥` every profile) admits
a **monotone realization** by fiber ceilings with finite defect-union. `Ψ_Σ` is a
trivialization iff `e` is trivial, so over nontrivial `e` it is a locally-trivial,
globally-nontrivial cochain — the `H¹(ω₁) ≠ 0` / derived-limit signature — and the
escapee exists iff such a cochain can be legally forced while resisting monotone
realization. ZFC-yes ⟹ no escapee; consistent-no ⟹ escapee.)*

*(Poset form, notes §25–§26: the finite-approximation poset `P(Σ)` — monotone partial
`γ ≥ μ` with **frozen** finite dips `X` and frozen per-top promises `F` (dips must be
frozen, else the generic's dips blow up to infinite; §26 corrects §25) — realizes a full
schedule generically iff it is ccc. With `γ = μ` the ccc obstruction is concrete: an
uncountable **cross-defective** family, `D⁺(μ(x_i), μ(u_j))` escaping the frozen finite
correction `X(x_i) ∪ F(u_j)` for `i ≠ j`, `x_i ⊑ u_j`. Whether one exists is a ZFC
question about `e`'s floor-defect sets, governed by walk oscillation `osc(ρ)` against
finite correction. The residual is a trichotomy: a legal ZFC cross-defective family ⟹
escapee in ZFC; `P(Σ)` ccc for all legal `Σ` ⟹ no escapee under MA_{ω₁}; a ccc-fatal but
V-correctable family ⟹ independence. Question 5 in its equivalent forms is this
`lim¹`/additivity boundary, with the deciding inequality now written down.)*

*(Located, notes §28–§31. The walk computations clear checkpoint (1): over canonical
`ρ₁` legal limit-raising families exist (`ρ₁(ω·k+j, ω·n) = j`, `⋃_n D⁺(ω·n, ω²) = ∅`), so
the residual is not a tameness artifact. **Correction (notes §31, retracting a §30
overreach):** checkpoint (2) is **not** the abelian strong-homology `lim¹` — Theorem F
(block-wild legal systems over nontrivial `e` are schedulable, while `[e] ≠ 0`) shows
schedulability is a **monotone order realization**, strictly weaker than cohomological
triviality, so the Dow–Simon–Vaughan / BLH / Bannister independence does not transfer.
The residual is an **order-theoretic / cofinality** question: does every legal constraint
system on the directed fiber order `D(e)` admit a monotone dominating selection — the
transfinite-selection question the line opened with (§4–§8). Its independence status is
**open and unknown**: possibly ZFC-decidable (a uniform monotone-selection theorem ⟹ no
escapee), possibly independent of a `pcf`/coherent-order flavor — not the strong-homology
flavor. The ZFC skeleton stands and is machine-checked; the final question is honestly
open.)*
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

**Theorem B⁻ (the downward dual) [proved; machine-checked, notes §53].** Put
`D⁻(μ, γ) := {ξ < μ : e_μ(ξ) < e_γ(ξ)}`. If there are finite `X_μ ⊆ μ` with
`V_γ := ⋃_{μ<γ}(D⁻(μ,γ) \ X_μ)` finite for every γ, then **`e` is trivial** (converse as
in Theorem A). *Proof.* Call γ *ξ-honest* if `γ > ξ` and `ξ ∉ X_γ ∪ V_γ`. Values are
**non-increasing** along honest levels (an increase at `ξ` between honest `μ < γ` puts
`ξ ∈ D⁻(μ,γ) \ X_μ ⊆ V_γ`). The set of `ξ` whose honest levels are bounded is finite: if
`H_ξ ⊆ δ_ξ` then `ξ ∈ X_γ ∪ V_γ` for all `γ > δ_ξ`, so `{ξ : δ_ξ < γ}` sits inside the
finite `X_γ ∪ V_γ`, and an increasing ω₁-chain of finite sets has eventually constant
cardinality, hence finite union. Off that finite set the honest values are a
non-increasing ω-sequence along an unbounded set, hence eventually constant at some
`E(ξ)`; taking `δ*` above `γ` and above the countably many stabilization stages,
`E(ξ) = e_{δ*}(ξ)` for all `ξ < γ` outside one finite set, and `e_{δ*}↾γ =* e_γ`. ∎
This is **strictly easier** than Theorem B — decreasing ℕ-values stabilize for free,
where Theorem B needed witness-concentration for unbounded columns — and it relativizes
to cofinal level sets the same way. It is the form matched to one-sided deviation
geometries (for `ρ₃`, (M1): all downward defect lies at or below the full lower trace).
*Machine-checked* at actual ω₁ as an **equivalence**: `omega1_downDip_iff_trivial` (with
`omega1_downDip_trivial` the substantive direction and `DownDip.ofTrivial` the converse,
which also settles non-vacuity) in
`transport-kernel/TransportKernel/OmegaOneCoherent.lean`; axioms `propext,
Classical.choice, Quot.sound`, no `sorry`. **The first formal dip theorem here** — note
the asymmetry: the *upward* Theorem B, which the Question-1′ corollary below rests on,
is still careful-prose, its witness-concentration step being precisely the part B⁻
avoids.

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

**Theorem C (◊) [careful-prose rigor, notes §15].** There is a coherent sequence that is
**not strongly dip-schedulable**: a ◊-recursion staggers kills across the forced gaps of
guessed schedules — at a guessing stage, one witness element per ladder block, one kill
point per witness chosen *after* seeing that element's finite dip set, inside its gap,
where its committed floor is `1`; the stage's own floor is killed to `0` there, and the
top `(β, e_β)` collects infinitely many surviving gap-inversions, one per pair. Trivial
sequences are schedulable (Theorem A), so the sequence is automatically nontrivial.
Consequences: "every coherent sequence is strongly schedulable" is not a ZFC theorem;
the minimal limit-raising pressure `λ∘ℓ` is already lethal; and Question 1 remains open
in both directions — but a Q1-FALSE witness (nontrivial *and* schedulable) must evade
the staggered-kill mechanism, and the consistency of a full transport escapee now
reduces to Question 2 (realizability of `λ∘ℓ`) over the killed sequence.

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
*(Sharpened, notes §16: over the Theorem-C sequence, realizing the lethal pressure
`λ∘ℓ` is equivalent to **canonical mark-visibility** — all high floors seeing the same
finite mark-set per canonical interval, mod one fixed finite set. Fodor forces some
interval to receive infinitely many marks; the glue makes each floor see only finitely
many; perfect cross-floor coherence of visibility trivializes. If the ◊-recursion can
thread between, the `Φ ⟹ schedule` arrow — now proved with leftover inside the single
set `X(u)` — delivers a legal system with no monotone dominator under ◊.)*
*(Resolved — after one retraction and a restoration; notes §17–§19. **Theorem D**:
over a Theorem-C sequence, the lethal pressure is not weakly realizable, so the
escapee-via-Theorem-C route is closed and the schedule game is strictly stronger than
`Φ` under ◊. The correct proof runs through the **global shown-pattern**: binary floors
are pairwise `=*`-equal, so all floors share one mod-finite pattern of visible marks;
coherence makes each killer's hidden marks finite (rows), legality makes each block's
shown marks finite (columns), and a pressing diagonal — constant row-count `m` on a
stationary set, then `m+2` iterated Fodor pressings — traps a stationary set inside a
finite union of columns. Per-slice arguments provably cannot see this: countable
survivor selection is always feasible via an injective rank, which is exactly what
fails at ω₁.)*

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
forcing whose conditions are finite partial schedules; the ccc/properness of that
forcing over the ◊-sequence is precisely where the fractal regress of Question 2
reappears. *(Update: the complementary consistency statement is settled — by Theorem C,
"some coherent sequence is NOT strongly dip-schedulable" holds under ◊, so
schedulability-for-all is not a ZFC theorem. And §5 now gives the affirmative side a
concrete route: the schedule forcing `P(e, μ)` is ccc iff the alignment statement `A(e)`
holds, which follows from `T(e)` Lipschitz — true for every `e` under MA_{ω₁}, Todorcevic.
So MA_{ω₁} ⟹ every coherent sequence schedulable is conjectured, reducing Question 4 to a
known theorem's applicability plus one citation-precision task.)*

A negative answer to Question 1 with a ZFC witness would (via the argued arrows) refute
`Φ` in ZFC for that sequence; a positive answer makes `Φ(e) ⟺ e trivial` plausible; an
independence answer to Question 3(a)/4 would place `Φ` at the independence boundary.

## 4. Toolbox — short lemmas [A–E, H, I, I′ proved (ZFC); B⁻ proved *and machine-checked*, notes §53; G value-category scope, notes §49]

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
rendered as "covered by a list". *And now unconditionally:*
`omega1_finiteToOne_not_trivial` (notes §53) machine-checks **a coherent sequence on ω₁
with finite-to-one rows is nontrivial** — the classical engine behind Handbook 1.16(a) ⟹
`T(ρ₁)` Aronszajn — so `omega1_finiteToOne_no_reps` gives *no monotone representative
system* with no nontriviality hypothesis imported: what remains cited is only the
positive, computation-checkable existence of a coherent finite-to-one sequence
(Handbook 1.16(a)+(b)), not a negative existential. The boundary is also machine-checked:
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

**Lemma G (invariance) [scope corrected; notes §49].** Dip-schedulability transports along
**value-category** morphisms: club-level correspondences with row comparisons preserving
*pointwise ω-order mod finite* (finite value-distortion per pair, locally finite per top —
absorbed by dips/promises). Instances, both [proved]: (i) *club restriction* (Lemma E);
(ii) *finite modification* — enlarge each dip by the finite `dev(e_{γ(x)}, e'_{γ(x)})`.
**Out of scope: tree maps.** The earlier part (iii) — transport along level-preserving
club-isomorphisms of `T(e)` — is **retracted** (notes §49): tree isomorphisms preserve
splits (`Δ`), but the game runs on deviation *sets* and value *comparisons*, which are not
tree data (per-coordinate value permutations are level-preserving tree isos that scramble
`D⁺` arbitrarily); the Lipschitz property controls `Δ`, not values. Consequently the
previously-stated *PFA 0–1 law* (via Abraham–Shelah club-isomorphism) is **withdrawn**:
Questions 3(a)/3(b) do not collapse by any argument on the table.

**Lemma H (uncountable chains) [proved, notes §51].** `D(e)` has an *uncountable* `⊑`-chain
iff `e` is trivial. (Levels of `D(e)` are countable, so an uncountable chain has uncountably
many levels and an ω₁-subchain with increasing cofinal levels is extractable — Lemma D
applies.) Consequently any σ-decomposition of `D(e)` into *down-finite* pieces (pieces meeting
every `↓u` finitely — "fiber-specialness", notes §50) forces `e` nontrivial; and **Theorem J
(notes §51)**: fiber-specialness of `D(e)` implies the full `=*`-closure tree of `e` is a
*special* Aronszajn tree — end-extension implies pointwise domination, so the closure tree is
a suborder of `D(e)`, and for trees specialness is exactly σ-down-finiteness. The converse
fails at the dips (a tree-antichain can be infinite inside one fiber-down-set).

**Lemma I (successor riding) [proved, notes §52].** For the walk sequence ρ₃ under the
Handbook's C-sequence normalizations ((a) `C_{α+1} = {α}`, (c) no limits in ladders, (d)
the nth ladder element is `λ+n+1`): `B_{γ+1} = B_γ ∪ {γ}`, hence `B_{λ+m} = B_λ ∪ [λ, λ+m)`
— successor rows ride their fans. Consequently **(Q-rows) is false** (notes §52, Theorem L):
the infinite canonical family `{(λ+m, B_{λ+m}) : m ≥ 1}` is bounded in `D(ρ₃)` by any
`(β, B_β ∪ D⁺(λ,β) ∪ ([λ,λ+ω) \ B_β) ∪ ({λ} \ B_β))`, `β ≥ λ+ω` — coherence at one pair
plus fan-cofiniteness. The canonical rows are not strongly unbounded; every fan witnesses it.

**Lemma I′ (successor collapse) [proved, notes §52].** For any coherent `e`, `D(e)` is
fiber-special iff its restriction to limit levels is (split successor levels by
(limit-part, level offset, tail values); restriction maps each piece injectively into a
limit-level down-set). So Lemma I costs fiber-specialness nothing, and the residue of
(Q-rows) is its limit-level form **(Q-rows-lim)** — open, and by notes §52 (Theorems M, N)
equivalent to a one-sided uniformization question for the **threshold sequence θ(ρ₃)**
(`thr_α(λ)` := least N with `ρ₃(λ+n, α) = 1` for all n ≥ N), which is coherent,
finite-to-one, and ω-valued on the fan-top index Λ — Lemma 3.8's clauses are exactly "θ
well-defined" and "θ finite-to-one".

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
equivalence do not appear in this literature. *(Verified first-hand, notes §51, from
Todorcevic's Handbook chapter "Coherent Sequences" and the JIMJ paper: Lemma 3.8 — ρ₃'s ones
are block-finite (`(Λ+n) ∩ B_β` finite) and fan-cofinite (`[λ, λ+ω) ⊆* B_β`); Remark 1.17 —
`T(ρ₁)`, the full `=*`-closure, is a special Aronszajn tree in ZFC, with finite-to-one rows;
JIMJ Lemma 1.10 — a coherent tree is Lipschitz iff every uncountable subset contains an
uncountable antichain, so `T(ρ₃)` is hereditarily non-Souslin in ZFC. No source states
`T(ρ₃)` special; JIMJ footnote 10's `supp` = zero-set is a typo — it contradicts Handbook
3.8 and JIMJ Lemma 2.8's own orthogonality claim; the 1-set reading is correct.)*

## 5. The independence program (concrete, two-sided)

The prediction "this sits at the independence boundary" is no longer structural — it is a
concrete two-sided program, with the MA side reduced to a known theorem's applicability and
the CH side reduced to one coding gap. Full detail and rigor grades in the notes, §41–§43;
citations verified against the sources.

**MA_{ω₁} side (no escapee).** The schedule forcing `P(e, μ)` — finite `⊑`-suitable domains,
monotone `γ ≥ μ`, finite dips, finite frozen promises — has routine density, and by the
machine-checked amalgamation lemma its ccc is equivalent to an **alignment statement** `A(e)`:
among any uncountable family of finite defect-labeled configurations in the coherent tree
`T(e)`, two have aligning cross-defect patterns. The cross-defect patterns are exactly the
Δ-patterns of `T(e)`, so `A(e)` is **Lemma 1.3** of Todorcevic, *Lipschitz maps on trees*,
JIMJ 6 (2007) (uncountable Δ-preserving subfamily). Even cleaner: **Lemma 1.4** (a family of
pairwise-disjoint finite subsets of a Lipschitz tree has an uncountable subfamily whose union
is an antichain) makes Δ-system'd stalks pairwise cross-incomparable, so the machine-checked
amalgamation lemma (`compat_of_crossMono`, vacuous cross-clauses) gives pairwise
compatibility — ccc. **The surprise (notes §46): there is a coherent, nontrivial, Lipschitz
tree `T(ρ₃)` in ZFC** — Todorcevic, *Lipschitz maps on trees*, Lemma 2.8 / Theorem 2.9
(unmarked by `(*)`), with mod-finite coherence and nontriviality. (Todorcevic's *Power-Set of
ω₁*, Theorem 2.5 gives `T(ρ₂)` Lipschitz + special in ZFC, but `ρ₂`'s mod-finite coherence is
not established there, so the coherent-*sequence* resource is `ρ₃`.) Since Lemma 1.4 is a ZFC
consequence of Lipschitz-ness, **the ccc of `P(ρ₃, μ)` is a ZFC question** — the amalgamation
runs with no axiom, and MA_{ω₁} enters only to meet the `ℵ₁` dense sets. **Conjecture:
MA_{ω₁} ⟹ `ρ₃` (nontrivial in ZFC) is strongly dip-schedulable** — Question 1 false, Question 4
affirmative, with the hard part (ccc) in ZFC and the axiom textbook. (The machine-checked
single-element ccc is the `n=1` shadow of Lemma 1.4; the ZFC/axiom boundary in Lean is exactly
`n=1` vs `n≥2`.) **Attack Question 3(b) at `ρ₃`, not `ρ₁`** — the ZFC Lipschitz resource lives
on its tree. The fractal regress of Question 2 is the promise-budget bookkeeping that becomes
*generic* under MA, as with ladder-system uniformization.

**◊ side (escapee), proved.** The false side of "every coherent sequence is strongly
schedulable" needs only *one* non-schedulable witness, and **Theorem C (notes §15) proves under
◊ one nontrivial `e` is not strongly dip-schedulable** — its staggered kill, guided by ◊'s full
guess of `(γ,X)↾D_β`, dodges the seen dips. So **◊ ⟹ some nontrivial coherent sequence is not
strongly dip-schedulable.** (The originally-proposed CH-via-weak-diamond route hits the
**thinness wall** — dodging a schedule's finite dip *set* is multi-bit, not the one bit weak
diamond predicts; notes §45. So the false side is carried by ◊, not by CH alone. **Open
refinement:** does CH-alone suffice, or is ◊-strength genuinely needed? The thinness wall is
evidence for the latter.)

**The 0–1 law: withdrawn (notes §49).** The previously-stated PFA 0–1 law ran Abraham–Shelah
club-isomorphism through Lemma G's part (iii), which is retracted: tree isomorphisms do not
transport schedules (the game's data — deviation sets and value comparisons — is not tree
data). Questions 3(a)/3(b) do not collapse by any argument on the table.

**The CH-wild kill target (notes §48).** Theorem 3.9 (Todorcevic, *Power-Set of ω₁*): under CH,
`2^{ℵ₁}` **pairwise-incomparable Lipschitz trees** — the conspiracy realized as objects, with
cross-oscillation defeating alignment by construction, so the schedule forcing over them has
uncountable antichains. This is the primary CH-side kill target (weak diamond, §45, only a
fallback) — but note it bears on `S` ("every sequence schedulable"), **not on Question 1**, by
the separation below.

**Net — the terminus, decided (notes §49).** Lemma G's exact scope (value category, not tree
category) resolves the §48 fork: **no transport bridge between the Theorem-3.9 wild trees and
`ρ₃` exists in any model** — value-category maps are strictly finer than tree maps, the wild
family is pairwise tree-incomparable under CH anyway, and the club-iso bridge was both PFA-only
and out of scope. So `ρ₃` is **separated**, and the standing picture is:
- **Q1 FALSE under MA_{ω₁}**, witness `ρ₃` (nontrivial in ZFC; schedulable under MA via the ccc
  of `P(ρ₃, μ)`, whose hard part is ZFC — mod the §47 steps-3–4 rigor).
- **Under CH/◊, Q1 is open, with the obstruction precise**: Theorem C's kill *builds* its
  witness and cannot target the fixed `ρ₃`; transport cannot reach `ρ₃`; the wild trees bear
  only on `S`. **The program's central open problem is now: is `ρ₃` strongly dip-schedulable
  under CH (or ◊)?** Its ZFC-Lipschitz-ness gives ccc but not a filter (MA_{ω₁} contradicts
  CH), so both answers are live. *(Reduced, notes §50: CH breaks the §45 thinness wall — only
  `ℵ₁`-many countable partial schedules under CH, enumerable as full objects — and by the
  verified Lemma 2.8 facts the kill over `ρ₃` is exactly the **block-accumulation game**:
  undipped support-points accumulating in one block-class `Λ+k` form a *permanent* leak (every
  floor meets every block finitely), while each element can guard only finitely many blocks.
  The schedule's necessary-and-sufficient counter is a diagonal ranking, existing iff `D(ρ₃)`
  is **fiber-special** — `⋃_n R_n` with each `R_n ∩ ↓u` finite. Tree-specialness does *not*
  supply this (a tree-antichain can meet one fiber-down-set infinitely). So the crux is:
  **is `D(ρ₃)` fiber-special?** ZFC-yes ⟹ the block game dies, `ρ₃` plausibly schedules under
  CH, Q1-false-everywhere-flavored; no ⟹ CH kills `ρ₃`, Q1 independent.)* *(Bracketed, notes
  §51: fiber-special ⟺ σ-decomposition into strongly unbounded sets. **Necessary** — Theorem J:
  the `=*`-closure tree must be special, so "is `T(ρ₃)` special?" (Q-T) is the gate: unstated
  in the verified sources, its ρ₁/ρ₂ proof engines unavailable (binary values), with the
  verified ZFC approximation being hereditary non-Souslinness (Lipschitz + JIMJ 1.10).
  **Cheap** — the Tukey half: `D(ρ₃) ≡_T [ω₁]^{<ω}` outright in ZFC (value-spikes /
  block-spikes via Lemma 3.8(2)), so the crux is the σ-covering, not the cofinal type.
  **Crux** — after the flat-core reduction, whether infinite families can be *jointly almost-
  inside one row*: `{(α_i, A_i)}` is bounded iff `⋃_i (A_i \ B_β)` is finite for some `β`, so
  the canonical-rows instance (Q-rows) is verbatim the game's own absorption quantity
  `⋃ D⁺(α, β)` — the self-similarity is an identity. Any CH-model with `T(ρ₃)` non-special
  kills the diagonal counter there; conversely under CH the C-sequence defining ρ₃ is ours to
  choose.)* *(Advanced, notes §52 — one subproblem settled, the other bracketed. **(Q-rows)
  is FALSE in ZFC** (Theorem L): successor rows ride their fans (`B_{γ+1} = B_γ ∪ {γ}`,
  Lemma I), so each fan's canonical family is jointly absorbed — §51's oscillation hunch
  corrected. Benign: fiber-specialness reduces to limit levels (Lemma I′), where the residue
  (Q-rows-lim) is open and **descends** (Theorems M, N — the pruning formula
  `ρ₃(ξ,β) = ρ₃(ξ,α) ∧ [ρ₁(ξ,α) ≥ ρ₁(α,β)]` above the full lower trace, via Handbook 1.6)
  to a one-sided uniformization game for the coherent finite-to-one threshold sequence
  θ(ρ₃) on fan-tops: absorption ⟺ downward θ-deviations concentrate in a finite set +
  scatter alignment; cheap window fans leak explicitly (N1) and failure forces the trace to
  chase the cheap region forever (N2). And **(Q-T) is bracketed from one side** (Theorem O):
  Con(CH + `T(ρ₃)` special) via BMR specialization — size-ℵ₁ ccc, CH survives, the tree is
  level-absolute — so the Theorem-J-contrapositive CH-kill needs strictly more than CH and a
  non-Souslin non-specialness mechanism that does not yet exist.)* *(Advanced, notes §53 —
  one more subproblem settled and the residue narrowed. **(Q-thr) is answered: θ(ρ₃) is
  NONTRIVIAL in ZFC** (Theorem P) — (T2)+(T3) alone suffice, by the classical engine that
  makes ρ₁ nontrivial (Handbook 1.16(a)); §52 had missed it by asking only about
  *implications between* θ's and ρ₃'s nontriviality, where the direct argument needs
  neither. Consequence: `T(θ)` is a coherent **Aronszajn** tree in ZFC (Handbook 3.11), so
  §52's descent lands on a genuine object rather than a degenerate one. **Theorem B⁻**
  (§4 above) is the downward dual of Theorem B — easier, and matched to (M1)'s one-sided
  pruning. Together they give **Theorem Q: the dense failure mode of (Q-rows-lim) is
  impossible in ZFC** — if the *full* family of limit rows below β were jointly absorbed
  cofinally often, `X_λ := ∅` would be a downward dip system for θ on a cofinal level set,
  trivializing θ against Theorem P. So any (Q-rows-lim) counterexample is **sparse**: for
  each β only a thin infinite subfamily, never all rows below β on a cofinal set of levels
  — the CH-adversary's block accumulation cannot be uniform, it must select, and the
  selection is the ω₁-obstruction again. Also new: **(Q-T-θ)** — is `T(θ)` special? — the
  one-level-down twin of (Q-T), with the record that Handbook 1.17 *asserts* `T(ρ₁)`
  special **without proof**, so no analogue may be cited. And a filed resource
  (Handbook 3.12–3.13, unopened until §53): ρ₃ is *nowhere dense*, `ω₁ = ⋃ₙ (Λ+n)` with
  each `Λ+n` orthogonal to ρ₃ — a free ZFC σ-decomposition of the **index** having exactly
  the shape fiber-specialness wants of the **fiber order**; the gap between them is the
  dips.)*
  *(Advanced, notes §54 — the residual narrowed again, and one natural route closed.
  **Theorem V**: a fan `μ` lying above the trace `λ_F(λ,β)` (with `μ+ω ≤ λ < β`,
  `W := ρ₁(λ,β) ≥ 1`) has `ρ₃(μ+n,β) = 0` for every `n ≤ W`, so `thr_β(μ) ≥ W+1` —
  M(3) plus arrival rigidity. **Corollary V1**: front-loading past the *β*-cheap region is
  therefore automatic, no C-sequence hypothesis needed. **Consequently the natural attack
  — transferring N1/N2 from `thr_α` to the single fixed `thr_β` — is VACUOUS**, its
  hypothesis contradicting V; N2's open content is irreducibly on the `thr_α` side, and
  **Corollary V2** is its surviving walk-computable form: a leak at `μ` needs
  `sup{ρ₁(ν,λ) : μ+ω ≤ ν < λ, λ_F(ν,λ) < μ} < ρ₁(λ,β)` — inner walks cheaper than the
  outer one. The dial itself is now explicit: unfolding Handbook 1.4 gives
  **`λ_F(λ,β) = max_i max(C_{β_i} ∩ λ)`** over the walk's stops, against
  `ρ₁(λ,β) = max_i |C_{β_i} ∩ λ|`, and under (d) these are the same data (place = size),
  so front-loading asks whether a stop can jump a fan with a high place but a low landing.
  Finally, under the harmless extra normalization **(e)** `C_{δ+ω} = {δ+n+1}`,
  **Theorem S** `B_{δ+ω} = B_δ ∪ [δ,δ+ω)` (Lemma I one level up — fan-tops ride their whole
  fan; without (e), `ρ₃(δ,δ+ω)=1` iff `|C_{δ+ω} ∩ δ| = 0`), whence **Theorem T** (those rows
  are strongly unbounded, by 3.8(2) at n=0) and **Theorem U**: **(Q-rows-lim) reduces to
  limits of limits**, parallel to Lemma I′ one level up. All walk formulas re-verified by
  `tools/walk-check.py` over randomized C-sequences below ω²·3. The central question is
  **not** decided.)*
  *(Reframed, notes §55 — the frames themselves audited, and two move. **Theorem W**: for
  coherent trees, *special ⟹ Lipschitz* (Todorcevic, *Lipschitz maps on trees*, Lemma 1.10
  — an iff, unmarked, ZFC — plus footnote 9's definition of special). Hence **`T(ρ₁)` is a
  coherent ZFC-Lipschitz tree**, by Handbook 1.16(b) + 1.17 + 1.10. This **corrects §46**,
  whose search for a coherent ZFC-Lipschitz resource ran ρ₂→ρ₃ and never examined ρ₁. The
  consequence is structural: the MA-side ccc argument needs only Lipschitz-ness, so it
  applies to `ρ₁`; and where Theorem J's necessary gate "`T(e)` special" is **open** for
  `ρ₃` ((Q-T)), it is **passed in ZFC** for `ρ₁`. Cost, stated: the whole §50–§54 apparatus
  (binary rows, Lemma 3.8's block/fan structure, the threshold sequence θ) is ρ₃-specific
  and does not transfer. Caveat: Handbook 1.17 asserts `T(ρ₁)` special *without proof*, so
  the ρ₁ line is graded [proved from a cited, in-source-unproved assertion]; locating that
  proof is a concrete task. **PID landscape** (Kuzeljević–Todorcevic, verified): PID is
  *independent of CH* and implies SH, but is **consistent with a non-special Aronszajn
  tree** — so PID cannot supply the (Q-T) gate. It can, however, speak where MA_{ω₁} cannot:
  applying PID to the fiber order with `I` the ideal generated by the down-sets makes
  alternative (2) *exactly* fiber-specialness, reducing the CH-side consistency question to
  **(Q-PID)**: is that ideal a P-ideal under the mod-finite reading (`↓u_n \ ↓u` finite for
  all n)? — strictly weaker than the σ-directedness of `D(e)` that provably fails. A yes
  gives Con(CH + `D(ρ₃)` fiber-special) from Con(CH + PID). Also recorded: in `D(e)` a
  down-set meets each single level infinitely often, so no level-organised decomposition
  can be fiber-special. The central question remains open.)*
  *(**Audited, notes §56 — and the reduction is corrected.** §50's step "fiber-special ⟹
  the block game dies ⟹ `ρ₃` plausibly schedules" **does not hold as stated**. Writing the
  diagonal ranking down as an explicit dip assignment
  (`X(x) := supp(t_{γ(x)}) ∩ ⋃_{k ≤ rank(x)}(Λ+k)`, finite by 3.8(2)) and computing the
  leftover gives: `L_u ∩ (Λ+k)` is finite **for every k** — the *block-localized* form of
  condition (i), strictly weaker than (i), which demands `L_u` itself finite. A leftover
  spread over infinitely many blocks, finitely in each, violates (i) and is invisible to
  §50's permanent-leak mechanism (which needs infinitely many points in *one* block). So
  the crux is a **conjunction**: **(C1)** fiber-specialness (per-block control — all that
  §51–§54 narrowed) **and (C2)** block-spread control. **Theorem A4** (proved; 9432
  instances checked) localizes (C2): an above-trace drop `ξ = μ+n ∈ D⁺(α,β)` has
  `n ≤ ρ₁(α,β)` or `ρ₁(ξ,α) = 0`, and `{ξ<α : ρ₁(ξ,α)=0}` is finite by Handbook 1.16(a),
  foldable into the dips — so above the trace **(C2) ⟺ for every `u`, all but finitely many
  `x ⊑ u` have `rank(x) ≥ ρ₁(γ(x),γ(u))`**: the ranking must **dominate the walk bars**
  along every down-set, both sides diverging (bars by M3, rank by fiber-specialness). Named
  **(Q-spread)** — and note it is again a monotone dominating selection, the program's own
  signature. Consequence for the record: settling (Q-rows-lim) or (Q-T) affirmatively would
  **not** settle schedulability. Discharged on the way: for binary-valued `e` the value-form
  (ii) is *equivalent* to the set-form (i), so §50's "modulo the value-form bookkeeping"
  hedge costs nothing over `ρ₃`.)*
  *(**(Q-spread) reframed, notes §58.** (C2) is not a boundedness condition but a **rate**
  one. **Lemma Y1 [ZFC]**: (C1) alone forces `{α<β : m_u(α) < N}` finite for every `N`, so
  the level-minima diverge — and Handbook 1.16(a) diverges the bars, so both sides of (C2)
  are finite-to-one below every bound. The two conjuncts of §56 are therefore *not*
  independent: fiber-specialness supplies the shape block-spread needs. **Lemma Y3 [ZFC]**:
  for any single `u`, a rank on the (countable) `↓u` gives (C1) at `u` and `BS(u) = ∅`. So
  neither conjunct alone, nor both at one down-set, is an obstruction: **the whole residual
  is simultaneity across overlapping `↓u`**. Restated as a covering condition: by Corollary
  X1 every element at a level in `S` is exceptional at cofinally many `u` above it, and
  those unavoidable exceptions must be distributed so no `↓u` collects infinitely many.)*
  *(**(Q-spread) worked, notes §57.** Localized: assuming (C1), **(C2) ⟺ for every `u` the
  level-minima `m_u(α) := min{rank(x) : x ⊑ u, γ(x)=α}` dominate `ρ₁(α,γ(u))` off finitely
  many levels** — because at each level all but finitely many elements of `↓u` already
  outrank any fixed bar, by (C1). Down-sets are level-full (`(α, B_α ∩ C) ⊑ (β,C)` for every
  `α<β`), so this is not vacuous. **Theorem X [ZFC]**: there is **no** `g : ω₁ → ω` with
  `{α<β : g(α) < ρ₁(α,β)}` finite for every `β` — by Handbook 1.16(a) plus regularity, the
  same three lines that give `ρ₁`'s nontriviality and Theorem P, now in their third role.
  **Corollary X2**: the domination (C2) needs cannot come from any *level* function, so all
  of (Q-spread)'s content lies in per-element freedom — **Question 1's own dichotomy, one
  level down**, with the level-factored side refuted on both (Theorem B's corollary there,
  Theorem X here). **Corollary X1**: `{α : sup_β ρ₁(α,β) = ∞}` is infinite below every large
  `β`, so the bars really do diverge in the second argument; whence a checkable **necessary
  condition** — any (C2)-rank has exceptional sets growing without bound along every
  ⊑-increasing ω-chain, killing every fixed-`k` block-guarding scheme. Recorded: the
  truncated model suggests `ρ₁(α,·)` is eventually constant, which would make all of this
  vacuous; that is an artefact, and Corollary X1 refutes it in ZFC.)*
- **`S` remains independent-shaped**: FALSE under ◊ (Theorem C, proved), TRUE under MA_{ω₁}
  (conjecture on the cited machinery).
This is the terminus the scope question was load-bearing for: not "Q1 independent via
invariance" (dead — the invariance doesn't exist) and not "Q1 false outright in ZFC"
(schedulability is model-dependent), but **Q1 false under MA with a canonical witness, and a
single concrete open problem — `ρ₃` under CH — standing between the program and a full
answer.**

## 6. Provenance

The question is the terminal reduction of a mechanized research program on certified
composition of contractive morphisms (this repository): the program's one remaining
qualitative question — whether a directed distance order of uncountable cofinality can
defeat every monotone modulus selection — reduces, through machine-checked order theory
(Lean, mathlib-free: `TransportCalculus.lean`) and ten sections of prose set theory
(`NOTES-coherent-escapee.md`), to the diagram of §2. Questions 1–4 are pure ω₁
combinatorics and can be attacked with no knowledge of the program.
