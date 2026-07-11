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

## 4. Toolbox — short lemmas [A–E proved (ZFC); G careful-prose, notes §41]

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

**Lemma G (invariance) [careful-prose; notes §41].** Dip-schedulability is invariant under
the three quotients the coherent-tree theory works modulo: (i) *club restriction* (Lemma E);
(ii) *finite modification* — if `e'_α =* e_α` for all `α`, enlarge each dip by the finite
`dev(e_{γ(x)}, e'_{γ(x)})`; (iii) *level-preserving club-isomorphism of `T(e)`* — a schedule
transports along the isomorphism with per-node finite error (level-preserving maps between
coherent trees are Lipschitz — finite error), absorbed into dips.
*Use (0–1 law):* under PFA all normal ω₁-Aronszajn trees are club-isomorphic
(Abraham–Shelah 1985), so schedulability is a 0–1 law across all nontrivial coherent
sequences; Questions 3(a)/3(b) collapse there and the MA-side conjecture reduces to one `e`.

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
compatibility — ccc. Under MA_{ω₁} every coherent tree is Lipschitz (Lemma 1.10 + MA
specialness; `(*)` there is exactly "meet `ℵ₁` dense sets in a proper poset of size `≤ ℵ₁`",
= MA_{ω₁} for ccc). So MA_{ω₁} makes every `P(e, μ)` ccc, meets the `ℵ₁` dense sets, produces
a schedule. **Conjecture: MA_{ω₁} ⟹ every coherent sequence is strongly dip-schedulable** —
Question 1 false, Question 4 affirmative. (The machine-checked single-element ccc is the
`n=1` shadow of Lemma 1.4; the ZFC/axiom boundary in Lean is exactly `n=1` vs `n≥2`.) The fractal regress of Question 2 is exactly the promise-budget
bookkeeping that becomes *generic* under MA, as with ladder-system uniformization.

**CH side (escapee).** Weak diamond `Φ_{ℵ₁}` (Devlin–Shelah 1978; `Φ ⟺ 2^{ℵ₀} < 2^{ℵ₁}`, so
CH ⟹ Φ) kills ladder-system uniformization — the shape of "no schedule survives." A recursion
building `e` codes each partial schedule on a countable `D_β` as `f↾β ∈ 2^{<ω₁}`, and uses the
Φ-prediction `g(β)` to pick, at stationarily many `β`, the continuation of `e_β` the predicted
schedule fails against. This evades the §9 no-go (weak diamond is a counting principle, not a
guessing recursion, and needs only *one* stationary failure per total schedule). **Target:
CH ⟹ some nontrivial coherent sequence is not strongly dip-schedulable** — Question 1 true.
**The open joint:** making failure-at-`β` verifiable from the countable `D_β`-data — the exact
point where thinness fought ◊; weak diamond's one-stage advantage does not yet close it.

**The 0–1 law (PFA).** By the Invariance Lemma (Lemma G below) dip-schedulability is invariant
under level-preserving club-isomorphism of `T(e)`; under PFA all normal ω₁-Aronszajn trees are
club-isomorphic (Abraham–Shelah, *Isomorphism types of Aronszajn trees*, Israel J. Math. 50
(1985)). So under PFA schedulability is a **0–1 law** across all nontrivial coherent sequences
— Questions 3(a) and 3(b) collapse, and the MA-side conjecture need be checked for one `e`.

**Net.** Question 1 is predicted **independent of ZFC**: false under MA_{ω₁}, true under CH.
`Φ(e)` sits at the independence boundary via the §12 arrow, and the transport escapee exists
in the CH model and is absent under MA. This is the intended terminus of the program — the
qualitative frontier closes as an independence, not a one-sided theorem.

## 6. Provenance

The question is the terminal reduction of a mechanized research program on certified
composition of contractive morphisms (this repository): the program's one remaining
qualitative question — whether a directed distance order of uncountable cofinality can
defeat every monotone modulus selection — reduces, through machine-checked order theory
(Lean, mathlib-free: `TransportCalculus.lean`) and ten sections of prose set theory
(`NOTES-coherent-escapee.md`), to the diagram of §2. Questions 1–4 are pure ω₁
combinatorics and can be attacked with no knowledge of the program.
