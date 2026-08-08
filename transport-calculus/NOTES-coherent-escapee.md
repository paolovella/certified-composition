# The ◊-side attempt — research note

Status: **attempt, not closed.** This note records the state of the ◊-side construction of
an escapee over the coherent fiber order `D_coh(e)` — what is proved, what is reduced, and
the precise point of obstruction. Prose rigor: careful sketch; nothing here is
machine-checked (ω₁ does not fit a mathlib-free repo), and claims are graded accordingly.

Throughout: `e = ⟨e_α : α < ω₁⟩` is coherent (`e_α : α → ℕ`, `e_α =* e_β↾α`), normalized to
values `≥ 1`; `D_coh(e) := Σ_α {s : α → ℕ ∣ s =* e_α}` with the pointwise order on the
smaller domain. A *system* is a monotone bounded-slice constraint family (realized by
val/img pairs); a *dominator* is a monotone `φ` with `φ(t) ⊒` every slice; an *escapee* is
a legal system with no dominator. A *representative system* ("reps") is `⟨ρ_α : α < ω₁⟩`
with `ρ_α =* e_α` and `ρ_α ≤ ρ_β↾α` pointwise for `α < β` — a level-monotone choice of
fiber representatives.

## 1. Two ZFC lemmas (proofs complete at prose rigor)

**Lemma 1 (level-preserving systems always factor).** If every requirement's level is ≤ its
threshold's level, `φ(t) := t ∨ sup S(t)` (pointwise sup on `dom t`) is a dominator: the
slice bound puts `sup S(t) ≤* e_{λ_t}`, so the value stays in the fiber; monotonicity of
`S` gives monotonicity of `φ` with no floor-mixing. *An escapee must raise levels.*

**Lemma 2 (reps ⇒ everything factors).** Given reps `ρ`, the repaired overshoot
`φ(t) := (μ_t, max(ext_ρ(t), sup S(t), ρ_{μ_t}))` — `μ_t` the sup of levels in the slice,
`ext_ρ` extending `t` by `ρ`-values — is a dominator for *every* legal system: each of the
three terms is monotone, the floor terms nest *exactly* (that is what reps are), and the
slice bound keeps everything in the fiber. Corollary: trivial `e` has reps
(`ρ_α := max(e_α, E↾α)`), so **triviality ⇒ factors-everything**; the escapee, if any,
lives strictly on nontrivial sequences.

## 2. The ◊ theorem (sketch-complete) — **superseded by §2′: this is a ZFC theorem**

*(Kept for the record. The construction below is correct but unnecessary: §2′ proves in ZFC
that reps exist iff the sequence is trivial, so every nontrivial coherent sequence — the
walk sequences included — already lacks reps. The ◊-guessing machinery bought nothing.)*

**Theorem (◊).** There is a coherent sequence `e` with values `≥ 1` admitting **no
representative system** — hence (Lemma 2's route) no canonical dominator repairs exist.

*Sketch.* Build `e` by recursion with a ◊-sequence guessing (codes of) partial rep systems.
Successors: `e_{β+1} := e_β⌢⟨1⟩`. At limit `β`, fix a ladder `β_n ↑ β` and the default glue
`ẽ_β` (block `[β_n, β_{n+1})` copies `e_{β_{n+1}}`). If the guess decodes to a level-monotone
partial system `ρ↾β`, let `P := sup_{α<β} ρ_α` pointwise. If `P` is infinite anywhere, any
`ρ_β` is already dead. Otherwise the constantly-0 set of `P` meets each initial segment
finitely (each `ρ_α =* e_α ≥ 1` off finite), so each block contains a point `ξ_n` with
`P(ξ_n) ≥ 1`; set `e_β := ẽ_β` except `e_β(ξ_n) := 0` for all `n`. Coherence survives —
finitely many `ξ_n` below any `α < β`. Any candidate `ρ_β` must satisfy
`ρ_β(ξ_n) ≥ P(ξ_n) ≥ 1 > 0 = e_β(ξ_n)` at infinitely many points, so `ρ_β ≁* e_β`: the
partial system cannot pass `β`. A total rep system is guessed correctly at stationarily
many `β` (standard coding + club argument), and dies there. ∎

Open side-question *(resolved in §2′)*: the walk sequences (`ρ₁`) may *already* lack reps
in ZFC — worth checking against Todorcevic's unboundedness properties before assuming ◊ is
needed here.

## 2′. ◊ was unnecessary: reps ⟺ trivial (ZFC)

Checking the side-question dissolved the ◊ theorem. No property of walks is needed —
nontriviality alone forbids reps.

**Theorem (ZFC).** A coherent sequence `e` admits a level-monotone representative system
iff `e` is trivial.

*Proof.* (⟸) `ρ_α := max(e_α, E↾α)` for a trivializing `E`. (⟹) Let `ρ` be reps.

1. **Pairwise differences are finite.** For `α < β`:
   `ρ_β↾α =* e_β↾α =* e_α =* ρ_α`, so `M(α,β) := {ξ < α : ρ_β(ξ) > ρ_α(ξ)}` is finite —
   coherence of `e` transfers to `ρ`.
2. **Only finitely many coordinates below `α` ever move after `α`.** Let
   `U_α := {ξ < α : ∃β > α, ρ_β(ξ) > ρ_α(ξ)}`. If `ξ_n ∈ U_α` are distinct with witnesses
   `β_n`, then `β* := sup_n β_n < ω₁` (regularity), and level-monotonicity gives
   `ρ_{β*}(ξ_n) ≥ ρ_{β_n}(ξ_n) > ρ_α(ξ_n)` — so `M(α, β*)` is infinite, contradicting 1.
   This is the decisive step: *monotonicity concentrates countably many witnesses at a
   single countable level.*
3. **The escape set is bounded.** `T := {ξ : sup_β ρ_β(ξ) = ∞}`: each `ξ ∈ T` moves
   cofinally, so `T ∩ α ⊆ U_α` is finite for every `α`; an unbounded set with finite
   initial segments has order type `ω` and hence countable sup — so `T` is bounded, say
   `T ⊆ α₀`.
4. **Bounded escape trivializes.** Off `α₀` every coordinate's value `ρ_β(ξ)` is
   nondecreasing and bounded, hence stable at some `E(ξ)` from a stage `γ_ξ` on. For any
   `α`, `γ(α) := sup{γ_ξ : ξ ∈ [α₀, α)} < ω₁`, and `ρ_{γ(α)}` agrees with `E` on
   `[α₀, α)`; since `ρ_{γ(α)}↾α =* e_α` (step 1's chain), `E =* e_α` on `[α₀, α)`. Set
   `E := e_{α₀}` below `α₀` (coherence handles that block). Then `E↾α =* e_α` for all `α`:
   `e` is trivial. ∎

Corollaries: the earlier "level-monotone + pointwise bounded ⇒ trivial" drops its
boundedness hypothesis (step 3 manufactures it); **every nontrivial coherent sequence — in
particular `ρ₁` of the walks, in ZFC — lacks reps**; and with Lemma 2:

> **Canonical dominators exist iff `e` is trivial — a ZFC dichotomy.**

The independence suspicion thus retreats: the rep-half of the question was never
axiom-sensitive. Whatever independence remains, if any, lives entirely in the
*non-canonical* dominators.

## 3. The obstruction: pressure vs. legality, and the "+1 trap"

Everything below is where the construction stops being a proof and becomes a reduction.

- **Pressure requires boundable infinity.** A dominator is only cornered where
  monotonicity focuses infinitely many committed constraints at one point — i.e. along an
  *infinite boundable* threshold family. Unbounded families exert no pressure (no element
  sits above them to be constrained).
- **Legality then defuses naive encodings.** Bounded slices force the requirements over
  any boundable family to have pointwise sup `≤*` the local floor; fibers absorb finite
  defects; so the focused constraint is always satisfiable *pointwise*. Encoding
  ladder-system colorings as above-floor spikes (`+1` over a reserved track) makes the
  slice unbounded the moment pressure exists: **illegal exactly when useful**. This
  killed every direct transcription of the classical ◊ uniformization failures.
- **The successor-push system is legal** — `Σ_succ := {((β, e_β), (β+1, e_β⌢⟨1⟩))}` has
  bounded slices (the image reuses the threshold's own function; values ≥ 1 absorb the new
  coordinate; an earlier version of this analysis wrongly called it illegal via floor
  accumulation — the defect-free choice of image avoids that). It forces every dominator
  to raise levels cofinally. But its constraint points `(β, e_β)` form an antichain, and
  antichains transmit no coherence.
- **Self-obstruction.** Turning antichain values into coherent data needs a threshold
  *chain* through the fibers; constructing an ω₁-chain of fiber elements requires exactly
  a representative system — the object whose nonexistence powers the kill. Every
  extraction route attempted (joins of canonical points, recursive threshold chains,
  club-restricted reps) circles back to this: **the kill needs reps to aim itself, and
  no-reps is the ammunition.**

## 4. The reduced open core (restated after §2′ — now a pure ZFC question)

With reps ⟺ trivial in ZFC, the bridge is no longer conditioned on ◊:

> **Bridge (open, ZFC-stated).** Over any *nontrivial* coherent sequence — e.g. `ρ₁` of
> the walks, a concrete ZFC object — does some legal system have no dominator at all?
> Equivalently: does "every legal system over `D_coh(e)` factors" imply `e` is trivial?

Lemma 2 + §2′ give the converse: trivial ⟺ reps ⟹ factors-everything. If the bridge
holds, **the transport escapee exists in ZFC** — no independence anywhere in this line. If
it fails — if non-canonical dominators can be assembled over a nontrivial sequence — then
the dip-coherence freedom (upper bounds may dip below the floor at finite sets, chosen
per-point) dodges every rep-shaped obstruction, and `D_coh(e)` factors everything in ZFC
despite the rep dichotomy. Independence, if it enters at all, now has exactly one place
left to live: the behaviour of dip-assembled dominators for specific systems like
`Σ_succ`. The repeated satisfiability wall of §3 is weak evidence for factoring; the
Aronszajn shape of the order and the ZFC rep dichotomy are evidence for the escapee.

What would decide it: (a) a direct construction of a dominator for `Σ_succ` over the ◊
sequence — this must route monotone values through the fibers *without* a rep chain, i.e.
exploit dips essentially, and any success would likely generalize to all legal systems; or
(b) a second ◊-diagonalization *against dominators of `Σ_succ` directly* — the guessed
object is then `φ↾D_β` (legal by a club argument), and the kill must place later structure
conflicting with committed values; §3 shows the conflict cannot be requirement-borne
(legality) nor boundedness-borne (monotone maps send bounded to bounded), leaving only the
fiber-membership of limit values — precisely where §2's kill operates, but now the guessed
`φ` need not be rep-shaped, and the lowering trick needs `P ≥ 1` on a set the adversary
controls, which a dip-happy `φ` may deny. That last sentence is the exact face of the
wall.

## 5. Verdict (revised after §2′ — see §6 for the current verdict)

The session's arc, kept honest: the ◊-side attempt first produced a ◊ theorem (§2), and
checking whether walks already satisfy it in ZFC (§2′) showed the ◊ machinery was
unnecessary — **canonical dominators die over every nontrivial coherent sequence, in
ZFC**, by a four-step argument whose engine is that level-monotonicity concentrates
countably many witnesses at one countable level. The attempt now stands as: three ZFC
theorems (level-preserving systems factor; reps ⟺ trivial; hence canonical dominators
exist iff trivial), one legal pressure system (`Σ_succ`), and one sharply-located open
bridge, now itself a ZFC question: whether rep-death over walks propagates to *all*
dominators of some legal system. One genuinely new idea — dip-side pressure — is still
what the bridge needs, in either direction.

## 6. The dip-side attempt — a correction, a chain-freeness theorem, and a flipped verdict

**Correction: `Σ_succ` factors — it was never a pressure system.** The uniform one-level
shift `φ((α,s)) := (α+1, (s ∨ 1)⌢⟨1⟩)` is a dominator: for `(β, e_β) ⊑ (α, s)` the
requirement `(β+1, e_β⌢⟨1⟩)` is covered (`e_β ≤ s↾β` is the threshold condition; the
appended coordinate is constant `1 ≤` everything, values normalized `≥ 1`); monotonicity
and fiber-membership are immediate. §3's claim that `Σ_succ` "forces every dominator to
raise levels cofinally" was technically true and useless: a one-level raise needs no
coherence choices. Real pressure requires raising to *limit* levels.

**Limit-raising: legality and satisfiability arrive together (the absorption pattern).**
The limit-push system `Σ_lim` (`r((α,s)) := (λ(α), canonical extension)`, `λ(α)` the least
limit above `α`) is legal iff the sequence is *block-tame* — each floor's own last block
sits pointwise below all later floors there — because the requirement floors partition
into blocks and their sup is the block-diagonal `D(ξ) := e_{λ(ξ)}(ξ)`. And over a
block-tame sequence the dominator `φ((α,s)) := (λ(α), max(s ∨ D↾α, e_{λ(α)} on the gap))`
is monotone *by block-tameness itself*: within a block the diagonal supplies the missing
inequality; across blocks tameness does. Fourth instance of the pattern: **whatever
coherence makes a system legal is enough coherence to build its dominator.**

**Theorem (ZFC): `D_coh(e)` contains an ω₁-chain with cofinal levels iff `e` is trivial.**
A chain `⟨(α_θ, s_θ)⟩` with `s_θ ≤ s_{θ'}↾α_θ` pointwise is a club-indexed level-monotone
representative system, and the §2′ proof runs verbatim: coherence pins pairwise
differences finite; the chain concentrates countably many movement-witnesses at
`θ* := sup θ'_n`; the escape set has finite initial segments (levels cofinal), hence is
bounded; bounded escape stabilizes and trivializes. Conversely a trivializing `E` builds
the chain. **So over nontrivial `e` every ⊑-chain has bounded levels — the fiber order is
chain-free, an Aronszajn-type order, provably.** This retroactively explains every failed
chain-mediated kill and extraction at once: the tool those arguments reached for does not
exist in the structure.

**Why no kill assembles: budgets are per-element.** A dominator's deviation set from the
floor (dips and raises) is finite *per element*, and each level carries infinitely many
elements. The per-level covering reduction is therefore wrong for the actual problem (◊
kills per-level coverings by the block-diagonal lowering trick, but dominators never
needed them); greedy assembly of a dominator accumulates corrections only at countable
unions — in *both* processing orders — without ever meeting a finite-budget
contradiction; and the ◊-kill at a limit stage closes into a circle: choosing `e_β` low
enough to defeat the guessed committed values makes the slices that would exert the
pressure illegal at exactly the same elements. Legality and killability quantify over the
same sups. Every kill scheme tried — covering extraction, sup-coherence extraction along
bounded families, chain summoning, stage-wise floor sabotage — fails at this wall, and
the chain-freeness theorem shows the one accumulation mechanism that genuinely binds
(§2′) is structurally unreachable.

**Flipped verdict on the Bridge.** The weight of evidence now favors **ZFC-factoring**:
plausibly every legal system over every coherent sequence has a dominator, and the
residual of the transport line is *empty over fiber orders* — the escapee, if it exists
anywhere, needs a different species of directed order. What is still missing for a proof
is one lemma: the global coordination of per-element finite corrections (the gap-fill
choices on `[α_t, μ_t)`) — a transfinite compactness/amalgamation problem that smells
MA-adjacent but may well be outright ZFC. The sharpest formulation: *can the canonical
overshoot's pairwise-finite monotonicity defects always be repaired by per-element finite
dips, coordinated across the whole order?* Chain-freeness removes the known obstruction;
no new obstruction has survived inspection.

## 7. The coordination lemma, attempted — the residue isolated, and the verdict oscillates

Attempting the coordination lemma directly produced a recursion that works except at one
named point, a positive absorption lemma, and a squeeze that points back toward the
escapee.

**The recursion framework.** Down-sets in `D_coh(e)` are countable, so `D` has an
ω₁-enumeration refining `⊑`. Process elements in that order:
`W_t := max(M_t, e_{μ_t} dipped at a finite X_t, sup of processed past W's)`, maintaining
a **ledger invariant**: for every unprocessed `u`, the excess of processed values over
`e_{γ_u}` (the floor at `u`'s eventual level) stays finite.

**Lemma (requirement-excess inherits uniformly, ZFC).** All `M`-contributions of all
pasts of `u` land inside the single finite set `F_u := {ξ : M_u(ξ) > e_{μ_u}(ξ)}`, by
monotonicity of `M` along `⊑`. The requirement side of the ledger is absorbed for free —
the wall was never the requirements.

**The residue, exactly.** The ledger of `u` reduces to
`∪_{t ∈ ↓u} (D⁺(μ_t, γ_u) \ X_t)` — past floor values baked into gap regions, in
upward-defect against `u`'s target floor, minus the pasts' committed dips. Two structural
facts pin every solution: **level-overshoot buys nothing** (high floors are pairwise
=*-equivalent, so no choice of `γ_u` dominates an accumulated sup), and the `X_t` are
committed once while the targets `γ_u` vary — the *moving-target problem*, the true face
of the coordination lemma.

**The sufficient condition, named.** Call `{X_μ}` (finite sets) a **uniformizing dip
system** for `e` if `∀γ: ∪_{μ<γ} (D⁺(μ,γ) \ X_μ)` is finite. Trivial `e` has one
(`X_μ := dev(e_μ, E)`; leftovers land in `dev(e_γ, E)`). A uniformizing dip system makes
the ledger close and the recursion deliver a dominator for every legal system (modulo
routine value-coordination, believed but not fully checked).

**The near-extraction.** Given `{X_μ}`, the running sup `H_γ := sup_{μ<γ}(e_μ off X_μ)`
is monotone in `γ` with `H_γ ≤* e_γ` — an *almost*-representative system. If its lower
fiber-control could be repaired (`{ξ : H_γ(ξ) < e_γ(ξ)}` finite — the one open gap: the
reps theorem's mover-finiteness needs =*-control from below), the reps theorem fires and
**uniformizing dip systems exist iff `e` is trivial**.

**The squeeze, and the oscillating verdict.** Necessity: a dominator forces per-`u`
finite absorption (`∪_{t ∈ ↓u}(D⁺(μ_t, γ_u) \ X_t)` finite for each `u`, with
`u`-dependent element sets). Sufficiency wants the uniform version. The gap between
per-`u` and uniform has the exact shape of a pressing-down argument — targets `γ_u`
along a club, finite leftover sets, Fodor to stabilize — call it **the Fodor step**. If
the Fodor step and the H-extraction repair both go through, the chain closes:
dominator ⇒ per-`u` absorption ⇒ uniform dips ⇒ trivial — i.e. **the escapee exists in
ZFC** over every nontrivial coherent sequence, reversing §6's lean. If either fails,
the failure mode itself should exhibit the dip-assembly that factors everything. The
Bridge is now squeezed between two finiteness conditions one Fodor argument and one
fiber-control repair apart — the narrowest it has been.

## 8. The Fodor step, attempted — the circle proves itself, and the core goes Aronszajn

**Pressing down works; its input is unobtainable.** The plan was: probe systems force
`W_{c_δ} ≥ e_λ` pointwise for cofinally many `λ < δ`; fiber-hood confines the excess
`X_δ := dev⁺(W_{c_δ})` to a finite set; `δ ↦ max X_δ` is regressive; Fodor stabilizes;
sup-coherence falls out on a stationary set and (via §7's extraction) trivializes. The
pressing-down half is sound. The input half self-destructs, exactly: probes
`m^δ_λ := (λ, min(e_λ, e_δ↾λ))` exist below every canonical `c_δ` (the min is a fiber
element — defects are finite), but then the slice at `c_δ` contains `{e_λ : λ < δ}` and
its *legality is sup-coherence at `δ`* — the conclusion. Dipping the images restores
legality and deletes the pressure at precisely the inversion points. **The probe circle
is now an equivalence, not a suspicion: cofinal floor-pressure is legal iff the
trivialization-surrogate already exists.**

**Two ZFC lemmas.** (i) *Single-target dips are free*: against one `δ`, dip each `e_λ` at
`D⁺(λ,δ)` — finite per `λ`, leftover empty. (ii) *Bounded families are never
obstructions*: if `sup v_λ ≤ w =* e_γ`, then for every `γ'` the leftover is
`⊆ dev⁺(w) ∪ D⁺(γ,γ')`, uniformly in `λ`. (Bounded families of thresholds have bounded
level-sets anyway — levels live below the bound's level — so cofinal-level families are
never jointly bounded; the difficulty was always per-`δ` families glued across `δ`.)

**The chain-continuation lemma (new).** For levels `μ_n ↑ δ*`: dips against `δ*` serve
every continuation, since `D⁺(μ_n, γ) \ D⁺(μ_n, δ*) ⊆ D⁺(δ*, γ)` — one finite set,
independent of `n`. *The moving target is fake for any single chain*: dip against the
chain's own sup.

**But the reduction is self-similar.** With per-element targets `δ*(t)`, the ledger
becomes `∪_{t ∈ ↓u} D⁺(δ*(t), γ_u)` — the sup-coherence problem reproduced at the target
level. Regularity of ω₁ defeats every selection scheme tried: global constants do not
exist; per-down-set constants conflict across overlapping down-sets; club-valued targets
fail over the ◊-sequence, whose kill-set is stationary and defeats sup-coherence along
*every* club. The dip-coordination problem is a fixed point of its own reduction.

**Correction to §7: level-overshoot is not useless.** Over the ◊-sequence, overshooting
the value's level past a kill-point lets the value sit at the post-kill *low* floor — the
killed coordinates need no dips at all; high fibers carry the low values natively. §7's
"overshoot buys nothing" applied to sup-absorption, not to kill-avoidance. Consequence:
a dominator is, in total, a **`D`-indexed rep-like coherent selection** (values in
fibers, pairwise-finite deviations, monotone along `⊑`) — and the §2′ reps kill needs an
ω₁-chain in the *index*, which `D` provably lacks (§6 chain-freeness). The escapee
direction loses its main weapon at exactly the final step, just as the factoring
direction loses its selection schemes to self-similarity.

**Where this leaves the Bridge (third flip).** Both directions now lack a closing
mechanism, and the hard core is isolated: *does a monotone fiber-valued selection with
pairwise-finite deviations exist on the chain-free directed order `D_coh(e)` itself,
over the ◊-built (or walk) sequence?* — a uniformization problem on an Aronszajn-type
index. That is exactly the family of statements where ◊ builds counterexamples and
MA/PFA builds uniformizations. Honest current lean, third revision: **independent of
ZFC**, with the candidate independence statement now concrete: "every legal system over
every coherent fiber order factors" — ◊ plausibly refutes it via a system realizing the
kill-traces (the remaining gap: making the dominator *need* the killed coordinates
despite level-overshoot), MA_{ω₁} plausibly proves it via amalgamation along the
countable-down-set enumeration (the remaining gap: the self-similar ledger). Neither gap
closed this session; both are now single, named, and disjoint.

## 9. The ◊-side gap, attempted — a no-go theorem for the kill template (fourth flip)

The gap was: make the dominator need the killed coordinates despite level-overshoot.
Working it produced a no-go, not a closure.

**Thinness (ZFC).** Coherence forces any single level's kill-set to be finite below every
`α < δ` — an ω-sequence cofinal in `δ`. So every element of level `< δ` sees finitely
many of `δ`'s kill points (dippable per-element), and every floor above `δ` inherits the
kill (coherence pins it ≈ 0 there): inversions live only across the single kill boundary,
thinly. The existing ◊-kill can never accumulate. Staggered multi-level kills die the
same way: one element seeing infinitely many pre-drop coordinates with drops above its
level would make two fixed levels differ infinitely — impossible.

**The forcing dilemma.** Accumulation therefore needs committed *values* (not floors):
img-families with levels cofinal in the kill stage, undipped at the candidate points.
Legality forbids exactly that: such families have unbounded slices (any bound exceeds its
own floor at all kill points). Marker-isolation legalizes mixed-stage systems but the
accumulating element must then carry infinitely many markers — not a fiber element;
unmarked mixing is illegal outright (kill-stage bounds are jointly sup-incoherent).
Delayed-level construction (build a low level late, kill against committed values) fails
too: coherence caps a late level's deviation from already-built higher levels at finite.

**No-go (template-level, proof-shaped).** For any ♦-recursion of the shape used since
§2: (i) commitments available at stage `β` have levels bounded by earlier stages; (ii)
legality confines every slice to sup-coherent stage-mixtures; (iii) sup-coherent mixtures
have absorbable forcing (the §8 bounded-family lemma); (iv) a kill needs cofinal
unabsorbable forcing below its stage. (i)–(iv) are jointly unsatisfiable. In three lines:
**legal forcing is bounded-family forcing; bounded families are absorbable; kills need
unabsorbable forcing.** This covers all five kill designs attempted across these notes —
the "+1 trap", the trace systems, the probe systems, the marker systems, and the delayed
levels are all instances.

**Fourth flip, and what remains live.** The ◊ route is closed for this entire template
family — the first genuinely one-sided evidence in the arc. Remaining routes: (a) the
MA-side amalgamation, which given the no-go pattern now reads as a candidate *ZFC*
factoring proof rather than a consistency result; its missing piece is unchanged (the
self-similar ledger), but the no-go suggests a strategy: show every cross-element
floor-inversion accumulation traces back to some slice's forcing ("**forcing-locality**",
named conjecture) — then absorbability of slices closes the ledger and the metatheorem
"legality ⇒ absorbability ⇒ dominator" becomes a theorem, emptying the fiber-order
residual in ZFC. (b) A kill attacking *monotonicity structure* rather than
fiber-membership — no design exists; the no-go does not formally exclude it, but every
mechanism tried routes through fiber-membership eventually. Current lean, fourth
revision: **ZFC-factoring**, now supported by a no-go rather than by failed attempts
alone.

## 10. Forcing-locality proved; the Bridge becomes a game on `e` alone

**Forcing-locality (proved).** The one forcing pattern the §9 no-go missed is the
*anti-kill*: raise `e_ν` above all its ladder floors at points cofinal in `ν` (coherent —
finitely many such points below each ladder level). It forces the dominator's values high
by *fiberhood*, not by requirements, evading the no-go. But it breaks nothing: for forced
highs to hurt, some higher floor must be low on the same infinite set, and "raised at
`ν`, killed at `ν′`" on one infinite set contradicts pairwise coherence of `(ν, ν′)`.
Together with the no-go: **nothing legal ever forces values above the eventual floors.**
Every cross-element accumulation traces to floor-baking, not forcing — forcing-locality,
as conjectured in §9.

**The collapse.** With forcing-locality the ledger analysis closes around three ZFC
facts: every down-set has a ⊑-cofinal ω-chain (countable and join-closed); the
requirement-sup over a down-set is bounded by legality at its top; and the only surviving
ledger term is **floor-baking along chains** — pre-kill floor values baked by fiberhood
below future kill-levels. Per pair everything is finite (thinness, coherence caps,
chain-continuation dips); across overlapping chains the dips leave per-pair-finite
leftovers whose union regenerates the problem one level up. The regress is *fractal*:
that self-similarity is the phenomenon, not a failure of technique.

**The game.** Level-pressure is free for the adversary — fully-dipped images are always
legal and force nothing but level-raising — so systems reduce to monotone
level-assignments `μ : D → ω₁`, and dominators reduce to schedules: `γ : D → ω₁` with
`γ ≥ μ` plus finite dip-sets `X : D → [ω₁]^{<ω}`. The dominator wins `G(e)` iff for every
`u`: `∪_{x ∈ ↓u} (D⁺(γ_x, γ_u) \ X_x)` is finite. Call `e` **dip-schedulable** iff the
dominator wins.

> **Theorem-shaped equivalence (both directions argued at prose rigor):**
> every legal system over `D_coh(e)` factors ⟺ `e` is dip-schedulable.
> (⟸ the §7 recursion armed with forcing-locality, chain-cofinality of down-sets, and
> chain-continuation dips; ⟹ trace-realization by fully-dipped systems.)

**The final open core.** Trivial `e` is dip-schedulable (reps schedule everything).
The question standing at the end of the whole reduction:

> **Is every dip-schedulable coherent sequence trivial?**

Equivalently: does the ◊-sequence (or `ρ₁`) defeat every schedule? The per-pair coherence
caps argue for the dominator; the fractal regress and the stationary kill-set argue for
the adversary. Everything else — systems, dominators, legality, forcing, fiberhood — has
been proved away. What remains is a self-contained uniformization invariant of coherent
sequences, stated in one line, sitting exactly at the boundary where such invariants
historically go independent. This is where the transport line hands the question to set
theory in its final form.

## 11. The fiber-control gap: `H` refuted, the theorem proved by honest columns

The §7 extraction gap — lower fiber-control of `H_γ` — resolves, but not by repair:
`H` was the wrong object, and abandoning it proves the theorem.

**The `H`-route is refutable.** Take trivial `e` with canonical dips `X_μ := ∅`, then
waste: `X'_μ := μ ∩ ω` for `μ ≤ ω`, unchanged above. Still uniformizing (larger dips only
shrink leftovers), but `H_ω` is undefined on all of ω: `{ξ : H_ω(ξ) < e_ω(ξ)}` is
infinite. A dip system may hide entire columns below any fixed ω-cofinality level, so
`H_γ =* e_γ` is simply false in general.

**Honest columns.** Given a uniformizing dip system `{X_μ}` (finite, with
`U_γ := ⋃_{μ<γ}(D⁺(μ,γ) \ X_μ)` finite for all `γ`), call `γ` *ξ-honest* if `γ > ξ` and
`ξ ∉ X_γ ∪ U_γ`. Then:

0. *Monotone along honest levels*: for ξ-honest `δ < γ`, `e_δ(ξ) ≤ e_γ(ξ)` — else
   `ξ ∈ D⁺(δ,γ) \ X_δ ⊆ U_γ`, against γ-honesty. (Only `ξ ∉ X_δ` and `ξ ∉ U_γ` are used.)
1. *Never-honest points are finite per level, automatically*:
   `NH ∩ γ ⊆ X_γ ∪ U_γ`, since a never-honest `ξ < γ` fails honesty at `γ` itself.
   (The wasteful example above has `NH = ∅`: levels above ω are honest for every `ξ < ω`.)
2. *Unbounded-value columns are finite below every `α`* — the §2′ concentration step,
   with the twist that witnesses live in the approximating levels: given distinct
   `ξ_n < α` whose honest values exceed `e_α(ξ_n)` at witnesses `γ_n`, take a level
   `β* > sup_n γ_n`; all but finitely many `ξ_n` avoid the finite `X_{β*} ∪ U_{β*}`, and
   for those, step 0 registers the excess at `β*`: `e_{β*}` then differs from `e_α`
   at infinitely many points — coherence violated. (No order-type-ω step is needed,
   unlike Lemma C: finiteness below each level is used directly.)

**Theorem B (ZFC): `e` admits a uniformizing dip system iff `e` is trivial.**
(⟸) is Theorem A's dips. (⟹): let `E(ξ)` be the maximum honest value at `ξ`
(attained — values are bounded naturals off the step-2 set; arbitrary on `NH ∪ T`).
Fix `γ`. Choose attainment stages for the countably many `ξ < γ` off `NH ∪ T`, and any
`δ*` above `γ` and above their sup. Off four finite sets — `NH ∩ γ` (step 1), `T ∩ γ`
(step 2), `X_{δ*} ∪ U_{δ*}`, and `dev(e_γ, e_{δ*})` — the value `e_{δ*}(ξ)` is sandwiched:
`≥ E(ξ)` by step 0 from the attainment stage, `≤ E(ξ)` since `δ*` is itself ξ-honest and
participates in the max; and `e_{δ*}(ξ) = e_γ(ξ)` off the deviation set. So `E =* e_γ`. ∎

The proof relativizes verbatim to a dip system defined on any *cofinal* set of levels
(choose `β*`, `δ*` inside it; the conclusion trivializes the full sequence by coherence).

**Corollary (Question 1′): level-factored strong schedulability implies triviality.**
A schedule with `γ(x) = g(ℓ(x))` and `X(x) = Y_{ℓ(x)}`, applied to the identity pressure
map and evaluated on the probe elements `m^u_α = (α, min(e_α, s_u↾α)) ⊑ u`, yields a
uniformizing dip system on the cofinal level set `g[ω₁]`; the relativized Theorem B
finishes. **The open content of Question 1 is now exactly element-dependent schedules** —
whether the fiber order's per-element freedom (infinitely many elements per level) can
absorb what no level-uniform assignment can. The §8 self-similarity analysis says that
freedom is the whole game; Theorem B says it is now the *only* game.

## 12. Phase 1 closes: cofinal restriction, and a multiplicity hole in the schedule

**(a) Lemma E (cofinal restriction).** If `e` is strongly dip-schedulable, then for every
cofinal `C ⊆ ω₁` the `C`-level-restricted game (elements of level in `C`, pressure and
schedule values in `C`) is winnable. *Proof.* Extend a `C`-pressure map `μ` to `D(e)` by
`μ̂(y) := min{c ∈ C : c ≥ ℓ(y) and c ≥ μ(x) for all x ∈ ↓y ∩ D_C}` (countable down-set,
`C` cofinal — well-defined and monotone). Take a full schedule `(γ, X)` for `μ̂`; push:
`γ_C(x) := min(C ∩ [γ(x), ω₁))`, `X_C(x) := X(x) ∪ dev(e_{γ(x)}, e_{γ_C(x)})` — finite by
coherence. For `u ∈ D_C` and `ξ ∈ D⁺(γ_C(x), γ_C(u)) \ X_C(x)`: the triangle inclusion
`D⁺(a,c) ⊆ D⁺(a,b) ∪ D⁺(b,c)` applied twice routes `ξ` into
`D⁺(γ(x), γ(u)) \ X(x)` (the full game's finite set at `u`) or into
`dev(e_{γ(u)}, e_{γ_C(u)})` (finite, `u`-only): the `C`-union is finite. ∎
Contrapositive, for Question 3(b): to refute schedulability of `ρ₁` it suffices to
refute it on any single club — and nontriviality of `ρ₁` is club-robust, so the adversary
may standardize the walk structure first.

**(b) The multiplicity hole, and the value-form schedule.** Writing the
strongly-schedulable ⟹ Φ arrow at careful rigor exposed a gap in the *set-based* schedule
condition: it bounds which coordinates leak, not the values there. Coherence permits
`e_{λ_k}(ξ) → ∞` along levels at a fixed defect coordinate; infinitely many `t ∈ ↓u` may
then hit the same leftover `ξ` with unbounded floor values, and the recursion's
`W_u(ξ) = sup_t W_t(ξ) = ∞` — no function value exists, while the set-condition holds.
**Fixed definition (value-form schedule):** require additionally that
`S_u(ξ) := sup{e_{γ(x)}(ξ) : x ⊑ u, ξ ∉ X(x), ξ < γ(x)}` is finite for every `ξ` and
`≤ e_{γ(u)}(ξ)` off a finite set (per `u`). Theorem A's `E`-schedule satisfies the
value-form (off `X(x)` the dipped floor *equals* `E`, so `S_u = E ≤ e_{γ(u)}` off
`dev(e_{γ(u)}, E)`); Theorem B uses only the set-form, so the equivalence chain survives
with the weaker hypothesis on the harder side.

**(c) Strongly-schedulable (value-form) ⟹ Φ, at careful rigor.** Given legal Σ, set
`μ_t := max(ℓ(t), sup of img-levels over the slice)` — a pressure map. Take a value-form
schedule `(γ, X)`. Enumerate `D(e)` refining `⊑`; define
`W_t := max(ext(t), M_t, sup_{s ⊑ t} W_s, e_{γ(t)} off X(t))` pointwise on `γ(t)`.
(i) *Pointwise finiteness*: unfolding, every ingredient at `ξ` is bounded by
`max(M_u(ξ), S_u(ξ))` — `M_u` finite via any legality bound, `S_u` finite by the
value-form. (ii) *Fiber-hood*: the excess of `W_u` over `e_{γ(u)}` is contained in
`F_u ∪ E_u` where `F_u` (requirement excess) is finite via a legality bound `b_u` —
`M_u ≤ b_u =* e_{ℓ(b_u)} =* e_{γ(u)}` on the common domain, three finite deviations —
and `E_u` (floor excess) is the value-form's exceptional set; downward deviation is at
most `X(u)`. (iii) *Monotonicity and domination* are by construction (the max includes
past values and the slice-sup). So `φ(t) := (γ(t), W_t)` is a dominator. ∎
The problem statement's diagram arrow "strongly schedulable ⟹ Φ" upgrades from [argued]
to [proved at prose rigor, §12(c)] *for the value-form definition*; the set-form retains
only the [argued] grade via this section's counterexample-shaped hole.

## 13. Literature pass, first sweep (gating for shipping) — no subsumption found

Comparison object: Theorem B (level-indexed finite dips + almost-monotonicity-with-
per-target-finite-leftover ⟺ trivial). Sources actually inspected (ar5iv full-text
fetches, excerpt-limited; final gate still requires the PDFs):

- **Bergfalk–Lambie-Hanson, *The Cohomology of the Ordinals I* (arXiv 1902.02736), §2.**
  Definition 2.10 confirmed verbatim as our coherence/triviality with values in an
  arbitrary abelian group `A` (our ω-valued case embeds; the ℤ-remark stands). Their §2
  proves *non*triviality (Theorem 2.4) by contradiction, via pressing-down and regressive
  functions on stationary sets (Claim 2.6) — a different engine from Theorem B's
  witness-concentration; no "uniformization ⟹ triviality" statement appears, no
  per-level finite-correction mechanism, no games or schedules. One nuance worth
  tracking for Question 3(b): `ρ₂` satisfies coherence mod *locally constant* functions
  (`=ᶜ`, their Corollary 2.7), strictly richer than mod-finite — the game as posed is
  mod-finite, and `ρ₂`'s extra rigidity might matter on either side.
- **Bannister, *Additivity of derived limits in the Cohen model* (arXiv 2302.07222).**
  Indexing is `ω^κ`-systems, not ω₁-level-indexed families; the "propagating
  trivializations" reframing (their §4, generalizing BHL Lemma 4.7) concerns injective
  systems and Cohen forcing; the partition principle (§5, not fully visible in the
  fetch) drives vanishing via higher-dimensional Δ-systems. Their "Type I triviality"
  (Definition 8) *is* a per-index finite-exceptional-set condition — but against a single
  global witness, i.e. it is the *definition* of triviality in their setting, not a
  sufficient condition of dip shape. No statement found of the form "per-level finite
  corrections making the family almost-monotone imply triviality".
- **Searches** across the derived-limits circle (partition hypotheses PHₙ, universally
  Baire n-coherent families on `ω^ω`, ladder-system uniformization on trees) surface
  adjacent shapes — Δ-system-driven uniformization, mod-finite agreement off finite
  sets — but nothing with Theorem B's mechanism or Lemma C's statement
  ("pointwise-monotone representatives ⟺ trivial").

**Preliminary verdict (first sweep): no subsumption.** The monotone/dip mechanism —
Lemma C, Theorem B, the schedule game — appears to be ours; the neighborhood is
Δ-systems and partition principles on function-space indices, while ours is
order-monotonicity on the level index. Residual risk before Phase 4: Bannister §5's full
partition principle, the BHL "simultaneously vanishing" paper, and Todorcevic's walks
book ch. 1–2 (for whether ρ₁-specific structure trivially decides Question 3(b)). Those
three reads remain the gate.

### §13 addendum: second sweep — gate CLEARED

Second-sweep fetches (BHL-circle *Simultaneously nonvanishing higher derived limits*,
arXiv 2411.15856; Bergfalk's higher-walks introduction, arXiv 2410.00607; Bannister full
HTML): (i) the BHL-circle's triviality criterion is a *cofinality bound* — their
Prop 2.7: `cf(ℐ, ⊆*) < ω_n` makes every coherent n-family trivial — degenerate for
ω₁-level-indexed 1-families, and of a different shape from dips; (ii) the walks
introduction confirms ρ₁ coherent mod finitely-supported, ρ₂ mod locally constant,
nontriviality as `H¹(ω₁; ℤ) ≠ 0`, and contains **no** monotonicity-after-finite-deletions
characterization ("appears to be an open direction" per the fetch), no level-index
correction machinery, no games; (iii) Bannister's PHₙ is Ramsey-theoretic on Cohen reals
over `ω^κ` via higher-dimensional Δ-systems, his Type I/II trivialities are structural
definitions, and neither involves level-indexed finite corrections or monotonicity off
finite sets. **Verdict: the gate clears — no subsumption of Theorem B, Lemma C, or the
schedule game found across four independent probes.** One footnote of residual risk: the
literal PHₙ statement is deferred inside Bannister §5 and the fetch could not extract it
verbatim; a PDF read of that one section is the last nice-to-have before the arXiv note,
not a blocker for drafting.

### Phase 4 prep: the three-sentence pitch (draft)

> We study a uniformization game on 1-coherent families on ω₁ (your Definition 2.10,
> ω-valued): finite "dip" sets per element of the fiber order, absorbing the pairwise
> upward-defects of a level assignment against every down-set at once. Trivial families
> are schedulable (and level-indexed schedulability is *equivalent* to triviality — a
> short ZFC theorem whose engine, a monotone-representatives ⟺ triviality lemma, is
> machine-checked in Lean); whether a *nontrivial* family — ρ₁, say — can be schedulable
> through genuinely element-dependent corrections is open, and sits at the
> ladder-uniformization/◊-vs-MA boundary. Problem statement with proofs, rigor grading,
> and the Lean artifacts: [link].

## 14. Attacking Question 1: the deviation-transfer lemma, and the gap-core reduction

Question 1's open content after Q1′ was element-dependent schedules. The elements of the
fiber order are exactly pairs (level, finite patch), so an element-dependent schedule is
a *patch-dependent* level assignment — and the patch turns out to carry real power.

**Lemma F (deviation-transfer / below-region absorption) [proved].** For any monotone
pressure `μ ≥ ℓ`, take `γ := μ` and
`X(x) := devSet(x) ∪ dev(e_{ℓ(x)}, e_{γ(x)})` — the element's own deviation set
`{ξ < ℓx : s_x(ξ) ≠ e_{ℓx}(ξ)}` plus one pair-defect, both finite. Then for every `u`
and every `x ⊑ u`:
`(D⁺(γ(x), γ(u)) ∩ [0, ℓ(x))) \ X(x) ⊆ devSet(u) ∪ dev(e_{ℓ(u)}, e_{γ(u)})` —
one finite set depending only on `u`.
*Proof.* At `ξ < ℓ(x)` off `X(x)`: `e_{γ(x)}(ξ) = e_{ℓ(x)}(ξ) = s_x(ξ) ≤ s_u(ξ)` — the
equalities by the dips, the inequality by `x ⊑ u`. Off `u`'s finite set,
`s_u(ξ) = e_{ℓ(u)}(ξ) = e_{γ(u)}(ξ)`, contradicting the inversion. ∎
The order relation transfers *function* inequalities that floors alone do not carry:
this is the first place the fiber order's per-element structure does work that no
level-indexed object can.

**Corollaries [proved].** (i) The identity pressure `μ = ℓ` is schedulable over *every*
coherent sequence (gap regions empty; the value-form holds since the surviving values
are `s_x(ξ) ≤ s_u(ξ)`). (ii) Every *finite-raising* pressure (`μ(x) < ℓ(x) + ω`) is
schedulable over every coherent sequence: the gap `[ℓ(x), γ(x))` is finite and the dips
absorb it outright.

**The gap-core reduction [proved].** Combining Lemma F's dips with any putative
gap-dips, Question 1 is equivalent to its restriction to **gap regions under
limit-raising pressure**: does some (equivalently every) nontrivial `e` defeat all
schedules on the leftovers
`⋃_{x ⊑ u} (D⁺(γ(x), γ(u)) ∩ [ℓ(x), γ(x)) \ X(x))` — coordinates *above* the element's
own level, where no function protects and only the floors speak? Everything below the
element's level is now provably absorbable; the §7/§8 residue was always exactly this.

**A negative finding, recorded as evidence.** The natural ladder-based schedule for the
◊-sequence (dip each ladder point against its successor along the gluing ladder)
collapses into Theorem B: a ladder point sits on the ladders of many limits, its finite
dip set must serve every continuation, and serving all continuations uniformly is a
uniformizing dip system — triviality. So gap-region schedules, if they exist over
nontrivial sequences, cannot be ladder-factored, just as they cannot be level-factored:
each successive factorization structure collapses to Theorem B. The open question now
lives entirely in whether *patch-dependence* (the one resource with a proved win, Lemma
F) can reach into gap regions — where, by definition, the element's patch is silent.
The two live readings sharpen accordingly: (a) patches are silent on gaps, so gap-cores
behave like level-indexed objects, Theorem B's engine eventually applies, and Q1 is
TRUE; (b) the schedule can *choose* γ to park gap floors past kills (§8 overshoot) with
patch-guided targeting, and some nontrivial sequence is schedulable, making Q1 FALSE.
Neither is closed; but the battlefield has shrunk to the gaps.

## 15. The staggered ◊-kill: a non-schedulable coherent sequence (fifth flip, partial)

**Theorem (◊) [careful-prose rigor].** There is a coherent sequence `e` (values `≥ 1`)
that is **not strongly dip-schedulable**: the minimal limit-raising pressure
`μ := λ∘ℓ` (each element raised to the least limit above its level) defeats every
schedule. Since trivial sequences are schedulable (Theorem A), `e` is automatically
nontrivial.

*Construction.* ◊-recursion with baseline value `1`. At a guessing limit `β` (the guess
decoding to a partial schedule `(γ, X)↾D_β`; a club confines `γ[D_β] ⊆ β` and closes
under `λ`), work up the blocks `[b_n, b_{n+1})` of `β`'s ladder, recursively in `n`:

1. `x_n := (b_n, min(e_{b_n}, e_β↾b_n))` — a fiber element of `D_β` (its function uses
   only the already-fixed part of `e_β`), so the guess reveals `γ(x_n), X(x_n)`; note
   `γ(x_n) ≥ λ(b_n)`, so the interval `(b_n, λ(b_n))` lies inside `x_n`'s **gap**.
2. Choose `ξ*_n ∈ (b_n, λ(b_n))` avoiding the finite `X(x_n)` and the finite `0`-set of
   `e_{γ(x_n)}` in the interval — available by the **interval-finiteness invariant**:
   every floor's `0`-set meets every interval `(α, λ(α))` finitely (the glue copies one
   ladder floor per block, each preserving the invariant; kills add one point per
   block). Then `e_{γ(x_n)}(ξ*_n) = 1`.
3. Kill: `e_β(ξ*_n) := 0` — one point per block, coherence preserved.

*The catch.* For a total schedule `(γ, X)` of `λ∘ℓ`, ◊ catches `(γ, X)↾D_β` at some
club-stage `β`. Set `u* := (β, e_β)`: every `x_n ⊑ u*` (their functions ride `e_β` by
construction). For almost every `n`: `ξ*_n ∈ [ℓ(x_n), γ(x_n)) \ X(x_n)`,
`e_{γ(x_n)}(ξ*_n) = 1`, and `e_{γ(u*)}(ξ*_n) = 0` — the single pair `(β, γ(u*))`
inherits the kills off a finite set. So
`⋃_{x ⊑ u*} (D⁺(γ(x), γ(u*)) ∩ [ℓ(x), γ(x)) \ X(x)) ⊇ {ξ*_n : n large}` is infinite:
the schedule condition fails at `u*`. ∎

**Why the prior walls don't stop this — the scope-corrections, recorded.**
- The §9 no-go's clauses (ii)–(iii) are about *legality of forcing systems*; the
  schedule game has no legality constraint on the pressure, so the no-go never governed
  game-kills. Its conclusion stands for what it covered (requirement-forcing kill
  templates in the Φ-frame).
- §10's anti-kill coherence argument covered fiberhood-forcing concentrated at a
  *single* level: "raised at ν, killed at ν′ on one infinite set" violates pair
  coherence. The staggered kill forces high at infinitely many *distinct* levels
  `γ(x_n)`, one point each: every pair carries one new inversion, coherence is
  untouched, and the infinity materializes only in the fiberhood of the would-be value
  at `u*` — which is exactly the refutation.
- Without ◊ the kill fails: the kill points are `e`-definable and finite-per-element, so
  a schedule chosen after `e` dips them (`X(x_n) := {ξ*_n}`). The guess is load-bearing:
  it chooses `ξ*_n` *after* seeing `X(x_n)`. Whether the kill survives without ◊ (e.g.
  from a nontrivial sequence with extra ZFC structure) is open.

**Consequences.**
1. "Every coherent sequence is strongly dip-schedulable" is **not a ZFC theorem** — one
   of §14's two live readings dies. Under ◊, non-schedulable (hence nontrivial)
   sequences exist.
2. The Question 3(a) shape is answered under ◊ for the killed sequence.
3. **Question 1 proper remains open in both directions**: this produces a nontrivial
   *non*-schedulable sequence — consistent with Q1 TRUE — and says nothing about
   whether some nontrivial sequence is schedulable (Q1 FALSE). But any Q1-FALSE witness
   must now evade the staggered-kill mechanism.
4. **The transport escapee's consistency now hinges on exactly one gap**: realizability
   (Question 2) of `λ∘ℓ` over the killed sequence — if the minimal limit-raising
   pressure is weakly realizable by a legal system there, then under ◊ the fiber order
   `D_coh(e)` carries a legal system with no monotone dominator, and the transport
   line's original residual is **consistently inhabited**. Realizing `λ∘ℓ` requires
   img-families whose gap-region floor-sups are slice-bounded — itself gap-core-shaped.
   This is the decisive next check.

## 16. Realizability of the lethal pressure: mark-visibility, and one proved arrow

Theorem C leaves the transport escapee one gap: realizing `λ∘ℓ` by a legal system over
the killed sequence. Working it produced a proved upgrade and a sharp reduction.

**Dominator ⟹ schedule [proved — the `Φ ⟹ weak-schedulable` arrow upgrades].** Given a
dominator `φ` of a legal system, set `γ(x) := ℓ(φ(x))` and `X(x) := dev(W_x, e_{γ(x)})`
(the value's finite deviation from its floor). Monotonicity of `φ` gives, at any
gap-or-below leftover point `ξ ∉ X(x)`:
`e_{γ(x)}(ξ) = W_x(ξ) ≤ W_u(ξ)`, which equals `e_{γ(u)}(ξ)` off `X(u)` — so the entire
leftover at `u` lands inside the single finite set `X(u)`, and the value-form holds via
`W_u`'s pointwise values. Consequently: **a legal system realizing a pressure `μ` with
`μ ≥ λ∘ℓ` on the §15 witnesses, over the killed sequence, yields a dominator-free legal
system under ◊** — the transport escapee — because any dominator would induce a schedule
that the staggered kill has already defeated.

**The realizability reduction.** The natural realizer (min-probes raised to `λ(ℓ(x))`,
gaps filled by the local floor) has slice-sups equal to the **block-diagonal**
`Δ(ξ) = e_{λ⁺(ξ)}(ξ)` — over the killed sequence `Δ = 1` at every kill-mark, while every
sufficiently high floor shows `0` there: slices unbounded, the system illegal — *unless
the images dip the marks in their gap-blocks*. Image dips are finite per block; so:

> **Legality of the lethal pressure ⟺ canonical mark-visibility**: does the §15
> construction admit ladders such that for every canonical interval `I`, all
> sufficiently high floors see the *same* finite set of marks in `I`, mod a single
> finite set per `I`? If yes, the images dip exactly those sets, the system is legal,
> and **the transport escapee exists under ◊**.

**Structural facts framing the sub-question.**
- *Fodor forbids point-finite ladder systems*: the first ladder points of a ladder
  system are constant on a stationary set, so some interval receives marks from
  stationarily many stages — infinite total marks per interval are unavoidable.
- *But the glue erases*: the interval-finiteness invariant (§15) means any *fixed* floor
  sees only finitely many marks per interval — each floor's ancestry chain through an
  interval is finite and forgets the rest. Visibility is finite per floor; the question
  is only whether it is *coherent across floors*.
- *Over-canonicalization fails instructively*: gluing by the canonical block tiling
  (every floor copies `e_{λ(b)}` on `[b, λ(b))`) makes visibility perfectly coherent —
  and erases every kill instantly, breaking coherence with the killing stages
  (their own cofinal mark-sets would differ infinitely from all later floors). Perfect
  visibility-coherence trivializes; the kill needs visibility-incoherence somewhere.
  The triviality/nontriviality tension reproduces itself one level down, now about
  *which marks survive*, not which values.

**Status.** The escapee under ◊ now rests on exactly the mark-visibility sub-question —
a concrete design problem about ladder routing in the §15 recursion, with a proved win
condition and a proved failure mode on either flank. Neither the §9 no-go nor the §10
anti-kill governs it (both scope-corrected in §15); the historically-fatal checks are
inline. This is the closest the transport line's original residual has come to being
consistently inhabited.

## 17. The incidence wall: mark-visibility is impossible — the escapee route closes (sixth flip)

§16's hope is refuted. The mark-visibility design question resolves **negatively**, by a
counting argument that survived every design tried against it.

**Design attempts, recorded compactly (each died by Fodor).** (a) *Milestone
confinement* (≤1 kill per gap of a dynamic club): every interval would carry ≤1 mark
ever — but pressing-down on gap-predecessors shows the kill-set is then non-stationary
(kills at milestone-limits have empty local zones), so some dominator escapes guessing.
(b) *Block-disjoint in-gap reuse, clean spines, gateway routing*: either the strays are
canonically suppressed everywhere — which erases entire mark-sets and breaks coherence
with the killing stages (the over-cleaning death, three separate guises) — or the
routing choices reintroduce stationary reuse. (c) *Canonical sacrifice / last-mark
policies*: consistent per pair, but the global assignment is a row-finite reuse system,
killed below.

**Theorem D (the incidence wall) [careful-prose rigor].** Over any §15-type killed
sequence, the lethal pressure (any `μ ≥ λ∘ℓ` on the witnesses) is **not weakly
realizable**: no legal constraint system exerts it. *Argument.* View
killers × intervals as an incidence matrix. (i) **Columns are Fodor-infinite**: the
first witness-block-starts of a stationary killing family are regressive, so some
interval `I*` is used by stationarily many killers. (ii) **Rows are coherence-finite**:
every floor above a killer shows all but finitely many of its marks (pairwise coherence
with an infinite mark-set), so any visibility policy hides only finitely many marks per
killer. (iii) Img-legality requires **per-interval finite visibility**: image dips are
finite per block, and a fiber element at level `λ(b)` cannot be `0` at infinitely many
marks placed by later stages (they deviate infinitely from its floor). So almost all of
`I*`'s users must permanently sacrifice their `I*`-mark — a sacrifice assignment whose
rows (sacrifices per killer) are finite. (iv) But a **row-finite reuse system is itself
Fodor-impossible**: the families' first elements are regressive, so some single point
lies in uncountably many families, and its owners' rows blow up. Columns force infinite
sacrifice; rows forbid it. ∎

**Consequences.**
1. **The Theorem-C route to the transport escapee is closed.** Under ◊ the killed
   sequence defeats every *schedule* for the lethal pressure — but no *legal system*
   can exert that pressure, so no dominator-free legal system arises this way. The
   legality wall protects Φ exactly at the pressure the kill needs.
2. **Theorem C separates the game from Φ.** The schedule game's adversary (free choice
   of pressure) is strictly stronger than legal systems: game-unwinnable coherent
   sequences exist under ◊, while the corresponding Φ-statement remains open — and now
   looks harder. The §9 no-go's *spirit* is re-established at the Φ-level (its letter
   was game-scoped; §15 corrected that), with the incidence matrix as the quantitative
   mechanism.
3. **A necessary condition on any future escapee construction**: its forcing pressure
   must be *incidence-tame* (legal: bounded columns after sacrifice, finite rows) and
   *kill-compatible* (the ◊-guess must still find undippable inversions) simultaneously.
   The two demands pull against each other through the same matrix; whether any
   construction threads them is the sharpened residual question.
4. **Question 2's answer over §15-sequences is NO** for the lethal pressure: weak
   realizability fails. Weak and strong schedulability can only differ on pressures a
   legal system can actually exert — the fractal regress now has a floor.

**Honest trail.** §16 conjectured mark-visibility might be achievable and flagged it as
the decisive check; this section refutes it. Sixth verdict flip of the program, and like
the others it was forced by an argument, not a mood: the columns are Fodor's, the rows
are coherence's, and nothing fits between them.

## 18. CORRECTION to §17: Theorem D's step (iv) is flawed — the wall is a reduction, not a closure (seventh flip)

Re-auditing §17 before building on it exposed an error. **Step (iv) conflated two row
notions**: the *reuse rows* of a family system (how often κ's family is reused by later
killers) and the *sacrifice rows* of a visibility policy (how many marks κ concedes).
Fodor's pressing-down on n-th witness-elements produces a descending chain of stationary
classes `S₀ ⊇ S₁ ⊇ ⋯`; a killer in `S_n \ S_{n+1}` concedes only ~n marks — finite
rows, no contradiction — unless some killer lies in `⋂_n S_n`, which is not forced
(stationarity is not σ-closed). So the claimed impossibility does not follow, and with
it fall §17's consequences 1, 2, and 4 as stated. What survives, and what replaces the
"theorem":

**Lemma G (columns rigidity) [proved].** For any stationary killing family with thin
cofinal witness-families, some interval is **heavy** (used by stationarily many
killers): press down on first witness-block-starts. Heaviness cannot be designed away.

**Lemma H (caps rigidity) [proved].** Enforcing any uniform per-interval usage cap
forces the killing set to be non-stationary — the same pressing-down violates any cap
on the constant interval. (Likewise the §17 milestone-confinement death stands.)

**The correct reduction [proved].** Per-interval-finite visibility with
per-killer-finite hiding is exactly a **survivor selection**: finitely many surviving
marks per interval, each killer surviving in all but finitely many of its own
intervals. Feasibility ⟺ **each killer's witness-family meets the heavy class
finitely** (concede exactly at heavy intervals; light intervals need no concessions).

**Status after the correction.**
1. The escapee-via-Theorem-C route is **not closed** — it is *reduced* to the
   survivor-selection design question: can the ◊-recursion choose witness-families so
   that heaviness (which Lemma G forces to exist and Lemma H forbids capping)
   concentrates on few-per-killer? The heaviness pattern is dynamic and
   self-referential; freshness-availability at limits of kills is the recurring
   unresolved mechanism.
2. "The game is strictly stronger than Φ" is **retracted to conditional**: it holds iff
   survivor selection is infeasible. Theorem C (game-unwinnable sequences under ◊)
   stands — it never depended on §17.
3. Question 2 over killed sequences **re-opens**: weak realizability of the lethal
   pressure ⟺ survivor selection.
4. The incidence *framework* stands and is the right ledger: columns are Fodor's, rows
   are coherence's, and both rigidity lemmas are real constraints on any future
   construction — but the space between them is open, not empty.

Found by re-auditing before building on §17; the referee that caught it was the
attempt to use it.

## 19. Theorem D restored with a correct proof: the global shown-pattern (eighth and ninth flips)

§18's correction was right that §17's proof was flawed — and wrong to leave feasibility
open. Both are now settled by identifying the load-bearing object §17 and §18 each
missed.

**Why no per-slice argument could work (the countable trick).** Within one slice the
survivor-selection demands are countable, and countable survivor selection is *always*
feasible: take any injective rank `n : blocks → ω`; let the survivors at `b` be the
users of rank `≤ n_b`. Each killer concedes only at the finitely many blocks ranked
below its own index. So legality can never be refuted slice-locally — which is exactly
why §17's attempts kept slipping between quantifiers.

**The global pattern is forced.** The floors of a §15-sequence are pairwise `=*`-equal
functions with binary values, and its only zeros are marks. Hence **any two floors'
shown-mark-sets differ globally finitely**, and there is a single canonical mod-finite
pattern `shown*` — a property of the sequence, not a per-slice choice. The injective
rank needed to satisfy it cheaply would have to embed ω₁-many blocks into ω: the
countable trick dies exactly at the global level.

**Theorem D (restored) [careful-prose rigor].** Over any §15-type killed sequence, no
legal constraint system realizes the lethal pressure. *Proof.*
(1) *Global pattern*: fix any reference floor `Γ*` above the relevant region;
`shown* := ` its shown marks; any other floor's pattern differs globally finitely.
(2) *Rows finite (coherence)*: `e_{Γ*} =* e_κ` and `e_κ` is `0` at all of `marks(κ)`,
so each killer hides only finitely many of its own marks: `g(κ) := |hidden(κ)| < ω`.
(3) *Columns finite (legality)*: a slice covering block `b` is bounded only if every
image at the block dips `shown* ∩ I_b`; image dips are finite and fiber elements cannot
be `0` at infinitely many later marks — so `S_b := ` users whose `b`-mark is shown is
finite, for every `b`.
(4) *Pressing diagonal*: `g` is constant `= m` on a stationary `K′` (countable
partition of a stationary set). Iterate Fodor on the first `m+2` witness-elements of
the families over `K′`: pressed blocks `b₀, …, b_{m+1}` and a stationary core
`K′_{m+1}` all of whose members use every `b_j`. Each core killer hides at most `m` of
its `m+2` pressed marks, hence **shows at least one**, hence lies in
`⋃_{j≤m+1} S_{b_j}` — a finite set. A stationary set inside a finite set is absurd. ∎

**Standing consequences (now on a correct footing).**
1. The escapee-via-Theorem-C route is **closed**: under ◊ the killed sequence defeats
   every schedule for the lethal pressure, and no legal system can exert that pressure.
2. **Theorem C separates the game from Φ**: the schedule game's free pressure is
   strictly stronger than what legality permits. The §9 no-go's spirit holds at the
   Φ-level with the incidence matrix as its mechanism; its §15 scope-correction (the
   game was never covered) also stands.
3. Question 2 over §15-sequences: **weak realizability of the lethal pressure fails** —
   the fractal regress has a floor, and the necessary condition of §17(3) (incidence-
   tameness ∧ kill-compatibility) is confirmed as the constraint on any future escapee
   attempt: by this theorem, over binary staggered-kill sequences, nothing satisfies
   both.
4. Lemmas G and H (§18) remain true and are subsumed: heaviness exists (columns
   somewhere infinite pre-selection) and cannot be capped away — but the real wall is
   the global pattern, not heaviness per se.

**Trail note.** Flip seven retracted §17's proof; flips eight and nine are its
restoration: the countable-feasibility discovery (which showed *why* the old proof
couldn't work) and the global-pattern observation (which made a correct one). The
statement of Theorem D was right the first time; its proof is only now sound.

## 20. The game is Φ-complete: schedule ⟹ dominator, and Φ(e) collapses to the game

The dip-schedulability game was derived as the combinatorial residue of Φ. It is in
fact **equivalent** to it.

**Theorem E (schedule ⟹ dominator) [proved].** Let `Σ` be a legal system over `D(e)`.
Define its induced pressure `μ(u) := max(Λ(u), sup{ℓ(img) : img ∈ S(u)}, ℓ(u))`, where
`E(u)(ξ) := sup{img(ξ) : img ∈ S(u)}` (pointwise finite *by legality*: any slice bound
dominates it) and `Λ(u)` is the least level whose floor absorbs `E(u)` (absorbers are
upward-closed by pair-coherence and nonempty by legality; `E` is monotone since slices
nest; so `Λ` and `μ` are monotone). If `(γ, X)` is a schedule for `μ` — value-form:
`S̃_u(ξ) := sup{e_{γ(x)}(ξ) : x ⊑ u, ξ < γ(x), ξ ∉ X(x)}` finite and `≤ e_{γ(u)}` off a
finite `F_u` — then
`φ(u) := (γ(u), W(u))`, `W(u) := max(e_{γ(u)} dipped at X(u), E(u), S̃_u·1_{F_u ∪ X(u)})`
is a monotone dominator of `Σ`. *Proof sketch, all cases.* Fiberhood: three finite
corrections (dips `X(u)`; `E(u)`'s excess, finite since `Λ(u) ≤ γ(u)` and floors are
pairwise `=*`; the finite raise on `F_u ∪ X(u)`, with finite values by the value-form).
Domination: the `E(u)`-part, with levels covered by the img-level-sup inside `μ`.
Monotonicity at `v ⊑ u`, coordinate `ξ < γ(v)`, by the three parts of `W(v)`:
the `E`-part lands in the `E`-part (`E(v) ≤ E(u)`); the raise-part has
`S̃_v(ξ) ≤ S̃_u(ξ)`, which sits under `W(u)` either via the raise (if `ξ ∈ F_u ∪ X(u)`)
or via the undipped floor (value-form, `ξ ∉ F_u`); and the honest-floor part is the
decisive one — `v` is itself a witness in `S̃_u`'s sup, so `e_{γ(v)}(ξ) ≤ S̃_u(ξ)`, and
the same dichotomy closes. ∎

**Corollary 1 (the collapse).** With `dominator ⟹ schedule` (§16):
**`Φ(e)` ⟺ every legally-induced pressure over `e` is schedulable.** The game is not
an abstraction of the transport question; it *is* the transport question.

**Corollary 2 (tame systems never escape) [ZFC].** By Lemma F, every legal system whose
induced pressure is finite-raising (`μ(u) < ℓ(u) + ω` mod the absorbed part) has a
monotone dominator — over *every* coherent sequence, trivial or not. The first
unconditional positive Φ-result beyond trivial sequences.

**Corollary 3 (the residual, exactly).** A transport escapee among fiber orders exists
iff **some legal system induces an unschedulable pressure over some coherent
sequence** — necessarily limit-raising (Corollary 2), necessarily wild inside down-sets
cofinally (else the kill-side of Lemma F absorbs it). Theorem C manufactures an
unschedulable pressure under ◊; Theorem D shows *that* pressure is not legally induced
over *that* sequence. The remaining question is whether legality and unschedulability
are compatible at all:

> **Question 5 (the wildness cap).** Is there — in ZFC or consistently — a coherent
> sequence `e` and a legal system over `D(e)` whose induced pressure is unschedulable?
> Equivalently (by Theorem E): does `Φ(e)` fail for some coherent sequence? A negative
> answer in ZFC would settle the transport line's original residual: the fiber orders
> of coherent sequences can never defeat every monotone modulus, and the escapee hunt
> must leave this class entirely.

The incidence machinery of §19 is the natural tool: its global shown-pattern argument
used binaryness and the kill's witness structure, and the open work is whether a
general coherent sequence's defect structure (`D⁺`-patterns replacing marks) supports
the same rows/columns dichotomy against wild legal systems.

## 21. The wildness cap, first assault: block-wild systems never escape; the residual is floor-selection

**Theorem F (block-wild cap) [proved].** Call a system *block-wild* if its imgs sit at
levels `λ(ℓ(val))` over their vals (the minimal limit-raising shape). For such systems:
(i) legality is equivalent to **block-diagonal domination** (BD): the function
`Δ_Σ(ξ) := sup{img-values at ξ from ξ's own block}` satisfies: for every `B` some floor
dominates `Δ_Σ↾B` mod finite. (ii) BD *also* schedules the induced pressure: with
`γ := λ∘ℓ`-closure, the gap-leftover at any top `u` is contained in `Δ_Σ↾`'s finite
excess over the bounding floor — no dips needed. Hence by Theorem E every legal
block-wild system has a monotone dominator, over every coherent sequence, in ZFC. ∎

Together with Corollary 2 of §20 (tame systems), the escapee hunt is pushed out of the
two most natural system classes. Two structural remarks:

- **Kills destroy BD** — the block-diagonal picks up pre-kill values (`λ⁺(ξ)` sits far
  below any kill stage marking `ξ`) while post-kill floors show `0` — which is exactly
  *why* Theorem D's wild system was illegal over the killed sequence. Theorems C, D,
  and F are three views of one mechanism.
- The same computation shows: over a sequence *with* BD for its own block-diagonal
  `Δ(ξ) = e_{λ⁺(ξ)}(ξ)`, the canonical block-wild system is legal and exerts genuinely
  limit-raising pressure — legally realizable wildness exists wherever BD holds. It
  just never escapes.

**The residual, sharpened (floor-selection).** For general wild systems, legality
bounds the *img-value* diagonal `Δ_Σ`; schedulability of the induced pressure needs a
*floor* diagonal dominated: some monotone level-selection `γ ≥ μ` for which
`Δ_γ(ξ) := sup{e_{γ(x)}(ξ) : ℓ(x) ≤ ξ < γ(x)}` is locally dominated mod the dips. The
obstruction: least-absorption floors can stick out pointwise above the img-profile on
gap regions (`E(x) ≤* e_{Λ(x)}` pins the floor only in the level order, not pointwise).
So:

> **Question 5′ (floor-selection form).** If every `Δ_Σ`-diagonal of a legal system is
> locally dominated, must *some* level-selection `γ ≥ μ` have locally-dominated floor
> diagonal? A ZFC yes settles Φ(e) for all coherent sequences (no escapee in the
> class); a consistent no — floors sticking out robustly under overshooting, against
> every selection — is the last doorway to an escapee.

The selection problem has the reps flavor one level up: choosing levels whose floors
behave pointwise. The reps theorem itself warns that canonical selections fail over
nontrivial sequences; but the selection here is level-valued, not element-valued, and
overshooting is allowed — neither the reps engine nor its refutation applies as-is.

## 22. Question 5, second assault: the value-form localizes to a finite gap-chain rider — and it IS the incidence problem

Attacking Q5′ against the official value-form (problem statement §1(ii)) produced a clean
demotion of the §12(b) hole and an identification: the wildness cap is the §17–§19
incidence problem, one level richer. No flip — this is forward reduction.

**Reduction Lemma (value-form localizes) [proved].** Fix schedule data `(γ, X)` meeting
the set-form (i), with finite leftover `L_u := ⋃_{x⊑u}(D⁺(γ(x),γ(u)) \ X(x))`. Then the
value-form (ii) holds at `u` **iff** `S_u(ξ) < ∞` for each of the finitely many `ξ ∈ L_u`.
*Proof.* For `ξ ∉ L_u`: any counted `x` (`x ⊑ u`, `ξ<γ(x)`, `ξ∉X(x)`) has
`ξ ∉ D⁺(γ(x),γ(u))` (else `ξ ∈ D⁺\X(x) ⊆ L_u`), so `e_{γ(x)}(ξ) ≤ e_{γ(u)}(ξ)`; hence
`S_u(ξ) ≤ e_{γ(u)}(ξ) < ∞`, and the inequality clause holds off the finite `L_u`. So the
value-form's *entire* surplus over the set-form is `|L_u|`-many pointwise finiteness
conditions. §12(b)'s "`W_u(ξ)=∞`" fear is demoted to a finite, coordinate-local rider. ∎

**Gap localization [proved].** Augment `X` with Lemma F's below-level dips. At `ξ ∈ L_u`,
split `S_u(ξ)` by element level. Elements with `ℓ(x) > ξ` contribute, off the F-dips,
`e_{γ(x)}(ξ) = s_x(ξ) ≤ s_u(ξ)` (fiber transfer), a single finite bound. So `S_u(ξ)=∞`
forces unboundedness over the **gap elements** `G_{u,ξ} := {x ⊑ u : ℓ(x) ≤ ξ < γ(x),
ξ∉X(x)}`. `G_{u,ξ}` is `⊑`-directed (joins of level `≤ ξ` stay below `u`) with a cofinal
ω-chain `y_0 ⊑ y_1 ⊑ ⋯`, levels `≤ ξ`, `γ(y_n) ↑ δ ≤ γ(u)`. So the rider fails at
`(u,ξ)` **iff** the gap-chain floor values `e_{γ(y_n)}(ξ)` are unbounded — a pure
gap-chain-divergence event, exactly the §21 floor-diagonal blow-up, now pinned to
finitely many `ξ` per `u`.

**Why no single-`u` concentration contradiction exists.** The Theorem-B / §2′
witness-concentration argument needs *infinitely many* bad `ξ` at one level to break
coherence. The Reduction Lemma caps bad `ξ` at `|L_u| < ω` per `u`. So coherence does
**not** locally forbid the divergence; the difficulty is genuinely global — spread thin
across all `u`.

**The identification: Q5 is the §19 incidence problem, gap-chain flavored.** Dipping
`ξ` at cofinally many `y_n ⊑ u` kills the `(u,ξ)`-divergence, and dipping only ever
*helps* both conditions (larger `X` shrinks `D⁺\X` and every sup). So the sole
constraint is **finiteness of dips per element**. Form the incidence matrix
rows = fiber elements, columns = coordinates, entry = "this element must dip this
coordinate to kill some divergence it lies on." A schedule for the induced pressure
exists **iff this matrix admits a finite-row covering** (each element dipping finitely
many coordinates suffices). This is precisely the §17–§19 rows/columns problem:
- *Columns* (§21's `Δ_Σ`-diagonal, legality): image-values are locally dominated — the
  column side is exactly the set-form (i) achievability.
- *Rows* (coherence + the value-form rider): finite dips per element.
- The wall of §19 (global shown-pattern ⟹ stationary-in-finite) was the special case
  where the pressure is the ◊-lethal one over the killed sequence: there the required
  covering is finite-row-impossible, which is *why* that pressure is not legally induced.

So the two open threads are one:

> **Question 5 (unified).** Over which coherent sequences does *every* legally-induced
> pressure admit a finite-row dip covering of its gap-chain-divergence incidence matrix?
> ZFC-always ⟹ Φ(e) for all coherent `e` ⟹ the transport line's fiber orders never
> escape (residual settled negatively). A consistent failure ⟹ an escapee. Theorem F
> (block-wild) and §20 Cor. 2 (tame) are the two proved finite-row cases; Theorem D is
> the one proved *infinite-row* case, but its pressure is illegal, so it is not a
> counterexample — it is the boundary marker showing the covering can fail exactly when
> legality already fails.

**Net.** §12(b)'s hole is downgraded to a finite rider; Q5′'s floor-selection is
exactly a finite-row incidence covering; the §19 machinery is the right tool and the
open content is whether *legal* induced pressures (unlike the ◊-lethal one) always yield
coverable matrices. The next concrete target: does legality (column-domination of
`Δ_Σ`) itself imply finite-row coverability — i.e. is there a legal induced pressure
whose gap-chain incidences have a stationary heavy row? Theorem F says no for the
block-wild shape; the general wild shape is the frontier.

## 23. The finite-fan criterion: coverability stripped of the system, and the sharp final question

Attacking §22's "does legality force finite-row coverability for the general wild shape."
The system `Σ` drops out entirely; coverability becomes an intrinsic uniformization
property of `e` relative to `γ`, with a clean criterion. No flip — reduction plus two
proved positive cases and one sharp open question.

**Level-spike finiteness [proved, trivial but load-bearing].** For a limit `δ` and any
`β < δ`, the set `{ξ < β : e_β(ξ) ≠ e_δ(ξ)} = dev(e_β, e_δ)` is finite (coherence). So
relative to any fixed ceiling floor `e_δ`, **each level spikes only finitely many
coordinates.** The floor-divergence of §21 is thus never "wide at a level" — it is thin
at every level and accumulates only across cofinally many levels.

**The obstruction, u-independent form.** Take `γ = μ`, a chain `y_0 ⊑ y_1 ⊑ ⋯ ⊑ u`,
`δ_u := sup_n γ(y_n) ≤ γ(u)`. Off Lemma F's below-level dips, the value-form rider fails
at `(u,ξ)` iff `ξ ∈ dev(e_{γ(y_n)}, e_{γ(u)})` for cofinally many `n` with the values
`e_{γ(y_n)}(ξ)` growing. To kill it, dip `ξ` at those `y_n`. The dip that works for a
*single* ceiling is exactly `X(y_n) ⊇ dev(e_{γ(y_n)}, e_{γ(u)}) ∩ [ℓ(y_n), γ(y_n))` —
**finite, by level-spike finiteness.** The entire difficulty is that `y_n`'s one finite
dip must serve *every* ceiling `γ(u)` for `u ⊒ y_n` at once.

**Definition (finite fan).** A monotone `γ ≥ μ` has the *finite-fan property* if for
every element `x`,
`Fan(x) := ⋃_{u ⊒ x} ( dev(e_{γ(x)}, e_{γ(u)}) ∩ [ℓ(x), γ(x)) )` is finite.

**Theorem G (finite-fan ⟹ coverable) [proved].** If `γ ≥ μ` has the finite-fan
property, then `(γ, X)` with `X(x) := Fan(x) ∪ (`Lemma F dips`)` schedules `μ` (value
form). *Proof.* `X(x)` is finite by hypothesis. For any `u` and `ξ ∈ [ℓ(x), γ(x))` off
`X(x)`, `ξ ∉ dev(e_{γ(x)}, e_{γ(u)})`, so `e_{γ(x)}(ξ) = e_{γ(u)}(ξ)`: no upward defect
and the floor value equals the ceiling — set-form leftover `⊆` the Lemma F `u`-set, and
`S_u(ξ) ≤ e_{γ(u)}(ξ) < ∞`. Below-level coordinates are Lemma F's. ∎

**The two proved classes have finite fan.** *Block-wild* (Theorem F): `γ` is the
`λ∘ℓ`-block closure; continuations `γ(u)` from `x` share `x`'s block ceiling, so
`Fan(x)` is one block-deviation, finite. *Tame* (§20 Cor. 2): `γ = μ` is finite-raising,
gaps finite, `Fan(x) ⊆ [ℓ(x), γ(x))` already finite. Both sidestep the accumulation by
keeping continuations within a bounded ceiling band.

**Why wildness threatens it, and the sharp question.** For strictly-wilder-than-block
legal systems the induced `μ` forces `γ(u)` up to *limit* ceilings, and the
continuations from `x` fan across cofinally many distinct `δ_u`, each contributing its
own finite spike-set — whose union can be infinite. Finite fan is then not automatic; it
must be *engineered* by choosing `γ` so that all continuations above `x` agree on a
single ceiling mod finite. That is exactly a **coherent level-selection**: assigning
levels `γ` so that `e_{γ(x)}` and `e_{γ(u)}` agree below `γ(x)` mod one finite set per
`x`, uniformly. So:

> **Question 5 (final form).** Does every legal induced pressure over every coherent
> sequence admit a finite-fan monotone `γ ≥ μ`? Equivalently: can the ceilings always be
> coherently selected? ZFC-yes ⟹ Φ(e) for all `e`, no transport escapee (residual
> settled negatively). A consistent no ⟹ an escapee.

**Where the evidence points (no claim).** A finite-fan `γ` over the whole order is a
coherent choice of ceilings — structurally a *global* mod-finite trivialization datum of
the reps-theorem type. The reps theorem (now machine-checked at ω₁, Tier 5) says
nontrivial `e` admits *no* level-monotone representative system; a finite-fan selection
is a cousin (level-valued, overshoot-allowed, so not literally refuted by it). The honest
reading: for nontrivial `e`, sufficiently-wild legal systems force `γ` into the limit-
ceiling zone where finite fan is a coherent-selection demand of exactly the flavor that
fails for reps — suggesting **escapees exist for nontrivial `e`, i.e. Q5 is NO and the
transport residual is settled *positively* (escapees exist in ZFC)**. But this is a
suggestion, not a proof: a witness requires exhibiting a *legal* wild system whose
induced pressure defeats every finite-fan `γ`, and legality is exactly the bar that
Theorem D showed the ◊-lethal pressure fails to clear. The construction — a legal wild
system forcing limit ceilings with a non-uniformizable spike pattern — is the single
remaining target, now fully concrete: it needs column-domination (legality) to coexist
with an infinite fan at stationarily many elements.

## 24. CORRECTION to §23, and the profile-diagonal reformulation (tenth flip)

Re-auditing §23 before attempting the escapee construction exposed an error, and the
repair reorganizes the picture toward the honest crux.

**The error.** §23 claimed block-wild `γ` has the finite-fan property. **False.**
Block-wild `γ(x) = λ(ℓ(x))` has *infinite* gap interval `[ℓ(x), λ(ℓ(x)))`, and over
nontrivial `e` the ceilings `{γ(u) = λ(ℓ(u)) : u ⊒ x}` are cofinal in ω₁, so
`Fan(x) = ⋃_u dev(e_{λ(ℓ(x))}, e_{λ(ℓ(u))}) ∩ [ℓ(x), λ(ℓ(x)))` collects every coordinate
in the interval whose floor-value changes at some higher ceiling — generically infinite.
Theorem F covers block-wild by **block-diagonal domination (BD)**, a *distinct*
sufficient condition; it does not go through finite fan. (Tame, §20 Cor. 2, genuinely
has finite fan: its gap interval is finite, so `Fan(x)` is finite outright.) Theorem G's
proof is untouched — finite fan ⟹ coverable still holds; only the "block-wild satisfies
it" remark is retracted.

**The productive consequence: coverability is a union of incomparable sufficient
routes** [proved] — tame (finite gaps), BD (Theorem F), finite-fan (Theorem G). A
non-schedulable induced pressure must defeat **all** routes at once. The schedulable side
is more robust than §23 implied; this is evidence *against* a cheap escapee.

**The profile-diagonal reformulation [proved].** Strip to the dominator (Theorem E). A
dominator's *values* `W(u)` need only track the profile `E(u)`, never the bare floor.
Legality bounds every profile pointwise: `E(u)(ξ) ≤ Δ_Σ(ξ) ≤ e_{β_{B(ξ)}}(ξ)` off finite,
where `e_{β_B}` is the block-`B` legality witness. Define the **profile diagonal**
`Ψ_Σ(ξ) := e_{β_{B(ξ)}}(ξ)` — a splice of the legality-witness floors, pointwise `≥`
every profile. Two facts pin it:

1. `Ψ_Σ` is a *trivialization of `e`* (`Ψ_Σ ↾ α =* e_α` for all `α`) **iff** `e` is
   trivial. (⟸ use the trivialization as witnesses. ⟹ `Ψ_Σ` is the required `E`.) So over
   nontrivial `e`, `Ψ_Σ` dominates all profiles and is *locally floored*
   (`Ψ_Σ ≤* e_{β_B}` on each block `B`) yet is **not** `=*` the sequence — a genuinely
   nontrivial, locally-trivial datum.
2. A dominator must approximate `Ψ_Σ` by *fiber* ceilings `W(u) =* e_{γ(u)}` with `W(u)
   ⊒ E(u)`, monotonically; the defect between `Ψ_Σ` and the floors `e_{γ(u)}` is exactly
   what the dips must absorb. `W(u) := Ψ_Σ ↾ γ(u)` is illegal precisely because
   `Ψ_Σ ↾ γ(u) ≠* e_{γ(u)}` for nontrivial `e`.

> **Question 5 (profile-diagonal form).** For a legal `Σ`, can its profile diagonal
> `Ψ_Σ` — locally floored, `≥` all profiles — be *monotonically realized* by fiber
> ceilings with finite defect-union? Equivalently: does local flooring plus monotonicity
> force a coherent global ceiling? ZFC-yes ⟹ no escapee (residual negative); consistent-no
> ⟹ escapee.

**Why this is the honest crux, and where it points (observation, not proof).** `Ψ_Σ` is a
*locally trivial, globally nontrivial* cochain — the exact signature of `H¹(ω₁) ≠ 0` /
the nonvanishing of a derived limit. The escapee exists iff such a cochain can be forced
by a **legal** system and simultaneously resist monotone realization. Legality supplies
the local flooring for free; the whole question is whether local flooring + monotonicity
forces global flooring — a coherent-sequence uniformization strongly resembling the
`lim¹` / additivity-of-derived-limits questions of Bergfalk–Lambie-Hanson (arXiv
1902.02736) and Bannister (2302.07222), which are classically *independent*. This does
not prove independence, but it relocates the transport residual into a well-mapped
independence-prone neighborhood — which explains why every ZFC attack (Theorems A–G, C, D)
has halted at a boundary rather than closing, and it makes the sharpest concrete target a
*legality-respecting* forcing: add a generic monotone realization of `Ψ_Σ` (MA/PFA side)
or a generic obstruction to all realizations (the escapee side), and check ccc/properness
— the same fractal-regress checkpoint §10 flagged, now with `Ψ_Σ` as the explicit object
being (anti-)uniformized.

**Trail note.** Tenth flip: §23's finite-fan-covers-block-wild remark retracted; found by
auditing before building the escapee on it. Theorem G stands; the reorganization into
three sufficient routes and the `Ψ_Σ` reformulation are the forward content.

## 25. The realization poset, and the ccc checkpoint: the ZFC phase closes, the residual is a lim¹-type independence

The profile-diagonal form (§24) makes the residual a concrete (anti-)uniformization. Here
is the poset that decides it, with the one checkpoint isolated. This is the natural end of
the ZFC-analysis phase: everything above is proved; what remains is a single forcing
dichotomy of known-independence-prone type.

**The realization poset `P(Σ)` [defined; density proved].** For legal `Σ` over `e` with
induced `μ`, conditions are quadruples `p = (d_p, γ_p, X_p, F_p)`:
`d_p ∈ [D(e)]^{<ω}`; `γ_p : d_p → ω₁` monotone with `γ_p ≥ μ`; `X_p, F_p : d_p → [ω₁]^{<ω}`;
subject to, for all `x ⊑ u` in `d_p`, the **promise-respecting** constraints
`D⁺(γ_p(x), γ_p(u)) \ X_p(x) ⊆ F_p(u)` and `{ξ : e_{γ_p(x)}(ξ) > e_{γ_p(u)}(ξ),
ξ ∉ X_p(x)} ⊆ F_p(u)` (value-form seed). Extension `q ≤ p`: `d_q ⊇ d_p`, `γ_q ⊇ γ_p`,
`X_q(x) ⊇ X_p(x)`, and **promises are frozen**: `F_q(u) = F_p(u)` for `u ∈ d_p`.

*Density [proved].* For each `w ∈ D(e)`, `{p : w ∈ d_p}` is dense: given `p`, pick
`γ(w) ≥ max(μ(w), max γ_p[d_p ∩ ↓w], …)` monotone; for the finitely many `u ∈ d_p` with
`w ⊑ u`, set `X(w) := ⋃_u (D⁺(γ(w), γ(u)) \ F_p(u))` — finite, and it forces the promise
`⊆ F_p(u)` at each such `u`; for `u ⊒ w` added later, `w`'s promise `F(w)` is fresh. So a
generic filter yields a total monotone `γ`, dips `X`, and per-top finite promise sets
`F_u` — and because promises are frozen, the realized leftover `L_u ⊆ F_u` stays finite:
**a generic realizes the schedule.** Hence, meeting the ω₁ density sets `{w ∈ d}`:

> **`P(Σ)` ccc (or proper) for every legal `Σ` over every coherent `e`, under MA_{ω₁}
> (resp. PFA), ⟹ Φ(e) for all `e` ⟹ no transport escapee** — consistently with ZFC.

**The checkpoint (isolated).** The only nontrivial question is the ccc/properness of
`P(Σ)`. Incompatibility of `p, q` sharing a top `u` arises from **frozen incompatible
promises**: `F_p(u) ≠ F_q(u)` with `γ`-values whose amalgamated defect escapes both. An
uncountable antichain is an uncountable family of conditions whose pairwise amalgamation
forces a defect outside every frozen promise — a Δ-system-plus-coherence-oscillation
configuration. Whether one exists is governed precisely by the **oscillation of `e`'s
walks** (Todorcevic): the same `osc(ρ)` structure that makes `H¹(ω₁) ≠ 0`. So:

> **Question 5 (poset form, final).** Is `P(Σ)` ccc for every legal `Σ`, or does some legal
> `Σ` over some nontrivial `e` yield a walk-oscillation antichain? The former (consistently)
> caps every escapee; the latter, if it forces the realization to fail *in V*, is the
> escapee. This is a `lim¹`-type dichotomy: `P(Σ)` is the finite-approximation poset of a
> derived-limit vanishing, `Ψ_Σ` the cochain being trivialized, and its ccc is the
> additivity/oscillation question of Bergfalk–Lambie-Hanson and Bannister.

**Status of the transport line (honest ledger).** The escapee is neither cheaply built
nor cheaply refuted, and now we know *why*: it sits at a `lim¹` independence boundary. The
ZFC reduction is complete and, at each step, a theorem:

- **[proved]** trivial ⟹ schedulable (A); level/ladder-factored ⟹ trivial (B, Cor 1′);
  Lemma F (below-level absorption); dominator ⟺ schedule (E, the game is Φ-complete);
  tame and block-wild caps (§20 Cor 2, F); finite-fan ⟹ coverable (G); the value-form
  localizes to a finite gap-chain rider = a finite-row incidence covering (§22);
  level-spike finiteness and the profile-diagonal reformulation (§23–24).
- **[proved under ◊]** a non-schedulable (hence nontrivial) coherent sequence exists (C);
  its lethal pressure is not legally induced (D) — the escapee route through *that* kill
  is closed.
- **[open, ⟺ Question 5]** whether a *legal* system can induce an unschedulable pressure
  = whether `Ψ_Σ` resists monotone realization = whether `P(Σ)` fails ccc — a
  `lim¹`-type question, expected independent, matching §10's original prediction.
- **[machine-checked, ZFC]** the anchor of the whole chain — reps ⟺ trivial — is
  formalized in Lean at actual ω₁ (Tier 5, `OmegaOneCoherent.lean`).

The transport line's original residual is thereby *located*, not eliminated: it is a
concrete, named `lim¹`-type independence, with its ZFC skeleton fully proved and its
combinatorial heart (Question 5, five equivalent forms) handed to set theory in final
form. This is the honest terminus of the ZFC phase.

## 26. CORRECTION to §25: the dips must be frozen, and the ccc reduces to a concrete ZFC defect-configuration (eleventh flip)

Attempting to *run* §25's poset — the honest test the user pressed for — exposed a gap and
sharpened the checkpoint to a concrete ZFC question.

**The gap.** §25 let dips grow under extension (`X_q(x) ⊇ X_p(x)`) and claimed a generic
realizes the schedule. But then `X(x) = ⋃{X_p(x) : p ∈ G}` is a union over uncountably
many conditions; each finite, the union need not be. A schedule requires **finite** dips.
So growing-dip genericity yields at best an infinite-dip pseudo-schedule — not a witness
to Φ(e). The dip poset with growing dips is trivially ccc (σ-centered: dips only help),
which is exactly why it proves nothing.

**The repair: freeze the dips.** The correct poset `P(Σ)` freezes both `X` and `F`:
`X_q(x) = X_p(x)` and `F_q(u) = F_p(u)` for `x, u ∈ d_p`. A generic then gives genuinely
finite `X(x)` and `F_u`, and `L_u ⊆ F_u` — a real schedule. But freezing dips **removes**
the free amalgamation: a new top `u ⊒ x` can no longer be served by *growing* `x`'s dip,
so the cross-constraint `D⁺(μ(x), μ(u)) \ X_p(x) ⊆ F_q(u)` with both sides frozen is a
hard compatibility condition. The obstruction §25 waved away is now first-class.

**The ccc checkpoint, made concrete [reduction proved].** Take `γ = μ` (monotone
already, so no γ-inversions). Δ-system a putative uncountable antichain to a fixed root
with matching frozen data and disjoint iso stalks. Two conditions `p_i, p_j` are
incompatible **iff** some cross pair `x ∈ a_i`, `u ∈ a_j` (or vice versa) with `x ⊑ u`
has `D⁺(μ(x), μ(u)) \ X_{p_i}(x) ⊄ F_{p_j}(u)`. Since each condition is internally
consistent (`D⁺` internal to a stalk already dipped/promised), an uncountable antichain
is exactly:

> an uncountable family of "internally clean" configurations that are pairwise
> **cross-defective beyond their frozen finite corrections** — the defect
> `D⁺(μ(x_i), μ(u_j))` escaping `X(x_i) ∪ F(u_j)` for `i ≠ j`.

Whether such a family exists is a **ZFC combinatorial question about the defect sets
`D⁺` of `e`'s floors at the pressure levels** — no forcing in the statement. It is
governed by walk oscillation: `osc(ρ)` unbounded on a stationary set is precisely what
would let the cross-defects outrun any fixed finite correction, building the antichain;
`osc` tame would refine it away (ccc).

**Honest status — the two decisive sub-questions.** The whole residual now rests on a
fork, both sides concrete and neither requiring the other's machinery:

1. **(ZFC escapee side.)** Does some legal `Σ` over a walk-based `e` admit an uncountable
   cross-defective family whose defects provably cannot be finitely corrected *in V*?
   That is a ZFC non-coverability — an escapee outright, no independence needed. Theorem
   D built the shape under ◊ but illegally; the open question is a **legal, ZFC** version
   driven by `osc(ρ₁)` rather than kills.
2. **(No-escapee-consistent side.)** Is `P(Σ)` (frozen) ccc for every legal `Σ`? Then
   MA_{ω₁} realizes every schedule ⟹ Φ(e) for all `e`, consistently.

If (1) succeeds the residual is settled *positively in ZFC* (escapees exist); if (1)
fails and (2) succeeds, escapees are *consistently absent*; and a walk-oscillation
antichain that is ccc-fatal but V-correctable would put the object squarely independent.
This is a genuine trichotomy, and which branch holds is exactly the `osc(ρ)`-vs-finite-
correction combinatorics — the `lim¹`/additivity boundary, now with the deciding
inequality written down.

**Trail note.** Eleventh flip: §25's growing-dip genericity retracted (proves nothing —
infinite dips); frozen-dip poset installed; ccc reduced to a written-down ZFC
cross-defect inequality. Found by trying to run the poset, per the standing discipline of
auditing before believing. The `lim¹`-neighborhood placement (§24) stands and is
reinforced: the deciding combinatorics is `osc(ρ)` against finite correction.

## 27. Branch (1) setup: the osc-driven legal cross-defective family — a precise open target (not a result)

The honest run at the one branch that would give a *ZFC* escapee with no independence
caveat. I can pose it exactly; I do **not** claim it — completing it needs Todorcevic's
oscillation combinatorics (Walks, ch. 1–2), which is a genuine development, not a
prose flourish. Stated so a future session or a set theorist can attack it directly.

**The target.** Exhibit, in ZFC, a coherent `e` (walk-based, `e_α := ρ₁(·, α)` or a
binary refinement) and a **legal** system `Σ` over `D(e)` with induced pressure `μ`,
admitting an uncountable family `{(x_i, u_i) : i < ω₁}` such that:
- (internal clean) `D⁺(μ(x_i), μ(u_i)) = ∅`;
- (cross defective, beyond finite correction) for `i < j` with `x_i ⊑ u_j`,
  `D⁺(μ(x_i), μ(u_j)) ⊄ X(x_i) ∪ F(u_j)` for the frozen finite `X, F`.
By §26 this makes `P(Σ)` non-ccc *and*, if the escape is witnessed in `V`, refutes
schedulability of `μ` — a legal, ZFC non-schedulable induced pressure, i.e. an escapee.

**The one lemma the construction must supply (isolated).**

> **(osc-escape.)** There is a legal `Σ` such that the map `(i, j) ↦ D⁺(μ(x_i), μ(u_j))`
> has the property: for every choice of finite `X(x_i), F(u_j)` (of the sizes a
> condition allows), stationarily many `j` see cofinally many `i < j` with the defect
> escaping — i.e. the defect count `|D⁺(μ(x_i), μ(u_j))|` is *unbounded* in `i` for
> fixed `j`, faster than any fixed finite correction absorbs.

This is where `osc(ρ₁)` enters: Todorcevic's theorem that `osc(ρ₁(·,α), ρ₁(·,β))` is
**unbounded on a stationary set** is exactly a lower bound on alternation counts, and the
defect `D⁺` between walk floors is governed by those alternations. The construction
would push the oscillation into `D⁺` while keeping the *img-values* (columns) bounded —
the split that Theorem D failed (its kills broke columns) but which walk oscillation,
adding no kills, plausibly respects.

**The two checkpoints, both real and both unverified here.**
1. **Legality survives.** The osc-driven `Σ` must keep `Δ_Σ` (img-value diagonal)
   locally dominated. Oscillation is a floor-structure phenomenon, not an added kill, so
   columns *may* stay bounded — but this needs the actual computation of `Δ_Σ` for the
   walk system, not an assertion. This is the checkpoint Theorem D shows is decisive.
2. **The escape outruns correction in `V`.** Unbounded `osc` gives unbounded defect
   counts, but "unbounded" must be upgraded to "escapes every *frozen finite* `X ∪ F`
   simultaneously across an uncountable family" — a uniformity that unbounded-on-
   stationary should give via a pressing-down, but the pressing-down interacts with the
   `⊑`-comparabilities `x_i ⊑ u_j`, which must be arranged in the walk order.

**Honest status.** Neither checkpoint is discharged here. The target is now *concrete*:
a single osc-escape lemma with two named verification obligations, both of the exact type
that the Walks machinery is built to handle and that this prose cannot responsibly fake.
If (osc-escape) holds with legality, the transport residual is settled **positively in
ZFC** (escapees exist, from any stationary-osc walk sequence). If legality provably fails
for every osc-driver — the columns *always* break when the defect oscillates enough —
that is a theorem pushing hard toward the no-escapee / independence side. Either resolution
is a real result; the fork is now a computation about `ρ₁`, handed off intact.

## 28. Computing Δ_Σ for the walk system: the block-diagonal is unbounded, and checkpoint (1) reframes to a floor-divergence question about ρ₁

Branch-(1) checkpoint (1), done as far as honest walk facts allow. One solid computation,
one definitional correction to §27, and a concrete reduction of the checkpoint — with the
genuinely walk-combinatorial residue flagged, not faked.

**Computation [solid, C-sequence-explicit].** Take `e_β := ρ₁(·, β)` (Todorcevic walks;
coherent and nontrivial). Fix a limit `δ`, block `[δ, δ+ω)`, `λ(δ+m) = δ+ω`. With the
natural `C_{δ+ω} = {δ+n : n < ω}` (cofinal, closed, order type ω), the walk from `δ+ω` to
`δ+m` is the single step `δ+ω → δ+m` (since `δ+m ∈ C_{δ+ω}`), of weight
`|C_{δ+ω} ∩ (δ+m)| = |{δ, δ+1, …, δ+m-1}| = m`. Hence
**`ρ₁(δ+m, δ+ω) = m`** — the sequence's own **block-diagonal `Δ(ξ) = ρ₁(ξ, λ(ξ))` is
unbounded on every block** (linearly, here; robustly unbounded for any cofinal ω-type
`C_{δ+ω}`, since all but finitely many of its points lie in `[δ, δ+ω)`).

*Two consequences, both checkable.* (i) **Block-wild systems are illegal over `ρ₁`** —
their `Δ_Σ` is exactly this unbounded block-diagonal, so Theorem F never applies to the
native walk system. (ii) The walk sequence is **natively wild**: the §21 "kills destroy
BD" phenomenon arises here with *no kills*, intrinsically from the C-sequence — the
oscillation is baked into `ρ₁`'s floors, not added.

*Within-block fixed-coordinate profile [computed].* At a fixed `ξ = δ+m`, for successor
levels `β = δ+m+j` in the block, the walk `β → δ+m` runs down the successors with weights
`|{δ+m+i-1} ∩ (δ+m)| = 0`, so `ρ₁(δ+m, δ+m+j) = 0`; the value jumps to `m` only at the
block-limit `δ+ω`. So the floor value at a fixed coordinate is flat (`0`) across the
block and **spikes at the limit level** — wildness concentrated exactly at limits, which
is exactly where limit-raising pressure lives.

**Correction to §27's checkpoint (1) [definitional].** "The osc-driven `Σ` must keep
`Δ_Σ` locally dominated" was misframed: `Δ_Σ` is *tautologically* locally dominated for
any legal `Σ`, because legality **is** joint-boundedness of the image family below each
`u`, and a joint bound `(γ, s)` gives `Δ_Σ ≤ s =* e_γ` for free. The real legality content
is the joint-boundedness itself: an infinite image family at levels `β_n` has a fiber
bound iff its pointwise sup `sup_n e_{β_n}` is `=*` a floor — i.e. iff `sup_n ρ₁(ξ, β_n)`
is finite at (almost) every `ξ`. That is precisely **no floor-divergence** (§23) = the
finite-fan condition = local realization of `Ψ_Σ` (§24). Legality and schedulability are
the *same* floor-divergence condition, one level apart.

**The checkpoint, reduced to a concrete `ρ₁` question.** A legal *limit-raising* system
over `ρ₁` exists iff some infinite image family at levels `β_n` cofinal in a limit `δ` is
jointly bounded — iff

> **(ρ₁-floor-convergence.)** For stationarily many `δ` and some (equivalently every
> tail-representative) cofinal `⟨β_n⟩ → δ`, is `sup_n ρ₁(ξ, β_n) < ∞` for all but
> finitely many `ξ < δ` — i.e. does `sup_n e_{β_n} =* e_δ`?

The block-diagonal spike (`ρ₁(δ+m, δ+ω) = m`) is the warning sign: floor values *do*
jump at limits, so the sup over levels approaching `δ` can pick up the spikes. Whether it
stays finite is the divergence question, and it is **C-sequence-dependent** walk
combinatorics — the honest boundary of this computation.

**Honest verdict.** The computation is decisive for framing, not for the fork. It shows:
(a) the escapee's raw material — unbounded local wildness — is genuinely present in `ρ₁`,
concentrated at limits; (b) that same wildness is the legality obstruction (spikes break
joint-boundedness), the Theorem-D double-edge now intrinsic; (c) which wins is exactly
`(ρ₁-floor-convergence)`, a concrete divergence computation. If floor-convergence holds
(stationarily), legal limit-raising systems exist and the escapee is live; if it fails
robustly, every legal system over `ρ₁` is tame (`§20 Cor. 2`) and **`ρ₁` is provably not
an escapee** — Φ(ρ₁) in ZFC. The next real step is that single divergence computation for
a concrete C-sequence, which needs Walks ch. 2's `ρ₁` estimates in hand — set up here,
not fabricated.

## 29. The ρ₁-floor-convergence computation: canonical ρ₁ clears checkpoint (1); the residual is confirmed at the forcing level

Done explicitly for the canonical C-sequence. One solid walk computation, one sharpening
of §28's condition, and a clear verdict: checkpoint (1) is *cleared positively* — legal
limit-raising systems exist over canonical `ρ₁` — so the fork lives entirely at
checkpoint (2), the poset ccc / `lim¹` independence. No fabrication; the walk values are
computed, not asserted.

**Walk computation [solid, explicit].** Canonical C-sequence:
`C_{ω·n} = {ω·(n-1)+m : m<ω}`, `C_{α+1} = {α}`, `C_{ω²} = {ω·n : n<ω}`. For
`ξ = ω·k+j` (`0<j<ω`) and `n>k`:
- **`ρ₁(ω·k+j, ω·n) = j`** — the walk `ω·n → ω·(n-1) → ⋯ → ω·(k+1) → ξ` has weight
  `|C_{ω·i} ∩ ξ| = 0` at every high step (ladders sit above `ξ`) and weight
  `|C_{ω·(k+1)} ∩ ξ| = |{ω·k+m : m<j}| = j` at the last. **Constant in `n`.**
- **`ρ₁(ω·k+j, ω²) = max(k+1, j)`** — the walk from `ω²` adds a first step of weight
  `|C_{ω²} ∩ ξ| = |{0, ω, …, ω·k}| = k+1`, then descends as above.

So `sup_n ρ₁(ξ, ω·n) = j < ∞`: **floor-convergence holds.** More: since
`ρ₁(ξ, ω·n) = j ≤ max(k+1,j) = ρ₁(ξ, ω²)`, the defect `D⁺(ω·n, ω²) = ∅` for every `n`.

**Sharpening §28's condition [correction].** §28 said joint-boundedness ⟺ floor-
convergence (`sup_n ρ₁(ξ,β_n) < ∞`). That was slightly loose: floor-convergence makes
`s := sup_n e_{β_n}` a total function, but a *fiber* bound at level `δ` needs
`e_δ ≥ s` off a finite set, i.e. **`⋃_n D⁺(β_n, δ)` finite** (the finite-fan condition at
the limit). Floor-convergence is necessary; `⋃ D⁺` finite is the exact condition. In the
canonical case `⋃_n D⁺(ω·n, ω²) = ∅`, so `e_{ω²}` bounds the whole family
`{e_{ω·n}}`: **the images at levels cofinal in `ω²` are jointly bounded — a legal
limit-raising family.**

**Verdict [computed ⟹ argued].** Over canonical `ρ₁`, **legal limit-raising systems
exist** (checkpoint (1) cleared, positively). So `ρ₁` is *not* excluded from
escapee-hood by tameness — the §20-Cor-2 route does not swallow it. Two riders keep the
honesty exact:
1. The *simplest* such system (everything pumped to `ω²`, `D⁺ = ∅`) is trivially
   schedulable — clearing checkpoint (1) does not produce an escapee, only the *room*
   for one. The escapee still requires a **cross-defective** legal system (`⋃ D⁺` finite
   for the joint bound, yet the cross-terms `D⁺(μ(x_i), μ(u_j))` escaping frozen finite
   correction, §26). That is checkpoint (2), untouched here.
2. The result is C-sequence-specific in the *right* direction: a C-sequence with
   `⋃_n D⁺(β_n, δ)` **infinite** at stationarily many `δ` would have *no* legal
   limit-raising family there, hence only tame legal systems, hence `Φ` and **not an
   escapee** — so the "not an escapee" verdict is *inhabited*, by floor-divergent
   sequences, while canonical `ρ₁` sits on the live side.

**Net.** The computation resolves checkpoint (1) for canonical `ρ₁`: legal wildness is
genuinely available, the residual is not a tameness artifact, and the entire remaining
question is checkpoint (2) — does a cross-defective legal system exist, i.e. is `P(Σ)`
non-ccc-with-V-witness — the `lim¹`/additivity independence, now reached with the ground
below it (checkpoints and legality) fully computed. The walk analysis has taken the fork
as far as ZFC computation can before the forcing dichotomy; the next move is genuinely a
consistency question, not another estimate.

## 30. Checkpoint (2) is the additivity/derived-limit independence: the identification, and the honest terminus

The canonical walk values (§29) live below ω²; a countable initial segment of any
coherent sequence is trivial, so cross-defect structure is invisible there — checkpoint
(2) is inescapably an ω₁-scale question driven by `osc(ρ₁)`, and `osc` unbounded on a
stationary set is Todorcevic's theorem (Walks, ch. 2), cited, not rederived. That places
checkpoint (2) exactly on a mapped independence, and the responsible move is the
identification, graded honestly, not a fabricated forcing proof.

**What is ZFC vs. what is independent [the clean split].**
- *Escapee material exists in ZFC.* Nontrivial coherent sequences on ω₁ exist (Todorcevic
  walks) — `H¹(ω₁) ≠ 0` in the relevant sense. A non-trivializable profile-diagonal
  cochain `Ψ` (locally trivial, globally not; §24) is a ZFC object.
- *The residual is the additivity, not the raw nonvanishing.* Φ(e) asks whether **every
  legally-induced** `Ψ_Σ` trivializes (schedules). That universal-over-legal-systems form
  is an **additivity / derived-limit-vanishing** statement, one quantifier past raw
  nonvanishing — and *that* is where independence lives.

**The identification [argued, structural — the remaining rigorous reduction named].** The
profile-diagonal reformulation (§24) puts the residual in the exact shape of the derived
functor `lim¹` of an inverse system over ω₁: `Ψ_Σ` is a 1-cochain, legality is the
system's coherence/boundedness data, and monotone realization is the coboundary
(vanishing) condition. This is the frame of the **strong-homology / additivity-of-`lim¹`
program**: Mardešić–Prasolov reduced additivity of strong homology to a specific
`lim¹ = 0`; Dow–Simon–Vaughan showed **CH ⟹ `lim¹ ≠ 0`** (additivity fails); and it is
**consistent that `lim¹ = 0`** (additivity holds) via PFA-type and Cohen-model
constructions — Bergfalk, Bergfalk–Lambie-Hanson (*Cohomology of the ordinals*),
Bannister (*Additivity of derived limits in the Cohen model*). The signature is exactly
our §26 trichotomy:

> - **◊ / CH side:** `lim¹ ≠ 0` — a non-trivializable legal cochain, i.e. **the escapee
>   exists** (`P(Σ)` non-ccc with a `V`-witness). Consistent.
> - **PFA / Cohen-model side:** `lim¹ = 0` — every legal cochain trivializes, i.e.
>   **`Φ(e)` for all `e`, no escapee** (`P(Σ)` proper/ccc). Consistent.

Hence **the transport residual is independent of ZFC**, of the same species as strong-
homology additivity. There is no single "solution": the dip-schedulability of coherent
sequences (equivalently the existence of a fiber-order transport escapee) is a `lim¹`-
additivity statement, true under ◊ ("escapee") and false under PFA/the Cohen model
("no escapee"). §15's Theorem C (a non-schedulable sequence under ◊) is the ◊-side made
concrete at the *game* level; the legal, cocycle-level ◊-side escapee is the same
phenomenon in the `lim¹` frame.

**The remaining rigorous work, named precisely (not claimed done).** The identification is
structural — a theorem-to-theorem reduction must match *our* legality (joint-boundedness
of image families, §29's `⋃ D⁺` finite) to the BLH/Bannister inverse system's coherence
data, so that their independence transfers as a proof rather than a resemblance. That is a
paper-scale reduction requiring the strong-homology machinery in hand; it is the honest
next artifact, and it is set-theoretic topology, not another walk estimate.

**Terminus of the program's ZFC/computational phase.** The line is complete up to this
point and each step is a theorem or an honest correction:
- **[machine-checked]** reps ⟺ trivial at ω₁ (Tier 5); Theorem A, Lemma F (`DipSchedule`).
- **[ZFC, proved]** the Φ-completeness of the game (E), the caps (F, §20 Cor 2, G), the
  incidence localization (§22), the finite-fan criterion (§23), the profile-diagonal
  reformulation (§24), the frozen-dip poset with density (§25–26), and the walk
  computations clearing checkpoint (1) (§28–29).
- **[independent, identified]** checkpoint (2) = additivity-of-`lim¹`: escapee under ◊,
  no escapee under PFA/Cohen — the transport residual has no single truth value.

The honest end state: the transport line's original qualitative residual is **resolved in
the only way it can be — as an independence** — reduced (structurally, with the last
reduction named) to the strong-homology additivity program, its ZFC skeleton proved and
machine-checked, its two models identified. Twelve verdict flips, each argument-forced;
the question is handed to set theory not as a mystery but as a located, named instance of
a known independent phenomenon.

## 31. CORRECTION to §30: the lim¹ identification overreached — schedulability is an ORDER realization, not a coboundary (thirteenth flip)

Trying to *finish* the §30 reduction is what exposed its flaw — the honest outcome of the
attempt. §30 identified schedulability with abelian `lim¹` vanishing (strong-homology
additivity). That identification is wrong, and one already-proved theorem refutes it.

**The refutation [proved, from Theorem F].** Schedulability of `Σ` = existence of a
**monotone dominator** `φ` (Theorem E, both directions). Theorem F: over *every* coherent
sequence, including nontrivial ones, block-wild legal systems have a monotone dominator —
they are schedulable. But a nontrivial `e` has `[e] ≠ 0` in `H¹(ω₁)` (ZFC, via walks). If
schedulability were "`[Ψ_Σ] = 0` in the abelian `lim¹`", a schedulable system over
nontrivial `e` could not exist with a cohomologically nontrivial cochain — yet block-wild
is schedulable and its profile diagonal `Ψ_Σ` is `≠*` any floor (`§24`, over nontrivial
`e`). **So schedulability is strictly weaker than / different from cohomological
triviality.** The dominator is a *monotone, order-valued* realization; the abelian
coboundary operation does not preserve monotonicity (a coboundary may decrease). The
correspondence §30 asserted does not hold.

**What this retracts, precisely.**
- §30's "checkpoint (2) = additivity-of-`lim¹`" and "the transport residual is
  independent of ZFC" are **withdrawn**. The strong-homology / Dow–Simon–Vaughan / BLH /
  Bannister results are about ℤ-valued `lim¹` vanishing; our object is a monotone
  realization over the fiber order, and those independence proofs do **not** transfer
  without a correspondence that Theorem F shows fails.
- What stands from §30: nontrivial coherent sequences exist in ZFC (`H¹(ω₁) ≠ 0`), and
  the residual is the *additivity* (universal over legal systems), not the raw
  nonvanishing. But "additivity" here is **order-additivity** (monotone realizability),
  not abelian `lim¹` additivity.

**The correct classification [argued].** The residual is an **order-theoretic /
cofinality** question about the fiber order `D(e)` under legal (countably-bounded)
constraints: does every legal constraint system on the directed set `D(e)` admit a
monotone dominating selection? This is exactly the transfinite-selection /
σ-directed-cofinal-factorization question the transport line *opened* with (§4–§8:
`prefix_bounded_cofinal_factors`, `sigma_directed_cofinal_factors`, the `D3`/`Dm`/`Fb`
witnesses) — now with legality as the constraint and the coherent sequence supplying the
branching. It is a `pcf`/ordered-derived-limit statement, not abelian strong homology.

**Honest status after the correction.** Neither side of the claimed dichotomy is proved:
the ◊-side legal non-schedulable system was **never** established (Theorem D blocked the
natural ◊ construction by showing its pressure illegal), and the PFA-side ccc of `P(Σ)`
was **never** proved. So:

> **The residual is open — genuinely, and its independence status is *unknown*.** It is
> an order-realization / cofinality question over `D(e)`; it may be ZFC-decidable (a
> uniform monotone-selection theorem would give **no escapee** outright) or independent
> (of a `pcf`/coherent-order flavor, *not* the abelian strong-homology flavor §30 named).
> Identifying the exact statement — or proving ZFC-decidability — is the real open
> problem, and §30's citation does not resolve it.

**Trail note.** Thirteenth flip, and the most consequential correction: §30 reached for a
clean "it's independent, here's the reference" resolution, and finishing the reduction
showed the reference does not apply, because schedulability is order-realization not
cohomological triviality — Theorem F, already proved, was the counterexample the whole
time. The honest terminus is *less* closed than §30 claimed: the ZFC skeleton stands and
is machine-checked, checkpoint (1) is cleared, but the final question is an **open**
order-theoretic realizability problem whose independence is not established. Better an
open question correctly classified than a resolution wrongly cited.

## 32. The order-realizability residual, re-grounded: a ZFC sufficient condition, and the triple-evasion that isolates it

Attacking the correctly-classified (§31) order question directly. One clean ZFC positive
result, and a precise location of the residual against the machine-checked §4–§8 order
theory — the frame the transport line opened with, now closed around the exact gap.

**Theorem H (bounded-complete ⟹ no escapee) [proved].** If the fiber order `D(e)` is
**bounded-complete** (every bounded subset has a join), then `Φ(e)` holds: every legal
system has a monotone dominator. *Proof.* Legality makes `{w_p : v_p ⊑ u}` bounded, so its
join `φ(u) := ⊔{w_p : v_p ⊑ u}` exists. `φ` is monotone (`u ⊑ u'` enlarges the set, so
enlarges the join) and dominating (a join is `⊒` each member). ∎ No recursion, no walk
estimate — the whole difficulty is *whether the join exists*.

**The join need not exist [machine-checked witnesses].** `D(e)` for nontrivial `e` is
generally **not** bounded-complete: coherence defects create bounded families with no
least upper bound, exactly the pathology the mathlib-free witnesses isolate —
`Dm_chain_no_sup` (a bounded chain with two incomparable minimal upper bounds `L, R`, no
join) and `Fb`'s `fb_no_minimal_ub` (a bounded family with *no* minimal upper bound at
all). So Theorem H's hypothesis genuinely fails, and the join-route does not settle `Φ(e)`
in general.

**But non-bounded-completeness is not enough for an escapee — the three sufficient
routes.** The same witnesses factor anyway, by *other* means:
- `Dm_factors`: `Dm` has no join for its chain, yet **a top `⊤` overshoots** every family
  — factorization via overshoot.
- `fb_factors`: `Fb` has no minimal upper bound, yet **a cofinal `ω`-ruler** dominates —
  factorization via a ruler (the `prefix_bounded_cofinal_factors` / σ-directed route).

So a directed order factors (no escapee) if **any** of: (a) it is bounded-complete
(joins, Theorem H); (b) it has a top / overshoot (`Dm`); (c) it carries a cofinal
monotone ruler (`Fb`, σ-directed, prefix-bounded). These are the machine-checked
sufficient conditions from §4–§8.

**The triple evasion — why `D(e)` is exactly the residual [argued].** For nontrivial `e`,
the fiber order `D(e)` evades all three at once:
- **not bounded-complete** — coherence defects give `Dm`/`Fb`-type bounded families with
  no join (the minimal-UB gap, locally);
- **no top / no overshoot** — `D(e)` is unbounded (every element has a strict successor);
- **no cofinal ω₁-ruler** — nontrivial `e` has no `⊑`-chain with cofinal levels
  (`Lemma D`), so no global monotone ruler.

`D(e)` sits precisely at the point where all three known sufficient conditions fail
simultaneously. That is the sharp reason it is the residual — and it re-anchors the whole
question to the order theory the transport line began with, not to cohomology.

**The honest open core, order-theoretically exact.**

> **`Φ(e)` open form.** Does a directed order that is simultaneously *not* bounded-complete,
> *top*-less, and *ruler*-less nonetheless admit a monotone dominator for every legal
> (down-set-bounded) constraint system — via *selection among incomparable minimal upper
> bounds*, coherently across the branching? A ZFC "yes" (a fourth sufficient condition
> covering the triple-evasion case) settles **no escapee**; a legal system realizing the
> minimal-UB obstruction cofinally settles **escapee**.

This is a genuine order/cofinality problem — a monotone-thread / ordered-inverse-limit
existence question (the correct non-abelian analog, §31) over an ω₁-directed-with-
countable-down-sets order lacking joins, tops, and rulers. Its ZFC status is **open and
unknown**. The transport line has thus returned, sharpened and with a machine-checked
skeleton, to the exact order-theoretic gap it started from: the escapee, if it exists, is
a legal constraint system witnessing that *selection among coherence-defect minimal upper
bounds cannot be made monotone* — the one thing the `Dm`/`Fb` overshoot and ruler routes
cannot rescue when there is no top and no ω₁-chain.

## 33. Trying the fourth sufficient condition: D(e) is a lattice, the selection reduces to countable joins, and the route stalls at the machine-checked gap

The honest attempt to prove "legality + countable down-sets ⟹ monotone selection ⟹ no
escapee." A new structural fact, a clean reduction, and a precise finding: the natural
routes all stall at the countable-join / minimal-UB gap — machine-checked to be real — so
this proof does **not** close, and the balance tips toward the escapee being live.

**Structural fact [proved]: `D(e)` is a lattice.** Binary joins were known (pointwise max,
`=* e_{max}`, by coherence). Meets too: `(α,s) ∧ (β,t) := (min(α,β), pointwise min)` is the
greatest lower bound and `=* e_{min}` (coherence: `s`, `t↾α` are both `=* e_α`, so their
min is). So **finite** joins and meets always exist. The bounded-completeness gap (§32) is
therefore located *precisely* at **countable** joins: `D(e)` is a lattice that is not
`ω`-join-complete.

**The selection reduces to countable joins [argued].** Build `φ` by recursion on an
enumeration `D(e) = {u_ξ}`, maintaining monotonicity. At stage `ξ`, `φ(u_ξ)` must be an
upper bound of `M(u_ξ) := {w_p : v_p ⊑ u_ξ}` (bounded, by legality) that lies `⊒` every
processed lower `φ(u_η)` (`u_η ⊑ u_ξ`) and `⊑` every processed upper `φ(u_η)`
(`u_ξ ⊑ u_η`). The upper constraints are handled by *meets* (which exist, finitely; the
processed uppers below a bound are fine). The lower constraints require an element `⊒`
the set `M(u_ξ) ∪ {φ(u_η) : u_η ⊑ u_ξ}` — a **countable** set (subset of a countable
down-set-image), **bounded** (legality + induction). Its least such element is its
**countable join**. Zorn's-lemma and maximal-partial-selection variants reduce to the
same point. So the recursion is feasible at `u_ξ` iff the relevant countable join exists.

**The route stalls [machine-checked gap].** Countable bounded joins **do not exist** in
general: `Dm_chain_no_sup` is a countable bounded chain with two incomparable minimal upper
bounds and no join; `fb_no_minimal_ub` is worse. And the stall is not rare — every element
of `D(e)` has an infinite down-set, so essentially every stage asks for a countable join of
the processed lower values. **Legality + countable down-sets does not supply these joins**;
that is exactly the bounded-completeness Theorem H assumed and §32 showed can fail. The
fourth-sufficient-condition proof, by this route, **does not close.**

**Clean reformulation [proved]: factoring = joins land in `D(e)`, not its completion.** The
ideal completion `Idl(D(e))` *is* bounded-complete (all bounded joins exist as ideals), so a
monotone dominator into `Idl(D(e))` always exists — `φ(u) := ⊔ M(u)` taken in `Idl`. Thus:

> **`Φ(e)` ⟺ this ideal-valued dominator can be taken to land in `D(e)` itself** — i.e. the
> required countable joins are *fiber elements*, not proper ideals. The escapee exists iff
> some legal system forces the dominator to rely on a proper ideal — a
> **coherence-defect "missing minimal upper bound"**, an ideal point of `Idl(D(e)) \ D(e)`.

The missing points of the completion are exactly the `Dm`/`Fb` gaps: bounded families whose
"join" is an ideal with no fiber realization. So the escapee is precisely a legal system
whose induced bounds are cofinally *ideal*, never fiber.

**Honest verdict.** The attempt does not prove the fourth sufficient condition; it shows
the natural routes (recursion, Zorn, join) all reduce to countable-join existence, which
legality + countable down-sets does **not** force — the obstruction is the machine-checked
countable-join / minimal-UB gap, active at essentially every stage. This is genuine
evidence that **no-escapee does not follow from these hypotheses**, tilting toward the
escapee being live: an escapee would be a legal system driving the dominator into proper
ideals cofinally. It is not a proof of the escapee — a route failing is not impossibility —
but it relocates the entire question to a sharp, `Dm`/`Fb`-anchored form: **can a legal
constraint system force cofinal reliance on ideal (non-fiber) joins over a nontrivial
`D(e)`?** That is the open problem, and it is now purely about coherence-defect minimal
upper bounds — the object the machine-checked witnesses were built to probe.

## 34. A legal family with a proper-ideal join, explicit over canonical ρ₁ — the ingredient Theorem D lacked

Constructing the escapee's local ingredient: a legal constraint family whose only join is
an ideal, not a fiber element — the reliance §33 identified. It exists **explicitly over
canonical ρ₁, with no kills**, so it is legal where Theorem D's kill-driven version was
not. One concrete construction, one anti-overclaim check, one honest remaining gap.

**The construction [proved, explicit].** Canonical ρ₁, levels `ω·n → ω²`. From §29,
`e_{ω·n}(ω·k+j) = j` (for `k < n`) while `e_{ω²}(ω·k+j) = max(k+1, j)`. So for `j < k`
there is a value-gap `(j, k+1]` between floor and bound. Define fiber elements
`c_n := (ω·n, s_n)` by
`s_n(ω·k+j) := j+1` when `j < k < n`, and `s_n := e_{ω·n}` elsewhere.
- *Each `c_n` is a fiber element*: `s_n` deviates from `e_{ω·n}` only on
  `{ω·k+j : j < k < n}`, which is **finite**. ✓
- *The `c_n` form a `⊑`-chain*: for `ξ = ω·k+j` shared by `c_n, c_{n+1}`, both give
  `j+1`; elsewhere both are the floor. So `s_n ≤ s_{n+1}↾ω·n`. ✓
- *Bounded by `e_{ω²}` (legal!)*: `s_n(ω·k+j) = j+1 ≤ k+1 = e_{ω²}(ω·k+j)` for `j<k`, and
  `s_n = e_{ω·n} ≤* e_{ω²}` elsewhere. So `c_n ⊑ (ω², e_{ω²})` for all `n`. ✓
- *The join is a proper ideal*: `s_ω := sup_n s_n` has `s_ω(ω·k+j) = j+1` for all `j < k`.
  This deviates from `e_{ω²}(ω·k+j) = k+1` on the **infinite** set `{ω·k+j : j+1 < k+1}`,
  and matches no other floor (no fiber element takes value `j+1` at cofinally many
  `ω·k+j`). So `s_ω` is **not `=*` any floor — not a fiber element**; the join lives only
  in `Idl(D(e))`. ✓

So `M := {c_n}` is a **legal** family (bounded by `e_{ω²}`) whose join is a **proper
ideal**. The reliance of §33 is real, concrete, and — crucially — needs **no kills**: it
rides the intrinsic value-gaps of `ρ₁`'s floors (`§28`'s block-diagonal spikes seen from
below), which is exactly why it stays legal where Theorem D's binary kills broke column-
boundedness.

**Anti-overclaim check [proved].** One might hope §29's floor-convergence gives bounded-
completeness (⟹ Theorem H ⟹ no escapee). It does **not**: the obstruction is the
**downward** defect. `⋃_n D⁻(ω·n, ω²) = ⋃_n {ξ : e_{ω²}(ξ) > e_{ω·n}(ξ)} =
{ω·k+j : k+1 > j}` is **infinite** — that infinite set is precisely the room the chain
climbs into, and precisely why `s_ω` deviates infinitely. Floor-*convergence* (upward,
`§29`) and floor-*co-divergence* (downward, here) are independent; the latter breaks
bounded-completeness even when the former holds. Theorem H does not apply to canonical
`ρ₁`, and the shortcut to no-escapee is closed.

**The remaining gap [honest].** A single legal ideal-join family is **not** an escapee:
its fiber bound `e_{ω²}` dominates it, so `φ(u) := e_{ω²}` schedules this one `M`. The
escapee needs **cofinally many** such families, cross-conflicting so that no *monotone*
fiber choice of bounds threads them — the §26 cross-defective configuration. That global
threading is the open part, and it is where osc-coherence (or a forcing) must enter.

**Verdict — the escapee-live side is materially strengthened.** The local ingredient — a
legal family forced onto an ideal join — is now **explicit, kill-free, and legal over
canonical `ρ₁`**. This is exactly the piece Theorem D could not supply legally: the
legality wall that stopped the kill construction does **not** stop the value-gap
construction. What remains is not "can the obstruction be made legal" (yes, done here) but
"can legal ideal-reliances be threaded into a cofinal cross-conflict" — the §26 poset/
osc problem, now the sole surviving obstacle to an outright escapee. The construction has
moved the frontier from *legality of the ingredient* (settled: legal) to *coherence of the
global conflict* (open), which is genuine forward motion on the escapee side.

## 35. CORRECTION to §29/§34: the canonical C-sequence gives a TRIVIAL ρ₁ — the escapee needs a nontrivial (oscillating) C-sequence (fourteenth flip)

Setting up the cofinal placement forced the check I should have run at §29: is the
canonical-C `ρ₁` even nontrivial? It is **not**. §29 and §34 were computed on a trivial
sequence. The mechanisms are correct; the sequence was the wrong one for an escapee.

**The triviality [proved].** For the canonical local-ladder C-sequence
(`C_{ω·n} = {ω·(n-1)+m}`, ladders staying in their block), the walk from any `γ` above
`ξ`'s block funnels down through `λ(ξ) → ξ`, so `ρ₁(ξ, γ)` **stabilizes**: for
`ξ = ω·k+j`, `E(ξ) := sup_γ ρ₁(ξ, γ) = max(k+1, j) < ∞` (high steps have weight 0; only
the block-entry `k+1` and final descent `j` survive). And `E` **trivializes** `e`:
`E↾α =* e_α`, because `E(ξ) ≠ e_{ω·n}(ξ) = j` only for `ξ = ω·k+j` with `j ≤ k < n` —
finitely many below each `ω·n`. So `E↾ω·n =* e_{ω·n}`, and by cofinality `E↾α =* e_α` for
all `α`. **Canonical `ρ₁` is trivial.** (A very regular C-sequence yields a trivial walk;
nontriviality of `ρ₁` requires a genuinely oscillating C-sequence — an Aronszajn/ladder
structure — not the nested-local one.)

**What this invalidates, and what stands.**
- *Invalidated as escapee-relevant:* §29's "floor-convergence holds over canonical `ρ₁`"
  and §34's "legal ideal-join family over canonical `ρ₁`" are computations on a **trivial**
  sequence. A trivial sequence is schedulable (Theorem A) — no escapee — so the §34 family,
  while a genuine legal family with an ideal join, is dominated by the trivialization and is
  **not** an escapee ingredient. The "checkpoint (1) cleared over canonical `ρ₁`" (§29) is
  the trivial baseline, not information about the nontrivial case.
- *Stands (all C-independent):* Theorem H (bounded-complete ⟹ no escapee); `D(e)` is a
  lattice (§33); the ideal-completion reformulation (`Φ(e)` ⟺ the ideal dominator lands in
  `D(e)`, §33); the *mechanism* of the value-gap construction (§34) — a bounded chain with
  accumulating deviations has an ideal join. These do not depend on which C-sequence, only
  on `e`'s abstract coherence.

**The escapee genuinely requires oscillation [reframing].** Over a **nontrivial** `ρ₁`
(oscillating C-sequence), floor values `ρ₁(ξ, γ)` are **unbounded in `γ`** at cofinally
many `ξ` — there is no stable `E(ξ)`, no trivialization; that unbounded incoherent growth
*is* `osc(ρ₁)`. The value-gap mechanism of §34 then has genuinely wild bounds (the "next
absorbing floor" `e_{Λ(u)}` climbs without a stable ceiling), and it is exactly there that
cofinally many families can be placed with **conflicting** bounds — because there is no
trivialization to thread them through. So the cofinal-placement construction is confirmed
to live **strictly in the nontrivial/oscillating regime**, and it needs the C-sequence's
oscillation as its engine — the Walks-ch.-2 machinery flagged since §27, not the canonical
computation.

**Honest verdict.** The placement attempt did not produce a conflict over the sequence I
was using, for the decisive reason that that sequence is **trivial**. This is the correct,
if humbling, outcome: §29–§34's canonical-C computations were the trivial baseline
throughout, and the escapee — if it exists — requires a nontrivial oscillating `ρ₁` where
the value-gap families' bounds have no common trivializing ceiling. The construction is
back at the oscillation frontier, now with the *reason* sharp: an escapee is a cofinal
family of value-gap ideal-reliances whose absorbing floors `e_{Λ}` cannot be monotonically
threaded precisely because `osc` denies a stable ceiling. Whether `osc` forces that is the
open question — genuinely at the Walks/independence boundary, and not settled by canonical
computation. Fourteenth flip: caught by checking triviality before building on it.

## 36. The residual IS Todorcevic's cofinal-types independence: the correct (Tukey) frame — literature research

Research (not reconstruction). The order-realizability residual (§31–§35) is a
**cofinal-type / Tukey** question about the ℵ₁-directed fiber order — and it is a *known,
deep, order-theoretic independence*, exactly the category §31 predicted after retracting
§30's abelian-`lim¹` overreach. Sourced from the literature below.

**The literature fact [Todorcevic, sourced].** For directed sets of size `≤ ℵ₁` under the
Tukey order (`D ≤_T E` iff a map sends unbounded sets to unbounded sets — i.e. a monotone
cofinal reduction):
- **Under PFA**: there are *exactly five* cofinal types — `1, ω, ω₁, ω×ω₁, [ω₁]^{<ω}`
  (Todorcevic's classification; `[ω₁]^{<ω}` is the maximum).
- **Under CH**: there are `2^{ℵ₁}` cofinal types (Todorcevic) — a wild zoo, realized by
  coherent/Aronszajn-tree structures.

This is *the* independence of the cofinal structure of ℵ₁-directed sets.

**The identification [argued — and in the correct category].** The fiber order `D(e)` of a
coherent sequence has size `ℵ₁` (ω₁ levels × countably many finite modifications each) and
is directed. A **monotone dominator** for a legal constraint system *is* a Tukey reduction
witnessing that `D(e)` is cofinally tame; the **escapee** is `D(e)` carrying a legal
constraint family that no monotone map dominates — i.e. `D(e)` sitting at a *wild* cofinal
type. So:

> - **PFA side:** every ℵ₁-directed set — `D(e)` included — is Tukey-equivalent to one of
>   the five tame types. The cofinal structure is *completely classified*; there is no wild
>   type, so no wild escapee. Everything factors up to the `[ω₁]^{<ω}` ceiling.
> - **CH side:** `2^{ℵ₁}` cofinal types exist, the wild ones built from exactly
>   coherent-sequence / tree structures like `D(e)`. A nontrivial coherent sequence's fiber
>   order can be a wild type — **an escapee.**

Hence the transport residual is **Todorcevic's cofinal-types independence**: escapee under
CH, tame under PFA — an *order-theoretic* (Tukey) independence, not the abelian
strong-homology one.

**Why this frame is correct where §30's was not [the decisive check].** §30's `lim¹` frame
was refuted by Theorem F (block-wild legal systems over nontrivial `e` are schedulable
while `[e] ≠ 0`), because schedulability is a *monotone order* realization, not an abelian
coboundary. The **Tukey** frame is *exactly* the monotone-order category — a Tukey
reduction is a monotone cofinal map — so Theorem F is no objection at all: it merely says
*some* constraint systems on `D(e)` are dominated (don't witness the maximal cofinal type),
which is normal — a directed set's Tukey type is witnessed by *particular* unbounded
families, not all of them. The frame that Theorem F killed (abelian `lim¹`) and the frame
that survives it (Tukey cofinal types) are different categories, and only the second is the
one our objects live in. §31 called this correctly ("pcf/coherent-order flavor, not
strong-homology"); the Tukey classification is that flavor, named.

**Closure of the line.** The transport calculus *opened* (§4–§8) as an order question —
dcpo/cofinal-factorization of directed sets, with the machine-checked witnesses `D3`, `Dm`,
`Fb` as small cofinal-type examples (`Dm` not a dcpo yet factoring via `⊤`; `Fb` factoring
via a ruler — these are Tukey-tameness witnesses). It detoured through cohomology (§24, §30)
and was corrected back to order theory (§31). It now lands, sourced, on its true home:
**the cofinal-type theory of ℵ₁-directed sets, whose independence (5 under PFA, `2^{ℵ₁}`
under CH) is exactly the escapee's independence.** The whole arc — Lipschitz/Hölder/
Dobrushin quantitative tiers, then the qualitative dcpo residual — was a Tukey question from
the first, and the residual is a *named, deep, decades-old independence* in Todorcevic's
program.

**Honest remaining work [named].** The exact reduction — that a *specific* legal constraint
system on `D(e)` realizes a wild cofinal type under CH (and that PFA-tameness implies every
legal system is dominated) — must be written to make "escapee ⟺ wild Tukey type" a theorem
rather than a (correct-category) identification. That is a reduction to Todorcevic's cofinal
types, tractable because the category is right. But the meta-question is now *answered*: the
residual is independent of ZFC, order-theoretically, and the reference is Todorcevic's
cofinal-types classification — this time in the category that survives Theorem F.

Sources: Todorcevic, *Directed sets and cofinal types* (Trans. AMS, 1985) and the PFA
five-types classification; the CH `2^{ℵ₁}`-types result; surveyed in "The Tukey Order and
Subsets of ω₁" (arXiv:1608.00319) and the cofinal-types literature (arXiv:2108.03701,
2211.13361).

## 37. The exact reduction, attempted: Φ is finer than the Tukey type — the bridge to PFA/CH is the realization poset, not a citation (fifteenth flip, refining §36)

Writing the reduction `Φ(e) ⟺ D(e)` tame-Tukey exposed a real gap: **`Φ` is not a coarse
function of the Tukey type.** §36 correctly identified the *category* (Tukey / cofinal
types) and the *independence* (PFA tame / CH wild), but the exact reduction is not a
citation. Here is what is solid, where it breaks, and the correct bridge.

**Solid: the three routes give Φ [proved].** A directed set `D` has `Φ` (every legal
constraint system has a monotone dominator) if it has any of:
- a **top** `⊤`: take `φ ≡ ⊤` (Dm's route — `Dm` has `Φ` though it is not bounded-complete);
- **bounded-completeness**: `φ(u) := ⊔ M(u)` (Theorem H);
- a **cofinal ruler**: dominate along the chain (`Fb`'s route).

**Solid: all five PFA-tame types have Φ [proved].** `1` (top); `ω`, `ω₁`, `ω×ω₁`,
`[ω₁]^{<ω}` are each **bounded-complete** — in `[ω₁]^{<ω}` a bounded set is `⊆ P(F)` for
finite `F`, hence finite, so `⊔ M(u) = ⋃ M(u)` is finite and in the set. So every tame type
has `Φ`.

**The gap: Φ is finer than the Tukey type [the obstruction].** The reduction needs `Φ`
downward-Tukey-closed (`D ≤_T E`, `Φ(E) ⟹ Φ(D)`). But `Φ` depends on **bounded-
completeness**, which is *not* Tukey-invariant: `D(e)` for nontrivial `e` is **not**
bounded-complete (the `Dm`/`Fb` coherence-defect gaps, §32–33), yet under PFA it is
`≡_T [ω₁]^{<ω}`, which **is** bounded-complete. Tukey-equivalent, different bounded-
completeness. So `Φ(e)` is **not** read off the Tukey type by the bounded-completeness
route, and §36's "`Φ(e)` = cofinal-type" was optimistic: the cofinal type is a *coarser*
invariant than `Φ(e)`. (Whether `Φ` is Tukey-invariant by some *other* argument is itself
open — the honest crux lemma of any citation-style reduction.)

**The correct bridge: the realization poset, not the classification [the actual reduction].**
`Φ(e)` connects to PFA/CH through the **frozen-dip realization poset `P(Σ)`** (§25–26), not
through Todorcevic's classification directly:
- **Under PFA (properness side):** if `P(Σ)` is proper for every legal `Σ`, then a generic
  realization exists and — meeting `ℵ₁` dense sets — `Φ(e)` holds. PFA making these
  coherent-selection posets proper is the *same* phenomenon that collapses the cofinal
  types to five; both are PFA killing wild ℵ₁-combinatorics. **PFA ⟹ no escapee**, via
  `P(Σ)` properness.
- **Under CH (proliferation side):** CH builds `2^{ℵ₁}` cofinal types and, by the same
  coherence-oscillation, legal `Σ` with `P(Σ)` non-ccc *and a `V`-witness* — an escapee.
  **CH ⟹ escapee**, via `P(Σ)` failure.

So `Φ(e)` is governed by the **PFA/CH independence**, and Todorcevic's cofinal-types
classification is its *parallel face* (same axioms, same wild-`ℵ₁`-combinatorics engine) —
but the reduction runs through `P(Σ)`-properness (an order/forcing statement about `D(e)`
directly), **not** through a Tukey-type equality that `Φ`'s finer-than-Tukey nature forbids.

**Honest status of "the exact reduction."**
- **[proved]** the three Φ-routes; all five tame types have `Φ`; `D(e)` not bounded-complete.
- **[proved-structural]** `Φ(e) ⟺ P(Σ)` realizable for all legal `Σ` (Theorem E + §25 density).
- **[argued, sourced parallel]** PFA ⟹ `P(Σ)` proper ⟹ `Φ(e)` (no escapee); CH ⟹ `P(Σ)`
  failure ⟹ escapee — the same independence classifying cofinal types.
- **[open lemma]** whether `Φ` is a genuine Tukey invariant (would upgrade the parallel to a
  literal "`Φ(e)` = tame cofinal type" reduction). Not established; possibly false, since
  bounded-completeness is finer than the cofinal type.

**Net (refining §36).** §36's frame is right — order-theoretic, PFA/CH-independent — and its
category (Tukey) is the one that survives Theorem F. But the *exact* reduction is **not**
"`Φ(e)` equals the Tukey type"; it is "`Φ(e)` ⟺ `P(Σ)` realizable, governed by the
PFA/CH independence, of which the cofinal-types classification is the parallel face." The
residual is independent of ZFC (PFA: no escapee; CH: escapee), proved-structurally through
the realization poset; the literal cofinal-type identification carries a genuine open lemma
(Tukey-invariance of `Φ`) that this pass does **not** fabricate. Fifteenth flip: attempting
the exact reduction found `Φ` finer than the cofinal type, and relocated the bridge to
`P(Σ)`-properness — the honest, order-theoretic, forcing-axiom form.

## 38. Theorem I: Φ(D) ⟺ a monotone dominating retraction of the σ-ideal completion — the three routes unified, the escapee sharpened

The breakthrough is structural: the messy "three sufficient routes" (§32) and the
machine-checked witnesses (`Dm`, `Fb`, the ruler) are **one condition** — `D` retracts,
monotonically and dominatingly, off its own σ-ideal completion. This is the clean form of
`Φ`, and it makes the escapee a single sharp object.

**Setup.** For a directed set `D`, let `Idl_σ(D)` be the countably-generated bounded
ideals — exactly the objects `⊔ M(u)` for legal systems (`M(u)` is countable and bounded,
§33). `ι : D ↪ Idl_σ(D)`, `d ↦ ↓d`. A **dominating retraction** is a monotone
`r : Idl_σ(D) → D` with `r(I) ⊒ I` (an upper bound of the ideal) and `r(↓d) = d`.

**Theorem I [⟸ proved; ⟹ argued].** `Φ(D)` holds **iff** `D` admits a monotone dominating
retraction `r : Idl_σ(D) → D`.
- *(⟸) [proved].* Given `r`, for any legal `M` set `φ(u) := r(I_M(u))` where `I_M(u)` is
  the ideal generated by `M(u)` (monotone in `u`; bounded, so in `Idl_σ`). Then `φ` is
  monotone (`r`, `I_M` monotone) and `φ(u) = r(I_M(u)) ⊒ I_M(u) ⊇ M(u)`. So `φ` is a
  monotone dominator; `Φ(D)` holds. ∎
- *(⟹) [argued].* Legal systems `M : D → Idl_σ(D)` are exactly the monotone maps into the
  completion; `Φ(D)` gives each a dominator, and amalgamating over a cofinal/universal
  family yields `r` on `Idl_σ(D)` (the step needing care — the honest gap in ⟹).

**The three routes are the three standard retractions [proved].** §32's sufficient
conditions are exactly the three natural dominating retractions, and the machine-checked
witnesses realize them:
- **Top**: `r(I) := ⊤` — constant, dominates all (`Dm`'s route; `Dm_factors`).
- **Bounded-complete**: `r(I) := ⊔ I` — the join lands in `D` (Theorem H).
- **Ruler** (cofinal chain `⟨c_ξ⟩`): `r(I) := c_{ξ(I)}`, `ξ(I) :=` least with `c_ξ ⊒ I`
  (`I` bounded ⟹ exists, by cofinality) — this is *literally*
  `wruler_defeats_bounded_escapee` (`Fb`'s route, machine-checked).

So the three routes, the `Dm`/`Fb` witnesses, and Theorem H are one theorem: **each is a
dominating retraction of `Idl_σ(D)`**, and any of them gives `Φ`.

**The escapee, sharpened to one object.** `¬Φ(D)` (an escapee) ⟺ **`Idl_σ(D)` admits no
monotone dominating retraction onto `D`** — `D` is not a "dominating monotone retract" of
its σ-ideal completion. For `D(e)`, `Idl_σ(D(e))` adds exactly the coherence-defect ideal
points (the `Dm`/`Fb` missing joins, the §34 accumulating-deviation ideals). A dominating
retraction must send each such ideal point *monotonically* back into `D(e)`, above it. The
escapee is precisely the failure of this single monotone map to exist.

**Why this is the clean form of the independence.**
- *Retraction ⟺ realization.* The retraction `r` is exactly a global, coherent choice of
  the `P(Σ)` bounds (§25) — one monotone map instead of a per-system schedule. `Φ(D) ⟺`
  the retraction exists `⟺ P(Σ)` realizable for all legal `Σ`.
- *PFA:* the retraction is added generically (the coherence-defect ideals are threaded by
  a proper poset) — **retraction exists, no escapee**.
- *CH:* the coherence-defect ideals oscillate so that no single monotone map threads them
  in `V` — **no retraction, escapee**.

**Status.** Theorem I (⟸ + the three-route unification) is **proved** and is the genuine
structural gain: `Φ` is *one* condition — a dominating monotone retraction of the σ-ideal
completion — not a disjunction of three, and the machine-checked `Dm`/`Fb`/ruler witnesses
are its three canonical instances. The escapee is now a single, sharp object (the missing
retraction), whose existence is the PFA/CH independence via `P(Σ)`. The `⟹` amalgamation
and the independence itself remain as the named open work — but the *form* of the question
is now as clean as it can be: **is `D(e)` a dominating monotone retract of `Idl_σ(D(e))`?**

## 39. The backward direction is a uniformization gap; the completion is Tukey-invisible — retraction is strictly finer than Φ (and than Tukey)

Working Theorem I's `⟹` and the independence. Two genuine results: a clean fact (the
σ-ideal completion does not change the Tukey type) and an honest correction (the `⟹` does
not follow — the retraction is a *uniform* strengthening of per-system `Φ`). This refines
§38 and pins the independence's exact shape.

**Fact [proved]: `D ≡_T Idl_σ(D)`.** The embedding `ι : D → Idl_σ(D)`, `d ↦ ↓d`, has
cofinal image: every `I ∈ Idl_σ(D)` is bounded by some `b ∈ D` (legality of its generating
family), so `I ⊆ ↓b = ι(b)`, i.e. `I ≤ ι(b)`. A monotone embedding with cofinal image is a
Tukey equivalence. **The completion is Tukey-invisible.**

**Correction to §38's `⟹` [the uniformization gap].** `Φ(D) ⟹` retraction does **not**
follow from per-system dominators:
- `Idl_σ(D)` has *more ideals than `D` has elements* (countably-generated bounded ideals
  number up to `2^{ℵ₀}` for `|D| = ℵ₁`), so **no single `D`-indexed legal system has all
  ideals in its image** — the "universal system" that would produce `r` does not exist.
- Per-system `Φ` gives, for each legal `M`, a dominator `φ_M`; but different systems sharing
  an ideal `I` (as `M(u) = I`) may dominate it by *incomparable* values `φ_M(u)`, with no
  coherent global choice `r(I)`. Assembling `r` needs a **monotone dominating selection on
  the ideal lattice `Idl_σ(D)` itself** — which is a `Φ`-type condition one level up, not
  delivered by `Φ(D)`.

So **Theorem I is honestly one-directional**: *retraction `⟹ Φ`* [proved, §38]; the
converse *`Φ ⟹` retraction* is a genuine uniformization, **open** (and plausibly false —
the retraction is strictly stronger). Restated cleanly:

> **Retraction exists `⟹` `Φ(D)` (no escapee)** [proved]. Contrapositive: **escapee
> `⟹` no dominating retraction** [proved]. The reverse (*no retraction `⟹` escapee*) is
> the open uniformization gap.

**Structural payoff — the escapee is finer than Tukey, with a clean mechanism.** Since
`D ≡_T Idl_σ(D)`, a dominating retraction is `D` retracting off a set *Tukey-equivalent to
itself*. Tukey-equivalence gives a Tukey *reduction* `Idl_σ(D) → D`, but a *monotone
dominating retraction* is strictly more (monotone + dominating + fixing `D`). The escapee
is exactly the gap between "Tukey-equivalent" (always) and "dominating monotone retract"
(the question) — which is precisely why `Φ` is **finer than the Tukey type** (§37), now
with the mechanism named: *`D` and its completion are Tukey-equal but the completion may
not monotonically dominating-retract onto `D`.*

**The independence, its exact shape [honest].** Both sides are forcing constructions,
stated precisely as the remaining work; neither is prose-provable here:
- **PFA side (no escapee):** the frozen-dip poset `P(Σ)` — whose generic *is* a dominating
  retraction restricted to `Σ`'s ideals — is proper for every legal `Σ`; PFA then supplies
  the retraction. The theorem to prove: *`P(Σ)` is proper (ZFC or under PFA-friendly
  hypotheses)*. This is the coherent-selection-poset properness, the same engine that
  collapses cofinal types to five.
- **CH side (escapee):** the coherence-defect ideals of `Idl_σ(D(e))` oscillate (via
  `osc`) so that no monotone map threads them in `V`; a `V`-generic obstruction — the
  standard CH proliferation of wild cofinal types — yields a legal `Σ` with no dominating
  retraction. The theorem to prove: *under CH, some nontrivial `e` has a legal `Σ` whose
  ideal-family admits no monotone dominating selection*.

**Net.** Theorem I is a *proved sufficient condition* (retraction `⟹` no escapee) unifying
the three routes and the machine-checked witnesses; its converse is an honest open
uniformization. The new clean fact `D ≡_T Idl_σ(D)` explains, mechanistically, why `Φ` is
finer than the Tukey type. The independence is two precisely-stated forcing theorems
(`P(Σ)` proper; CH obstruction), which is where prose ends and model construction begins.
The form is now exact: **does `D(e)` dominating-monotone-retract off its Tukey-equal σ-ideal
completion? — no under CH, yes under PFA, both to be shown by forcing.**

## 40. The PFA proof, written to its core: Δ-system reduction to one oscillation lemma

The user asked for the PFA proof. Here it is, run as far as it honestly goes — and it does
*not* bottom out in hand-waving: it reduces, rigorously, to a single named lemma, which is
the technical heart of Todorcevic's ω₁ theory. I state that lemma exactly and cite it; I do
not reprove it, and I say plainly which step is cited.

**Poset.** Fix legal `Σ`, `γ := μ` (frozen, monotone — no level inversions). Conditions
`p = (d, X, F)`: finite `d ⊆ D(e)`; `X, F : d → [ω₁]^{<ω}` (dips, promises); for `x ⊑ u` in
`d`, `D⁺(μx, μu) \ X(x) ⊆ F(u)`. Extension freezes `X, F`.

**Density [proved, ZFC].** For each `w`, `{p : w ∈ d}` is dense: given `p`, add `w` with
`X(w) := ⋃_{u ∈ d, w ⊑ u}(D⁺(μw, μu) \ F(u))` (finite) and a fresh `F(w)`. `D(e)` being a
lattice (§33) supplies the finite joins/meets to keep `μ`-monotonicity; no axiom used.

**A generic filter yields `Φ` [proved, this is `phi_of_generic`].** A filter meeting the
`ℵ₁` density sets `{w ∈ d}` gives a total monotone dominator (frozen promises keep each
leftover `L_u ⊆ F_u` finite). So `Φ(e)` follows from: *a filter meeting `ℵ₁` dense sets
exists* — which MA_{ℵ₁}/PFA supplies **if the poset is ccc/proper.**

**ccc/properness ⟹ the reduction [proved, ZFC].** Take `{p_ξ : ξ < ω₁}`. By the Δ-system
lemma applied to the supports (domain elements ⊆ `D(e)` together with all ordinals in the
`X, F` values), refine to an uncountable canonical family: common root `r`, disjoint stalks
`a_ξ`, identical `X, F` on `r`, order-isomorphic stalk-data, and (pressing down on stalk
levels) stalk levels strictly increasing in `ξ`. By the **amalgamation lemma**
(`compat_of_crossMono`, machine-checked) two such `p_ξ, p_η` are compatible **iff** the
cross-constraints hold: for `x ∈ a_ξ`, `u ∈ a_η` with `x ⊑ u`,
`D⁺(μx, μu) \ X(x) ⊆ F(u)` (and the symmetric clause). Root-agreement and domination are
already secured. So ccc `⟺` **some pair `ξ < η` fits its cross-defects.**

**The core [cited — Todorcevic; NOT reproved here].**

> **Cross-defect stabilization.** For a canonical Δ-system of walk conditions with
> strictly-increasing stalk levels, there are `ξ < η` such that every cross pair `x ⊑ u`
> (`x ∈ a_ξ`, `u ∈ a_η`) has `D⁺(μx, μu) ⊆ X(x) ∪ F(u)`.

This is the point where `osc(ρ)` enters: `D⁺(μx, μu)` is the trace-difference of the walks
from `μu` and `μx`, and finding a pair whose trace-differences fit fixed finite sets is a
pressing-down argument on the tree of walks controlled by oscillation — the mechanism of
Todorcevic's *Walks*, ch. 2, and of the cofinal-types-under-PFA theorem. Under **PFA**
(properness of exactly this poset via countable elementary submodels + the oscillation
control) the pair exists; hence the poset is proper, the generic exists, and **`Φ(e)`
holds — no escapee.**

**What is proved vs. cited [honest ledger].**
- **[proved, ZFC/machine-checked]** density; generic `⟹ Φ` (`phi_of_generic`); compatibility
  `⟺` cross-monotone/cross-defect fitting (`compat_of_crossMono`); the Δ-system reduction of
  ccc to the fitting statement.
- **[cited, Todorcevic, NOT reproved]** the cross-defect stabilization lemma — that under
  PFA a fitting pair exists. This is the one deep step, and it is genuinely deep: it *is*
  the oscillation content that makes ω₁ walks work, and it is *false* without the axiom (a
  CH counter-family is an antichain — the escapee).

**Straight statement.** The PFA proof is: [proved reduction] + [Todorcevic's oscillation
stabilization]. I have written and machine-checked the reduction and the generic-to-`Φ`
bridge; the oscillation lemma I cite. That lemma is not a gap in effort — it is the
irreducible engine, provable only with the axiom and only by the walks machinery, and I will
not transcribe a proof of it I cannot verify. This is the honest maximum: a complete proof
*relative to* the one theorem that is the actual heart of the subject.

## 41. The two-sided independence program: citations pinned, and the Invariance Lemma

Executing the collaborator's work order. Three load-bearing sources verified against the
literature; the residual is now a concrete two-sided program (MA reduces to a known
theorem's applicability; CH reduces to one coding gap).

**Citations pinned [verified this pass, except as flagged].**
- **Lipschitz / MA.** Todorcevic, *Lipschitz maps on trees*, J. Inst. Math. Jussieu **6**
  (2007) 527–556 (`math.toronto.edu/stevo/l-map2.pdf`). Under MA(ω₁): every coherent tree
  is **Lipschitz** (every level-preserving map on an uncountable subset has an uncountable
  Δ-preserving restriction), and every Aronszajn tree embeds into a coherent one. [verified]
- **Club-iso / PFA, and CH types.** Abraham–Shelah, *Isomorphism types of Aronszajn trees*,
  Israel J. Math. **50** (1985) 75–113 (`shelah.logic.at/files/95522/114.pdf`). Under PFA
  any two **normal** ω₁-Aronszajn trees are **club-isomorphic**; no prime tree; the CH side
  carries the many-non-isomorphic-types constructions. [verified]
- **Weak diamond / CH.** Devlin–Shelah, *A weak version of ◊ which follows from
  2^{ℵ₀} < 2^{ℵ₁}*, Israel J. Math. **29** (1978) 239–247. `Φ_{ℵ₁} ⟺ 2^{ℵ₀} < 2^{ℵ₁}`
  (so **CH ⟹ Φ**); predicts `c(f↾α) = g(α)` stationarily for every `f`; **kills
  ladder-system uniformization** — the exact shape of "no schedule survives." [verified]

**The Invariance Lemma (dip-schedulability is a tree-quotient invariant) [careful-prose].**
Schedulability of `e` is invariant under the three quotients the coherent-tree theory works
modulo:
1. **Club restriction** — Lemma E (§12), done.
2. **Finite modification** — if `e'_α =* e_α` for every `α`, a schedule `(γ, X)` for `e`
   schedules `e'` after enlarging each `X(x)` by the finite set `dev(e_{γ(x)}, e'_{γ(x)})`:
   the defects `D⁺` change only inside those finite sets, absorbed. [proved]
3. **Level-preserving club-isomorphism of `T(e)`** — if `φ : T(e)↾C → T(e')↾C` is a
   level-preserving club-isomorphism, a schedule for `e` transports to `e'` along `φ` with
   per-node finite error: `φ` carries defect patterns `D⁺(ζ, η)` to those of `e'` up to
   `φ`'s per-node finite error (level-preserving maps between coherent trees are Lipschitz —
   finite error, Todorcevic), which the dips absorb. [careful-prose; the finite-error step
   is the Lipschitz property, cited]

**The 0–1 law under PFA [conditional on Invariance + Abraham–Shelah].** `T(e)` for nontrivial
`e` is a normal ω₁-Aronszajn tree (coherent ⟹ Aronszajn; normalize). Under PFA all such are
club-isomorphic (Abraham–Shelah), so by the Invariance Lemma dip-schedulability is a **0–1
law**: under PFA either *every* nontrivial coherent sequence is schedulable or *none* is.
Consequences: the MA-side conjecture need be checked for **one** sequence; and Questions
3(a) (`ρ₁`) and 3(b) (`ρ₂`) **collapse** to the same question under PFA.

## 42. The MA side: the schedule forcing `P(e,μ)`, ccc reduced to alignment, alignment from Lipschitz

**The forcing `P(e,μ)` [defined].** Fix nontrivial `e` and pressure `μ` (per-`μ` suffices —
strong schedulability is `∀μ ∃schedule`, so MA_{ω₁} applies to each `P(e,μ)` separately).
Conditions `p = (d_p, γ_p, X_p, {(u, F_u) : u ∈ d_p})`: finite `⊑`-suitable `d_p ⊆ D(e)`;
monotone `γ_p ≥ μ↾d_p`; finite dips `X_p`; finite **promises** `F_u` sealing
`⋃_{x ⊑ u}(D⁺(γx, γu) \ X_x) ⊆ F_u`. Extension refines `d, γ`, grows `X`, **freezes** promises.

**Density [routine, ZFC].** `{p : w ∈ d_p}` is dense — chain-continuation dips (§10) give the
extension move (`γ(w) ≥ μ(w)` and above the down-set; `X(w)` absorbs into the frozen promises
of the finitely many tops above `w`).

**ccc ⟺ alignment [reduced, on the machine-checked amalgamation lemma].** Δ-system uncountably
many `p_α` (supports = domain ∪ dip/promise ordinals), isomorph over root `R`. Amalgamating
`p_α, p_β` requires the **cross-defects** `D⁺(γ_α(x), γ_β(u))` (`x ∈ d_α∖R`, `u ∈ d_β∖R`,
`x ⊑ u`) to land inside the already-committed `X_α(x) ∪ F_β(u)` — finite sets fixed *before*
seeing the partner. By `compat_of_crossMono` (machine-checked), amalgamation succeeds iff two
members' cross-defect patterns align:

> **A(e) (alignment).** Among any uncountable family of finite defect-labeled configurations
> in `T(e)`, two have aligning cross-defect patterns (on their overlap, mod committed finite
> sets). Then `ccc(P(e,μ)) ⟺ A(e)`.

**A(e) from Lipschitz [the crux, cited].** The cross-defect pattern `D⁺(ζ, η)` *is* the
difference-pattern of the coherent-tree nodes at `ζ, η` — the Δ-pattern the Lipschitz
property governs. Lipschitz-ness of `T(e)` (every level-preserving map on an uncountable
subset has an uncountable Δ-preserving restriction) yields an uncountable subfamily on which
patterns are Δ-preserved, hence align. So **Lipschitz(`T(e)`) ⟹ A(e) ⟹ ccc(`P(e,μ)`)**.
Under MA_{ω₁} every coherent tree is Lipschitz (Todorcevic), so A(e) holds for *every* `e`,
MA_{ω₁} meets the `ℵ₁` dense sets `{w ∈ d}`, and the generic is a schedule (`phi_of_generic`).

> **Conjecture (sharp): MA_{ω₁} ⟹ every coherent sequence is strongly dip-schedulable.**
> Hence **Question 1 is FALSE under MA_{ω₁}**, and **Question 4 affirmative**. Nontrivial
> coherent sequences exist absolutely (walks survive ω₁-preserving forcing), so this is a
> genuine model.

Note on Question 2's fractal regress: the promise-budget self-similarity (§8) becomes
**generic** under MA — the same dissolution MA performs on ladder-system uniformization
bookkeeping. The regress was the symptom of building the schedule by hand in ZFC.

Honest grade: `ccc ⟺ A(e)` is careful-prose on the machine-checked amalgamation lemma;
`A(e) ⟸ Lipschitz` is now **pinned to Lemma 1.3** of *Lipschitz maps on trees*, and §44
gives the cleaner ccc route via **Lemma 1.4** (disjoint finite stalks have an antichain
subfamily) landing directly on the machine-checked `compat_of_crossMono`. Citation precision
for the MA side is closed; see §44.

## 43. The CH side: Devlin–Shelah weak-diamond coding, and the one open joint

**The tool [verified].** Weak diamond `Φ_{ℵ₁}` (Devlin–Shelah; CH ⟹ Φ): for every
`c : 2^{<ω₁} → 2` there is `g : ω₁ → 2` with `{α : c(f↾α) = g(α)}` stationary for every
`f : ω₁ → 2`. It kills ladder-system uniformization — precisely "no schedule survives."

**The construction [sketch, one gap flagged].** Build `e` by recursion. At a limit `β`, a
schedule restricted to the countable `D_β` is a countable object, coded `f↾β ∈ 2^{<ω₁}`. Let
`c(f↾β)` predict one bit of *which continuation of `e_β` the partial schedule fails against*.
Φ gives `g` with `c(f↾β) = g(β)` stationarily for every total schedule `f`; at stage `β` use
`g(β)` to choose the continuation of `e_β` the predicted partial schedule cannot survive. At
the stationarily-many correct-prediction stages, the total schedule `f` fails at `β`.

**Why it evades the §9 no-go.** That no-go covered ◊-template kills (guess-and-lower
recursions vs *systems*). Weak diamond is a different species — a counting/prediction
principle (`2^ω < 2^{ω₁}`), not a guessing recursion — and post-§10 the target is
right-shaped: it needs only to defeat each *total* schedule at *one* stationary stage, not to
make any single stage's damage unabsorbable everywhere (which is what thinness fought in every
◊ design).

**The open joint [flagged, not papered].** Making "the partial schedule cannot survive
continuation-`g(β)`" **verifiable from the partial schedule at `β`** (countable data) is the
hard step — the exact point where thinness resisted ◊. Weak diamond's advantage (one
stationary stage suffices) is real but does *not* close it; the verifiability of failure-at-`β`
from `D_β`-data is the open joint.

> **Target: CH ⟹ some (plausibly every) nontrivial coherent sequence is not strongly
> dip-schedulable.** Hence **Question 1 TRUE under CH**.

The CH many-types structure (Abraham–Shelah 1985; Walks §4.3 CH constructions) is the ambient
source; the specific *wild-oscillation coherent tree* underneath the coding should be pinned
there — **relayed from the collaborator's verification, not independently confirmed this pass
(flagged per the citation discipline).**

**Both sides: Question 1 is independent of ZFC.** `Φ(e)` sits at the independence boundary via
the §12 arrow; the transport escapee **exists under CH, is absent under MA**. The qualitative
frontier of the program closes as *independent of ZFC* — the honest terminus, and exactly the
shape §5 of the problem statement predicted.

## 44. Lipschitz citations extracted, exact — and Lemma 1.4 upgrades the ccc proof (and ties to the machine-checked amalgamation lemma)

Extracted from the source PDF (Todorcevic, *Lipschitz maps on trees*, JIMJ 6 (2007);
`math.toronto.edu/stevo/l-map2.pdf`). The numbers are pinned, and the extraction *sharpens*
the MA-side argument rather than merely citing it.

**The standing postulate `(*)` [exact].** Def. (Introduction): the existence of filters
meeting given families of `ℵ₁`-many dense sets in **proper** partial orderings of size
`≤ ℵ₁` — the bounded proper-forcing-axiom shape; **for ccc posets this is MA_{ω₁}**, the
framework Todorcevic notes covers "a large majority" of the results. This is *precisely* the
shape of `P(e,μ)`: meet `ℵ₁` dense sets in a ccc poset of size `ℵ₁`.

**The exact statements.**
- **Definition 1.1.** `T` is *Lipschitz* iff it is Aronszajn and every level-preserving map
  from an uncountable subset of `T` into `T` is Lipschitz on an uncountable subset.
- **Lemma 1.3 [ZFC].** `T` Lipschitz, `A` uncountable `⊆ Tⁿ` ⟹ ∃ uncountable `B ⊆ A` with
  `Δ(aᵢ,bᵢ) = Δ(aⱼ,bⱼ)` for all `a ≠ b ∈ B`, `i,j < n`. **This is `A(e)`** — the alignment
  of cross-defect (= Δ-) patterns on an uncountable subfamily.
- **Lemma 1.4 [ZFC].** Every family of pairwise-disjoint *finite* subsets of a Lipschitz
  tree has an uncountable subfamily whose **union is an antichain**.
- **Lemma 1.7 (*), Lemma 1.10 [ZFC].** A coherent tree is Lipschitz iff every uncountable
  subset contains an uncountable antichain (1.10); every Lipschitz tree is a downward-closed
  subtree of the coherent (maps-mod-finite) tree (1.7, under `(*)`).
- **Lemma 7.2 (*).** Every Aronszajn tree embeds a Lipschitz (coherent) tree.

**MA_{ω₁} ⟹ coherent is Lipschitz [precise chain].** MA_{ω₁} ⟹ every Aronszajn tree is
special (classical) ⟹ every uncountable subset has an uncountable antichain ⟹ (Lemma 1.10)
every coherent tree is Lipschitz. So `A(e)` (= Lemma 1.3) holds for every coherent `e`
under MA_{ω₁}.

**The upgrade: Lemma 1.4 gives ccc directly, through the machine-checked amalgamation
lemma.** §42 routed ccc through the Δ-alignment (Lemma 1.3). Lemma 1.4 is cleaner and lands
exactly on the Lean result:
1. Δ-system the conditions ⟹ pairwise-disjoint finite **stalks** `a_ξ ⊆ T(e)` (root handled
   by isomorphism-over-root refinement).
2. Under MA_{ω₁} (`T(e)` Lipschitz), **Lemma 1.4** gives an uncountable subfamily whose stalk
   union is an **antichain** — so across any two, `a_ξ` and `a_η` have **no
   cross-comparabilities**.
3. No cross-comparabilities ⟹ the cross-clauses of `compat_of_crossMono` are **vacuous** ⟹
   the two conditions are **compatible** (the machine-checked amalgamation lemma, exactly the
   vacuous-cross case).
4. Uncountably many pairwise-compatible conditions ⟹ **ccc** (the family is linked).

So the MA-side ccc proof is: **Δ-system + Lemma 1.4 + `compat_of_crossMono`** — and the last
step is the *same* vacuous-cross mechanism the Lean `singleton_antichain_is_chain` uses. In
fact `singleton_antichain_is_chain` (single-element ccc, ZFC, machine-checked) is exactly the
**`n = 1` shadow of Lemma 1.4**: for singletons, "no ℵ₁-chain" *is* Lemma 1.4 at `n=1`; the
general finite-stalk case is Lemma 1.4 proper, which needs MA_{ω₁} (Lipschitz-ness). The ZFC
boundary the Lean file draws (single-element yes, multi-element axiom-dependent) is *exactly*
the boundary between `n=1` (ZFC) and `n≥2` (MA) of Lemma 1.4.

**Net [citation precision closed for the MA side].** `A(e) = ` Lemma 1.3; the clean ccc route
is Lemma 1.4; coherent-is-Lipschitz is Lemma 1.10 + MA-specialness; `(*)` = MA_{ω₁} for ccc,
the exact forcing-axiom shape of `P(e,μ)`. The MA-side conjecture now cites specific numbered
theorems, and the reduction bottoms out on the machine-checked amalgamation lemma. The only
remaining open joint in the whole program is the CH-side verifiability gap (§43).

## 45. The CH verifiability gap, attacked: weak diamond hits the thinness wall — but the independence stands via ◊ (Theorem C), which the gap was never needed for

Going at §43's open joint directly. The finding is two-sided and corrects §43's optimism:
weak diamond (one bit) genuinely does **not** close the dodge — but the independence of
"every coherent sequence is strongly schedulable" does **not need** the weak-diamond
strengthening, because the ◊ side is already **proved** (Theorem C, §15). So the gap is real
but not load-bearing.

**Why weak diamond hits the thinness wall [careful-prose].** The weak-diamond design wants,
at a limit `δ`, two continuations `e_δ^0, e_δ^1` (built from `e↾δ`, *not* from a schedule)
such that every partial schedule `(γ,X)↾D_δ` is defeated by at least one, with `c(f↾δ)`
computing which. Defeating `f` at the top `u = (δ, e_δ)` means a **surviving kill** — a kill
point `ξ ∉ X(x_δ)` (undipped by `f`) whose `0` propagates up to every floor `e_{γ(u)}` by
coherence. But `X(x_δ)` is a finite **set**, unknown, and:
- a *fixed* kill point `ξ_δ` fails — `f` may dip it (`ξ_δ ∈ X(x_δ)`), one point in a finite
  set it is free to include;
- *two* fixed kill points fail — `f` may dip both;
- dodging `f`'s finite dip set requires **seeing the set** (choosing `ξ ∉ X(x_δ)`), which is
  `|X(x_δ)|`-many bits, not one.

This is the **thinness wall** (the toolbox Remark): `f` can dip any single `e`-definable point
per element, so a surviving kill needs a point outside `f`'s finite dip — and identifying one
is multi-bit. The ladder-uniformization use of weak diamond escapes this because *there* the
adversary controls the target (the ladder colour) and sets it to differ from a *predicted
bit*; here the schedule defends by dipping a finite **set**, not by matching a bit. **The two
problems are not isomorphic, and one bit does not suffice.** So `Φ_{ℵ₁}` (CH) does not
obviously drive the kill; the construction wants the full countable partial schedule —
**◊-strength**.

**But the ◊ side is already proved, and the independence needs only that [proved].** The
statement whose independence the program wants is `S :≡ ` "every coherent sequence is strongly
dip-schedulable." A `∃`-refutation suffices for `¬S`, and **Theorem C (§15) proves under ◊
one nontrivial `e` is not strongly schedulable** — its staggered kill, guided by ◊'s full
guess of `(γ,X)↾D_β`, dodges the seen dips (exactly the multi-bit move weak diamond cannot
make). So **◊ ⟹ ¬S**. With the MA side (§42, §44: MA_{ω₁} ⟹ every coherent tree Lipschitz ⟹
every `P(e,μ)` ccc via Lemma 1.4 ⟹ `S`, conjecture on cited machinery), `S` is **independent**:

> **`S` = "every coherent sequence is strongly dip-schedulable" is independent of ZFC:
> TRUE under MA_{ω₁} (Lipschitz; conjecture on cited numbered theorems), FALSE under ◊
> (Theorem C, proved).** The strong-schedulability escapee exists under ◊, is absent under MA.

**Correction to §43.** §43 proposed the CH-side via Devlin–Shelah weak diamond and framed the
verifiability as the one gap. Corrected: weak diamond hits the thinness wall (the dodge is
multi-bit), so **CH-via-weak-diamond does not obviously work**; the ◊ side is instead carried
by the already-proved Theorem C, and the independence stands with ◊ (not CH) on the false
side. The genuinely open **refinement** is exactly: *does CH-alone (weaker than ◊) suffice for
`¬S`?* The thinness wall is evidence it may **not** — that `¬S` may need ◊-strength guessing,
not mere `2^{ℵ₀} < 2^{ℵ₁}`. This is a sharper and more honest open question than §43's, and it
sits precisely where ◊ and weak diamond part company for uniformization problems whose
"defense" is a finite set rather than a single value.

**The finer `Φ`/legal-escapee question, kept distinct [honest].** `S` is the
*strong-schedulability* (all pressures) statement. The *transport `Φ`-escapee* (a **legal**
system with no monotone dominator) is finer: Theorem C's lethal pressure is **illegal**
(Theorem D), so ◊ ⟹ ¬S does **not** yet give a legal ◊-escapee — that remains the §34–§40
open construction (legal value-gap ingredient in hand, global conflict open). So: `S`
independent (◊/MA); the legal-`Φ` escapee under ◊ still open; MA kills both. The
strong-schedulability frontier closes as independent; the legal-escapee frontier does not, and
the distinction is now explicit.

## 46. Citations pinned (three, exact), and the ρ₂→ρ₃ refinement: a coherent ZFC-Lipschitz tree

Collaborator's directive, executed with the two new citations verified verbatim against the
sources (local PDF extraction). One refinement to the directive, on the citation discipline
the collaborator themselves flagged.

**Repo-state note.** The collaborator's fetch cache is serving a ~§13 snapshot; the repo is at
**§45** — the Tukey identification (§36), Theorem I and the machine-checked amalgamation lemma
`compat_of_crossMono` (§38), and the Lipschitz-maps Lemma 1.3/1.4 pins (§44) already landed.
This work is §46+, renumbered from the directive's "§14."

**Pinned, verbatim.**
- **Theorem 2.5** (Todorcevic, *The Power-Set of ω₁ and the Continuum Problem*): "The tree
  `T(ρ₂)` is a **Lipschitz tree that can be decomposed into countably many antichains**"
  (Lipschitz + special) — **no axiom hypothesis, ZFC**. [verified]
- **Theorem 3.9** (same paper): "Assume CH. The class of Lipschitz trees is **not totally
  ordered** under `≤`; in fact there is a family of cardinality `2^{ℵ₁}` of **pairwise
  incomparable Lipschitz trees**." [verified]
- **Lemma 2.8 / Theorem 2.9** (Todorcevic, *Lipschitz maps on trees*, JIMJ 6 (2007), *unmarked
  by* `(*)` = **ZFC**): "There exists a **coherent Lipschitz tree**" / "a uniform coherent
  Lipschitz tree whose shifts are all coherent and Lipschitz." The tree is `T(ρ₃)`, with
  **(b) `t_α =* t_β↾α`** (mod-finite coherence) and **(c)** no trivialization (nontrivial),
  both ZFC. [verified]

**The refinement (ρ₂ → ρ₃).** The dip-schedulability game needs `e` **coherent in the
mod-finite sense** (`e_β↾α =* e_α`) — that is what makes `D(e)`, `D⁺`, and the whole apparatus
well-defined. Theorem 2.5 gives `T(ρ₂)` Lipschitz + special in ZFC, but `ρ₂` is *step-counting*;
its mod-finite coherence is **not** established by these sources (Lipschitz `⟹` coherent-form is
JIMJ Lemma 1.7, which is under `(*)`, not ZFC). The object that is **both** mod-finite-coherent
**and** ZFC-Lipschitz is **`ρ₃`** (Lemma 2.8/(b),(c) + Theorem 2.9). So the ZFC alignment
resource for a genuine coherent *sequence* lives on **`ρ₃`**, and the ccc attempt below is over
`ρ₃` (equivalently the JIMJ Lemma 2.8 coherent Lipschitz tree). `ρ₂` carries the resource for
the *tree/linear-order* theory but not, verified, for the coherent-sequence game. This is the
collaborator's own citation discipline applied to their `ρ₂`: the surprise is real, the
sequence is `ρ₃`.

**The reorientation.** The alignment (Lemma 1.3) and antichain (Lemma 1.4) resources are ZFC
consequences of a tree being Lipschitz — so for `T(ρ₃)` they hold **in ZFC**. Therefore the
**ccc of the schedule forcing `P(ρ₃, μ)` is itself a ZFC question**, with the axiom (MA_{ω₁})
entering only afterward to meet the `ℵ₁` dense sets. Attack Question 3(b) at **`ρ₃`** (the ZFC
Lipschitz resource lives on its tree), not `ρ₁`.

## 47. The ZFC ccc attempt for P(ρ₃, μ), on the machine-checked amalgamation lemma

Attempting the ccc of `P(ρ₃, μ)` **in ZFC**, per the directive, with the tuple-Lipschitz lemma
(JIMJ Lemma 1.4, ZFC for `T(ρ₃)` by Lemma 2.8) as the amalgamation engine.

**The argument [careful-prose; lands on `compat_of_crossMono`].** Fix `μ`; take uncountably
many conditions `p_ξ = (d_ξ, γ_ξ, X_ξ, F_ξ)`.
1. **Δ-system + type isomorphism.** Refine to root `R`, pairwise-disjoint finite **stalks**
   `a_ξ ⊆ D(ρ₃)`, with `γ, X, F` matching on `R` and the stalks order/label-isomorphic.
2. **Lemma 1.4 (ZFC, `T(ρ₃)` Lipschitz).** The stalks' tree-nodes are pairwise-disjoint finite
   subsets of `T(ρ₃)`; Lemma 1.4 gives an uncountable subfamily whose stalk-node union is a
   **`T(ρ₃)`-antichain** — so across any two, the tree-nodes are pairwise incomparable.
3. **Tree-antichain `⟹` fiber-incomparability, mod finite.** Tree-incomparable nodes have
   floors that split below both levels, with one exceeding the other at the split — so the
   fiber functions satisfy `s_x ⋠ s_u` and `s_u ⋠ s_x` off a finite set: `x, u` are
   `D(ρ₃)`-incomparable up to the coherence `=*` fuzz, which is finite.
4. **Vacuous/finite cross `⟹` compatible.** With no cross-`⊑` (mod finite), the cross-defects
   `D⁺(γ_ξ x, γ_η u)` are finite (coherence) and absorbed into the amalgam's dips and the frozen
   promise budgets; the cross-clauses of the machine-checked `compat_of_crossMono` are then
   (mod the finite absorption) **vacuous**, so `p_ξ, p_η` are compatible.
5. Uncountably many pairwise-compatible conditions `⟹` **ccc**.

**Assessment [honest].** Steps 1, 2, 5 are rigorous (Δ-system is standard; Lemma 1.4 is the
verified ZFC input; the machine-checked amalgamation lemma is the compatibility core). Steps 3–4
are careful-prose: the "tree-antichain `⟹` fiber-incomparable mod finite" and the absorption of
the finite cross-defects into the committed budget are the bookkeeping the `n=1` Lean result
(`singleton_antichain_is_chain`) already discharges in the vacuous case — this is its `n≥2`
generalization, powered by Lemma 1.4 exactly as §44 predicted. **No axiom is used**: `T(ρ₃)`
Lipschitz is ZFC (Lemma 2.8). If steps 3–4 close (they are of standard Δ-system type), then:

> **ccc(`P(ρ₃, μ)`) in ZFC** ⟹ under **MA_{ω₁}** the `ℵ₁` dense sets `{w ∈ d}` are met ⟹
> **`ρ₃` is strongly dip-schedulable**. `ρ₃` is nontrivial in ZFC (fact (c)), so **Question 1
> is FALSE under MA_{ω₁}** and **Question 4 is answered affirmatively** — with the hard part
> (ccc) done in ZFC and the axiom reduced to its textbook role of meeting dense sets.

The one residual is steps 3–4's bookkeeping at full rigor; the engine (ZFC Lipschitz `⟹`
Lemma 1.4 `⟹` amalgamation) is pinned and machine-checked at its core.

## 48. The CH side via Theorem 3.9's incomparable family; and the shape-of-the-answer question

**The kill target, now an object.** Theorem 3.9 gives, under CH, a `2^{ℵ₁}`-family of
**pairwise-incomparable Lipschitz trees** — the conspiracy *realized*: their §3-construction
(JIMJ, combining different coherent trees so cross-oscillation defeats comparability) manufactures
exactly the **unalignable cross-defect patterns** an amalgamation argument chokes on. This
replaces the generic weak-diamond sketch (§43, blocked by the thinness wall §45) as the **primary**
CH-side route: over such a wild tree the schedule forcing has uncountable antichains (alignment
fails by construction), so no schedule of any provenance plausibly survives. Devlin–Shelah weak
diamond stays only as a fallback.

**The shape-of-the-answer question [honest, and it may not be independence].** Note the quantifier
structure. The MA side (§47) makes **`ρ₃` schedulable using only its ZFC-Lipschitz resource** — the
axiom just meets dense sets. If `ρ₃`'s schedulability is genuinely ZFC-adjacent (needs only a mild
axiom, not full independence), while the Theorem-3.9 wild trees are **non-schedulable under CH**,
then the outcome is **not** "Question 1 independent" but:

> **Possible outcome: `ρ₃` (and its kin) schedulable at ZFC-adjacent strength; the CH-wild trees
> dead under CH — Question 1 FALSE outright, with CH controlling only *which* sequences schedule,
> not *whether any* do.**

Because Q1-false needs only *one* nontrivial schedulable sequence, and `ρ₃` is the candidate whose
ZFC-Lipschitz-ness *resists* the CH kill (its tree is Lipschitz in ZFC, so Theorem 3.9's
incomparability does not touch it). So CH does not obviously kill `ρ₃` — it kills the *wild* trees.
This is a genuinely different terminus from §45's "◊ false / MA true independence," and which one
holds is decided by **how much Lemma G (invariance) separates `ρ₃` from the wild trees**:

- if schedulability is invariant only under club-iso *within* a Lipschitz-tree class, `ρ₃` and the
  wild trees are separated, and Q1 is **false outright** (`ρ₃` always schedules, mild-axiom);
- if invariance is broad enough to transport the wild trees' non-schedulability to `ρ₃`, then the
  independence of §45 stands.

So **Lemma G is load-bearing for the *shape* of the final answer**, not a convenience. Its exact
scope — precisely which tree maps transport schedules — decides "Q1 false outright" vs "Q1
independent." Stating that scope exactly is the next task; §41's three-quotient version (club
restriction, finite modification, level-preserving club-iso) transports *within* a club-iso class,
which — since Abraham–Shelah club-iso is a *PFA* phenomenon, not ZFC — does **not** by itself bridge
`ρ₃` to a ZFC-incomparable wild tree. That points toward **Q1 false outright** (`ρ₃` schedules,
wild trees are a separate CH story), with the independence being of the *finer* legal-`Φ` escapee
rather than of strong schedulability. Kept as an open, honestly two-branched, verdict.

## 49. Lemma G's exact scope: the value/tree boundary — part (iii) retracted, the 0–1 law withdrawn, the terminus decided (sixteenth flip)

Nailing the scope, as directed. The finding is sharp and partly a retraction: **schedule
transport lives in the value category, not the tree category** — and this decides the
terminus.

**What the game data actually is.** The fiber order `D(e)` is *pointwise value dominance*
(`s ≤ t↾α` in the ω-order at every coordinate); the defects `D⁺(a,b) = {ξ : e_a(ξ) > e_b(ξ)}`
are *value comparisons at deviation coordinates*. The tree `T(e)` is ordered by *exact
extension*; its isomorphism invariants are levels and **splits** (`Δ` = *first*
disagreement). Two facts, both checkable:
1. **Deviation sets are not tree data.** For same-level nodes `x, y`, the tree order sees
   only `Δ(x,y)` (`x↾ξ = y↾ξ` iff `ξ ≤ Δ`); the *later* disagreements — their positions and
   their value-directions — leave no trace in the tree order.
2. **Value permutations are tree isos.** Permuting `ω`-values independently at each
   coordinate maps `T(e)` level-preserving-isomorphically onto `T(e″)` (it preserves
   equality/disagreement of restrictions) while **flipping value comparisons arbitrarily**
   (only the identity is an increasing bijection of ω): `D(e″)` and its `D⁺` bear no fixed
   relation to `D(e)`'s.

**Retraction (part iii of Lemma G, §41).** The §41 sketch — "schedules transport along
level-preserving club-isos with per-node finite error, since level-preserving maps between
coherent trees are Lipschitz" — is **wrong as stated**: the Lipschitz property controls
`Δ` (splits, on an uncountable subset), *not values*; the "per-node finite error" in the
value sense was never established, and by fact 2 it is not establishable from tree data.
**Lemma G(iii) is retracted.** With it falls the **PFA 0–1 law** (§41/§48), which ran
Abraham–Shelah club-isomorphism through (iii): club-isos are tree-category maps, and they do
not transport schedules. Withdrawn.

**Lemma G, correct scope [stated exactly].** Dip-schedulability transports along `h` iff `h`
is a **value-category** morphism: a club-level correspondence `σ` together with row
correspondences that preserve *pointwise ω-order mod finite* — precisely: for a club of
levels, `e'_{σ(a)}` and `e_a` compare with **finite value-distortion per pair, locally finite
per top** (so dips/promises absorb the distortion). Parts (i) club restriction and (ii)
finite modification are instances and stand [proved]. Tree-embeddability, tree-isomorphism,
and club-isomorphism are **not** in scope.

**The terminus, decided.** The §48 fork asked whether the Theorem-3.9 wild trees'
(conjectured) CH-non-schedulability can transport to `ρ₃`. Answer: **no bridge exists in any
model** — (a) transport needs a value-category map, strictly finer than tree maps; (b) under
CH the wild family is pairwise tree-incomparable and any wild↔ρ₃ tree map, if one existed,
still wouldn't transport; (c) the club-iso quotient was the only proposed broad bridge and it
is both PFA-only *and* out of scope. **`ρ₃` is separated. The §45 "Q1 independent via
invariance" route is dead.** What stands, with honest grades:
- **Q1 FALSE under MA_{ω₁}**, witness `ρ₃` — nontrivial in ZFC, schedulable under MA via the
  §47 ccc (mod steps 3–4 rigor). [the MA half of the terminus]
- **Under CH/◊, Q1 is genuinely open, and the obstruction is now precise**: Theorem C's kill
  *builds* its sequence and cannot target the *fixed* `ρ₃`; transport cannot reach `ρ₃`; the
  wild trees bear on `S` (all-schedulable), not on Q1. **The program's new central open
  problem: is `ρ₃` strongly dip-schedulable under CH (or ◊)?** Its ZFC-Lipschitz-ness gives
  ccc but not a filter (MA_{ω₁} contradicts CH), so both answers are live.
- **`S` = "every coherent sequence is strongly schedulable" remains independent-shaped**:
  FALSE under ◊ (Theorem C, proved — the custom-built witness), TRUE under MA (the §42/§47
  conjecture). Unchanged by this section.
- **The 0–1 law: withdrawn**; Questions 3(a)/3(b) do *not* collapse under PFA by any argument
  currently on the table.

**Why this is the right kind of ending for the scope question.** The collaborator's
instinct — "Lemma G is load-bearing for the shape of the final answer" — is confirmed, but
in the negative direction: its honest scope is *narrow* (value category), the broad
invariance that would have forced independence-of-Q1 does not exist, and the terminus is the
**separated** picture: MA schedules `ρ₃` (Q1 false there); CH's wildness kills only wild
trees (bearing on `S`); and the last question standing between the program and a full
answer is `ρ₃`-under-CH — a single, concrete, well-posed problem about the canonical walk
sequence. Sixteenth flip: a retraction (G(iii), the 0–1 law) that *decides* a fork.

## 50. ρ₃ under CH: the wall breaks, the kill becomes the block-accumulation game, and the crux is fiber-specialness

Going at the central open problem. Three findings at careful-prose rigor, each two-sided-honest;
the problem does not fall, but it reduces to one new, concrete invariant of `D(ρ₃)`.

**Finding 1: CH breaks the thinness wall.** §45's protection was specific to *weak diamond's one
bit*: dodging a finite dip set is multi-bit. But under CH there are only `ℵ₁`-many countable
partial schedules (each is a countable object over a countable set; `2^{ℵ₀} = ℵ₁`), so a
CH-adversary can **enumerate them as full objects** — dips visible, the exact information ◊
supplied in Theorem C and weak diamond lacked. So ρ₃-under-CH is genuinely threatened: the
enumeration resource is available. What the CH-adversary does *not* have is Theorem C's other
resource: it cannot build `e` — `ρ₃` is fixed — so the kill must be manufactured from `ρ₃`'s own
drop structure, steered only through the pressure map `μ`.

**Finding 2: over ρ₃ the kill is exactly the block-accumulation game.** From the verified
construction (Lemma 2.8): rows are binary, and **(a)** `supp(t_β) ∩ (Λ+k)` is *finite for every
`β` and every `k`* — every row meets every block-class finitely. Since drops are
`D⁺(c, γ) = supp(t_c) \ supp(t_γ)` (binary values), fact (a) cuts both ways:

> **Permanent-leak mechanism [careful-prose].** If commitments `c_n` (the schedule's chosen
> levels, at elements `x_n ⊑ u`) have support points `ξ_n ∈ supp(t_{c_n}) ∩ (Λ+k₀) ∩ gap(x_n)`,
> *distinct, undipped, in a single block-class `Λ+k₀`*, then for **every** later floor `γ`:
> `supp(t_γ) ∩ (Λ+k₀)` is finite (fact (a)), so all but finitely many `ξ_n` are drops surviving
> at `γ` — the leftover at `u` is infinite for *all* continuations. **A block-accumulation is a
> permanent leak: no future floor ever absorbs it.** Conversely, per-element exposure *per
> block* is finite (fact (a) again), so each element can dip its exposure in any *finitely many*
> named blocks — but its total gap-exposure (across all blocks) may be infinite, so it cannot
> guard every block at once.

So the CH-kill has a precise shape: force pressure so gaps are long, then use the enumeration to
pick, against each candidate's committed dips, a block-class its commitments under-guard, and
accumulate. And the schedule's precise counter: guard blocks *diagonally*.

**Finding 3: the schedule's counter is a ranking, and its existence is the crux.** The diagonal
strategy — element `x` dips its exposure in blocks `k ≤ rank(x)` — blocks every accumulation
*iff* along every down-set, every fixed block-class is eventually guarded, i.e. iff the ranking
has **finite fibers on every down-set**:

> **Definition (fiber-special).** `D(e)` is *fiber-special* if `D(e) = ⋃_{n<ω} R_n` with each
> `R_n ∩ ↓u` **finite** for every `u ∈ D(e)`.

If `D(ρ₃)` is fiber-special (in ZFC), the diagonal dips defeat every block-accumulation, and the
CH-kill's *only known mechanism* dies — evidence that **ρ₃ is schedulable under CH too**, which
with §47/§49 would push toward *Q1 false in both models* (false outright-flavored, modulo the
value-form bookkeeping). If fiber-specialness fails — or holds only off a Φ-guessable core — the
enumeration + block game plausibly kills, and **Q1 goes independent** (`ρ₃` dead under CH, alive
under MA). Two honest checks already run:
- *Tree-specialness does not give it*: `T(ρ₂)`-style specialness decomposes into
  tree-antichains, but a tree-antichain can meet a single ⊑-down-set infinitely (turn off one
  point of `s_u↾α_n` at distinct points: pairwise tree-incomparable, all `⊑ u`) — checked, so
  the known ZFC specialness of walk trees does **not** settle it.
- *The regress signature is present*: a global ranking is a uniformization-type object (its
  per-down-set order types are countable but the ranks must cohere across overlapping
  down-sets) — the same self-similarity the program has met at every level. This is where the
  problem's difficulty genuinely lives, not an artifact.

**Status after the attack.**
- ρ₃-under-CH does **not** fall this session, in either direction — honestly.
- It **reduces** to: *is `D(ρ₃)` fiber-special?* — a new, sharply-posed, ZFC-or-not invariant
  (σ-decomposition into pieces finite in every down-set), now the program's crux. ZFC-yes ⟹
  the block-game dies and `ρ₃` plausibly schedules under CH (Q1 false everywhere reachable);
  no/Φ-defeatable ⟹ CH kills `ρ₃` and Q1 is independent.
- The findings sharpen both sides: the CH-adversary's wall is *down* (Finding 1) and its
  mechanism is *explicit* (Finding 2); the schedule's necessary-and-sufficient counter is
  *named* (Finding 3). The next session's target is fiber-specialness of `D(ρ₃)` — and note it
  is a **pure order-theoretic question about the fiber order**, back in the value category
  where (§49) the game actually lives.

## 51. Fiber-specialness is σ-down-finiteness: Theorem J transfers it to the tree order, Theorem K lands the Tukey frame, and the sources yield three new verified resources — "T(ρ₃) special?" is now the necessary gate

Going at the §50 crux. It does not fall, but it is structurally located this session: three
proved theorems, a first-hand source-verification round (both ρ₃ sources fetched and
extracted; one typo caught *in the source*), and the crux split into a necessary
tree-condition — a new, named, classical-flavored subproblem — plus a dip-refinement.

**Source round [verified, verbatim quotes].** Both sources are now first-hand: Todorcevic,
*Lipschitz maps on trees* (JIMJ 6 (2007); `l-map2.pdf`, author's Toronto page) and Todorcevic,
*Coherent Sequences* (Handbook of Set Theory, ch. 1; `coherent.pdf`, ibid.) — the latter being
the JIMJ paper's own reference [15] for the `T(ρ₃)` facts (its §3: Def 3.3, ρ₃ = last-step-of-
maximal-weight indicator; Lemma 3.4, coherence).
- **§50's fact (a) CONFIRMED — and a typo found in the source.** Handbook Lemma 3.8, verbatim,
  for `B_α = {ξ < α : ρ₃(ξ, α) = 1}`: "(1) `B_α =∗ B_β ∩ α` for `α < β`, (2) `(Λ + n) ∩ B_β`
  is finite for all `n < ω` and `β < ω₁`, (3) `{λ + n : n < ω} ⊆∗ B_β` whenever `λ + ω ≤ β`."
  So (2) is §50's "every row meets every block-class finitely" — for the **ones**, as §50 used
  it. The scare: JIMJ footnote 10 defines `supp(t_β) = {α < β : t_β(α) = 0}` — the *zero*-set —
  under which §50's game would invert (single-block accumulations would be absorbed, not
  permanent). The second source killed the scare in §50's favor: blocks are infinite, so
  zeros-per-block-finite (footnote-10 reading of JIMJ (a)) and ones-per-block-finite (3.8(2))
  cannot both hold, and JIMJ Lemma 2.8's own claim ("orthogonal to `Λ + k` for every `k`")
  matches 3.8(2) exactly under `supp` = ones. **Footnote 10 is a typo; fact (a) means the
  1-set; the §50 block-accumulation game stands unchanged.** (A seventeenth flip threatened by
  a footnote and averted by a second source — the citation discipline paying for itself.)
- **New resource 1 (fan-cofiniteness, 3.8(3)) [verified]:** every row is 1 on all but finitely
  much of every fan `[λ, λ+ω)` below it. Dual orthogonal pictures: ones are *column*-finite
  (3.8(2)), zeros are *fan*-finite (3.8(3)). The Handbook also frames ρ₃ as the prototype
  *nowhere dense* coherent map — `ω₁ = ⋃_n (Λ+n)` with each block orthogonal to ρ₃ (Def 3.12)
  — and Prop 3.13: under the **P-ideal dichotomy** (CH-compatible!) every nowhere dense
  coherent map's domain so decomposes. Filed for the CH game.
- **New resource 2 (Remark 1.17 + Lemma 1.16(a)) [verified]:** `T(ρ₁) := {t : α → ω : t =∗
  (ρ₁)_α}` — the **full =∗-closure**, i.e. literally the element set of `D(ρ₁)` — "is a
  homogeneous, special Aronszajn tree", ZFC; and the rows `(ρ₁)_α` are finite-to-one
  (`{ξ ≤ α : ρ₁(ξ, α) ≤ n}` finite). The ρ₀/ρ₁/ρ₂ specializations all run on value-
  unboundedness — the resource binary ρ₃ maximally lacks. **No specialness statement for
  `T(ρ₃)` appears in either source** (grep-verified: "special" occurs in the JIMJ paper only
  at Lemma 1.9 and its footnote 9).
- **New resource 3 (JIMJ Lemma 1.10, ZFC) [verified]:** "A coherent tree T is Lipschitz if and
  only if every uncountable subset of T contains an uncountable antichain." With Lemma 2.8
  (`T(ρ₃)` Lipschitz, ZFC): **`T(ρ₃)` is hereditarily non-Souslin in ZFC** — every uncountable
  subset, in every model, contains an uncountable antichain. Meanwhile coherent *Souslin*
  trees exist under ◊ (secondary: Todorcevic, *Forcing with a coherent Souslin tree*; Rinot's
  microscopic-approach papers), and by 1.10 they are exactly non-Lipschitz coherent trees. So
  coherence alone never yields specialness, and Lipschitzness is precisely what separates
  `T(ρ₃)` from the ◊-wild coherent trees — it closes the Souslin door but not the
  non-special door.

**Reformulation [proved].** Call `R ⊆ D(e)` **down-finite** if `R ∩ ↓u` is finite for every
`u`; equivalently (two lines): every infinite subset of `R` is `⊑`-unbounded — `R` is
*strongly unbounded* in the Tukey sense. Fiber-special = `D(e) = ⋃_{n<ω} R_n` with each `R_n`
down-finite = there is `r : D(e) → ω` finite-to-one on every down-set. Note each level of
`D(e)` is countable (`[α]^{<ω} × ω^{<ω}` many elements), so per-level injectivity is free; the
entire content is cross-level.

**Lemma H (chains) [proved].** For coherent `e`: `D(e)` has an *uncountable* `⊑`-chain iff `e`
is trivial. *Proof.* Levels are countable, so an uncountable chain uses uncountably many
levels; comparability orders levels, so a recursion (elements at levels `≤ δ` form a countable
union of countable level-fibers) extracts an ω₁-subchain with strictly increasing cofinal
levels — Lemma D applies. Converse: Lemma D's chain. ∎ Corollary: fiber-special ⟹ nontrivial
(each `R_n` meets every initial segment of an ω₁-chain finitely, hence meets the chain in
order type ≤ ω; countably many such sets cannot cover it).

**Theorem J [proved]: fiber-special ⟹ the closure tree is special.** Let `U(e)` be the full
=∗-closure tree — all fiber elements ordered by **end-extension** (`⊇ T(e)` as the
restriction-closure of the exact tree). Three observations:
1. *For trees, special ⟺ σ-down-finite.* (⟸) If `B` meets every tree-down-set finitely, then
   since tree-predecessors `↓_T x` form a chain, `ρ(x) := |↓_T x ∩ B|` is a finite rank on
   `B`, strictly increasing along comparabilities — its fibers are antichains, so `B` is a
   countable union of antichains. (⟹) An antichain meets each `↓_T x` (a chain) in ≤ 1 point.
2. *End-extension implies pointwise domination.* If `s ⊆ s'` then `(dom s, s) ⊑ (dom s', s')`
   — equality below `dom s` is domination. So `U(e)` is a **suborder of `D(e)` on the same
   element set**, and every tree-down-set `↓_T s` (the restrictions `s↾ξ`, which stay in the
   closure) is contained in the fiber-down-set `↓(dom s, s)`.
3. *σ-down-finiteness passes to suborders.* Immediate: fewer relations, smaller down-sets.
Chaining 1–3: `D(e)` fiber-special ⟹ `U(e)` = ⋃ of tree-down-finite pieces ⟹ **`U(e)` (hence
`T(e)`) is special** — hence Aronszajn, hence `e` nontrivial. ∎
The converse **fails at the dips** — §50's check stands: a tree-antichain (turn off one point
of `s_u↾α_n` at distinct points) can be infinite inside a single fiber-down-set, so
tree-specialness is the *order-reduct* necessary condition, not the whole invariant.

**The gate.** By Theorem J, **"`T(ρ₃)` is special" is formally necessary for fiber-specialness
of `D(ρ₃)`** — and it is *not* among the verified facts (resource 2), its classical proof
engines don't apply (binary kills the value-labeled antichains that specialize ρ₁/ρ₂), and
what is verified is strictly weaker (hereditary non-Souslinness, resource 3). Named:
- **(Q-T)** Is `T(ρ₃)` special — in ZFC? under CH? *(New subproblem, classical flavor. If
  some CH-model has `T(ρ₃)` non-special, fiber-specialness fails there and §50's diagonal
  counter dies in that model — though not schedulability itself; honest. Note also `T(ρ₃)`
  is one tree per C-sequence satisfying (d): under CH the choice of C-sequence is *ours*,
  a freedom the positive side should exploit.)*

**Theorem K (the Tukey landing) [proved].** (i) Always `D(e) ≤_T [ω₁]^{<ω}` (directed, size
ℵ₁, finite sets bounded — map `x` to a singleton). (ii) If `D(e)` is fiber-special, some piece
is uncountable, i.e. an uncountable strongly unbounded set exists, i.e. `[ω₁]^{<ω} ≤_T D(e)`
(map a finite set to an upper bound of its elements' witnesses; unbounded families have
infinite unions, whose witness-sets no single element bounds). So **fiber-special ⟹ `D(e) ≡_T
[ω₁]^{<ω}`**, the maximal cofinal type of size ℵ₁ — the exact σ-refinement of §36's frame.
**Calibration [proved]: for ρ₃ the Tukey half is ZFC-cheap, two ways.** (a) *Value-spikes*:
`x_α := (α+1, row-with-value-2-at-α)`; a top's function is =∗ a binary row, so it exceeds 1
only finitely often — every infinite subfamily is unbounded. (b) *Flat block-spikes*: by
3.8(2) pick recursively `α_ι` increasing and fresh `ζ_ι ∈ (Λ+1) ∩ α_ι \ B_{α_ι}` above all
previous; `x_ι := (α_ι, χ_{B_{α_ι}} ∪ {ζ_ι})`. Any top's ones meet `Λ+1` finitely (3.8(2)),
so it bounds only finitely many `x_ι`. **So `D(ρ₃) ≡_T [ω₁]^{<ω}` outright in ZFC**, and the
crux is *not* the Tukey type: it is the σ-*covering* — every element, in particular every
canonical one, must land in some strongly unbounded piece. Third occurrence of the program's
"strictly finer than Tukey" signature (§37 Φ, §39 retraction, now fiber-specialness).

**Flat-core reduction [proved].** `flat(α, s) := (α, {ξ : s(ξ) ≥ 1})` is monotone into the
binary core `{(α, A) : A =∗ B_α}` with countable fibers (the exceptional values form a finite
partial function into ω), so pairing a flat decomposition with fiber-indices pulls
down-finiteness back: **`D(ρ₃)` is fiber-special iff its flat support core is** — a pure
statement about the coherent set-system `{B_α}` under (level, ⊆). There, boundedness is
explicit: an infinite `{(α_i, A_i)}` is bounded iff `∃β ≥ sup α_i` with `⋃_i (A_i \ B_β)`
**finite** (then `χ_{B_β ∪ ⋃(A_i\B_β)}` is a legitimate top). So a piece is strongly unbounded
iff no infinite subfamily is *jointly almost-inside one row*.

**The canonical-rows subquestion.** Specializing to the rows themselves:
- **(Q-rows)** Is `{(α, B_α) : α < ω₁}` strongly unbounded — i.e. is `⋃_{α∈I}(B_α \ B_β)`
  infinite for every `β` and every infinite `I ⊆ β`?
This is *verbatim* the schedule game's central quantity: `B_α \ B_β = D⁺(α, β)`, so (Q-rows)
is the `γ = id`, `X = ∅` instance of "the leftover `⋃_{x⊑u} D⁺(γ(x), γ(u)) \ X(x)` is infinite
for every top." **The absorption phenomenon the game is about *is* the boundedness relation of
`D(ρ₃)`** — the self-similarity met at every level (§32, §50) is here an identity, not an
analogy. Two-sided: if some infinite row-family is jointly absorbed, those rows are exactly
the hard-to-cover elements (a trivial-direction germ inside a nontrivial sequence); if none
is, the canonical rows form a single strongly unbounded piece — one piece of the needed
decomposition, for free. Resource note: each deviation `B_α \ B_β` lives inside `α \ B_β`,
which meets every fan finitely (3.8(3)) — joint absorption would confine infinitely many
rows' deviations to one finite set, a very rigid alignment that ρ₃'s oscillation plausibly
forbids; unresolved this session.

**Status after the attack.**
- Fiber-specialness of `D(ρ₃)` does not fall, but is now bracketed: **necessary** — `T(ρ₃)`
  special (Q-T, open, unverified in the sources, ZFC-plausible since the Souslin obstruction
  is dead in ZFC); **cheap** — the Tukey type (`≡_T [ω₁]^{<ω}` in ZFC, Theorem K); **crux** —
  the σ-covering of the flat core, whose boundedness relation is the game's own absorption
  condition (Q-rows).
- The §50 dichotomy sharpens: the "ZFC-yes" branch must first clear Q-T in ZFC — a wall with
  independent classical interest; the "CH-kills" branch gains a new mechanism — any CH-model
  with `T(ρ₃)` non-special refutes fiber-specialness there via Theorem J's contrapositive.
- Verified base extended: fact (a) re-confirmed against [15] with the JIMJ footnote-10 typo
  flagged; fan-cofiniteness, `T(ρ₁)`-specialness (full closure, ZFC), and hereditary
  non-Souslinness of `T(ρ₃)` (ZFC) added as resources. `D(ρ₁)` is now also a live secondary
  target: *its* tree-special gate is already verified-ZFC, so fiber-specialness of `D(ρ₁)` is
  unobstructed at the gate — though the §50 game analysis (blocks, fans) is ρ₃-specific and
  would need its ρ₁ analogue before feeding a CH-schedulability claim.

## 52. Q-rows falls (answer: NO) — successor rows ride their fans; the crux descends to a threshold sequence θ(ρ₃) of ρ₁-species; and CH alone cannot slam the Q-T gate

Going at §51's two open subproblems. One of them is *settled*: (Q-rows) is **false**, by a
two-line ZFC argument that §51's closing plausibility remark got exactly wrong. The failure
is benign for the crux (successor levels collapse onto limit levels) and productive beyond
it: the same source round that verified the conventions yields an exact pruning formula for
the deviation sets, and through it the whole absorption game descends one level — from ρ₃'s
binary rows to a canonical ω-valued, coherent, *finite-to-one* "threshold sequence" on the
fan-top index. On the second subproblem (Q-T), the gate is shown consistently open with CH
(Theorem O), so the CH-kill branch needs strictly more than CH.

**Source round 3 [verified, verbatim].** From `coherent.pdf` (Handbook ch. 1), closing §51's
gaps and correcting one attribution:
- Standing normalizations of the C-sequence, verbatim: **(a)** `C_{α+1} = {α}`; **(c)** "If α
  is a limit ordinal, then C_α does not contain limit ordinals"; **(d)** "If α is a limit
  ordinal > 0 and if ξ occupies the nth place in the increasing enumeration of C_α ..., then
  ξ = λ + n + 1 for some limit ordinal λ (possibly 0)". All of §3's ρ₃-facts assume these;
  so does everything below. Note the rigidity (d) buys: an ordinal ξ can appear in a ladder
  only if ξ = λ+n+1, and then only at place n — *the place is intrinsic to ξ*. Consequently
  a walk arrives at ξ = λ+n (n ≥ 1) with last weight n−1 (off a limit's ladder) or 0 (off
  `C_{λ+n+1} = {λ+n}`), and walks reach a limit ordinal only through its successor.
- Def 3.3, verbatim: `ρ₃(α,β) = 1 iff ρ₀(α,β)(ρ₂(α,β)−1) = ρ₁(α,β)` — "the last step of
  the walk β → α comes with the maximal weight". **Weak tie convention**; in particular a
  one-step walk always has ρ₃ = 1. Here ρ₁ is Handbook **1.15** (maximal weight = largest
  entry of ρ₀), with **1.16(a)** (rows finite-to-one: `{ξ ≤ α : ρ₁(ξ,α) ≤ n}` finite),
  **1.16(b)** (ρ₁ coherent), **1.17** (`T(ρ₁)` special). Correction of record: §51's
  "resource 2" citations are *Handbook* numbers — the JIMJ paper has no 1.16/1.17.
- **Lemma 1.6(b)**, the factoring engine, verbatim: `ρ₀(α,γ) = ρ₀(min(F(β,γ)\α), γ)⌢
  ρ₀(α, min(F(β,γ)\α))` for α ≤ β ≤ γ, with F the full lower trace (1.4; subadditive, 1.5).
- JIMJ **Lemma 1.9** now read — the one "special" occurrence §51 left unopened: "The square
  of every special coherent tree T can be covered by the graphs of countably many Lipschitz
  functions." Specialness is a *hypothesis* there, not a conclusion (footnote 9 is just the
  definition). No specialness dichotomy for `T(ρ₃)` hides in either source; Q-T stands.
- Every walk-level formula below was additionally brute-checked on a randomized
  (d)-conforming C-sequence over the ordinals below ω·25 (scratch script: the pruning
  formula and the arrival rigidity at ~42k sample points, the successor and fan-absorption
  identities across hundreds of instances; all pass). [proved + numerically checked]

**Lemma I (successor riding) [proved].** `B_{γ+1} = B_γ ∪ {γ}` for every γ. *Proof.*
`C_{γ+1} = {γ}` gives `ρ₀(ξ, γ+1) = ⟨0⟩⌢ρ₀(ξ,γ)` for ξ < γ, and prepending a 0 changes
neither the last entry nor the maximum of a weight sequence; and `ρ₀(γ,γ+1) = ⟨0⟩` has
last = max. ∎ (Uses (a) only.) Iterating: **`B_{λ+m} = B_λ ∪ [λ, λ+m)`** for λ limit-or-0,
m ≥ 1 — inside a fan the canonical rows just eat the fan from the bottom.

**Theorem L (Q-rows is FALSE) [proved].** For every limit λ and every β ≥ λ+ω the infinite
canonical family `I = {λ+m : 0 < m < ω} ⊆ β` satisfies
`⋃_{α∈I}(B_α \ B_β) ⊆ D⁺(λ,β) ∪ ([λ, λ+ω) \ B_β) ∪ ({λ} \ B_β)` — finite, by coherence at
the single pair (λ,β) and fan-cofiniteness 3.8(3). So `{(λ+m, χ_{B_{λ+m}}) : m ≥ 1}` is
bounded in `D(ρ₃)` (top `(β, χ_C)`, `C := B_β ∪` that finite set), and §51's (Q-rows) is
settled: **the canonical rows are not strongly unbounded — every fan witnesses it.** Two
corrections to §51's record follow. Its closing remark ("joint absorption would confine
infinitely many rows' deviations to one finite set — a very rigid alignment that ρ₃'s
oscillation plausibly forbids") was wrong: the rigid alignment is realized, everywhere, by
the cheapest structure in sight. And its two-sided note "absorbed rows are exactly the
hard-to-cover elements" fails for these witnesses — they are cover-trivial:

**Lemma I′ (successor collapse) [proved].** For any coherent e: `D(e)` is fiber-special iff
its restriction to limit levels is. *Proof of the substantive direction.* Given a
σ-down-finite cover `{R_n}` of the limit-level suborder, split the successor levels as
`R′_{n,k,T} := {(λ+k, s) : (λ, s↾λ) ∈ R_n, s↾[λ, λ+k) = T}` (λ limit-or-0, k ≥ 1,
`T ∈ ω^k` — countably many pieces). If `(λ+k, s) ⊑ u = (β,t)` then `(λ, s↾λ) ⊑ u`; and if
β = μ+j is itself a successor then, λ being a limit ≤ μ, also `(λ, s↾λ) ⊑ (μ, t↾μ)`. So
restriction maps `R′_{n,k,T} ∩ ↓u` injectively (s is recovered from s↾λ and T) into the
intersection of `R_n` with a limit-level down-set — finite. ∎ So Theorem L costs the crux
nothing: the absorbed families are successor-padding, coverable for free. The invariant
content of §50's crux — and the true residue of Q-rows — lives at limit levels:
> **(Q-rows-lim)** Is `{(λ, B_λ) : λ ∈ Λ}` strongly unbounded — i.e. is
> `⋃_{λ∈I}(B_λ \ B_β)` infinite for every β and every infinite `I ⊆ Λ ∩ β`? (At limit
> levels the fan trick is dead: `B_λ ∩ Λ` is finite — 3.8(2) at n = 0 — so limit rows do
> not contain their own fan-bottoms.)

**Theorem M (the pruning formula) [proved].** For α < β put `λ_F(α,β) := max(F(α,β) ∖ {α})`
and `W := ρ₁(α,β)`. For every ξ with `λ_F(α,β) < ξ < α`:
1. `ρ₀(ξ,β) = ρ₀(α,β)⌢ρ₀(ξ,α)` — Lemma 1.6(b) at (ξ,α,β), since `min(F(α,β)\ξ) = α` there;
2. `ρ₁(ξ,β) = max(W, ρ₁(ξ,α))`;
3. **`ρ₃(ξ,β) = 1 iff ρ₃(ξ,α) = 1 and ρ₁(ξ,α) ≥ W`.**
Consequences for the deviation sets the game runs on:
- **(M1) one-sided pruning.** `B_β ∩ (λ_F(α,β), α) ⊆ B_α`: above the full trace, the later
  row only turns coordinates *off*; all of `D⁻(α,β)` lives at or below `λ_F(α,β)`.
- **(M2)** `D⁺(α,β) ∩ (λ_F, α) = {ξ ∈ (λ_F, α) : ρ₃(ξ,α) = 1, ρ₁(ξ,α) < W}` — *the walk
  from β prunes exactly α's ρ₁-cheap ones* — finite outright by 1.16(a), re-deriving
  coherence above the trace and identifying the deviation set as a ρ₁-object.
- **(M3) bars diverge [proved].** Along any infinite `I ⊆ β` (ordered `α_n ↗ γ := sup`),
  `ρ₁(α_n, β) → ∞`: for γ = β since `ρ₁(α,β) ≥ |C_β ∩ α|`; for γ < β apply (1) at the
  triple (α,γ,β) to get `ρ₁(α,β) ≥ ρ₁(α,γ) ≥ |C_γ ∩ α|` on the tail of I above `λ_F(γ,β)`.

**The threshold sequence θ(ρ₃) [proved].** For λ limit-or-0 and λ < α let
`thr_α(λ) :=` the least N such that `ρ₃(λ+n, α) = 1` for all n ≥ N with λ+n < α
(well-defined by Lemma 3.6). The sequence `θ := ⟨thr_α⟩`:
- **(T1)** is fan-cofinite by construction (3.6 *is* well-definedness);
- **(T2) finite-to-one:** `{λ : λ+ω ≤ α, thr_α(λ) ≤ n}` is finite — else the column Λ+n
  meets `B_α` infinitely, against 3.8(2);
- **(T3) coherent:** `{λ : λ+ω ≤ α, thr_α(λ) ≠ thr_β(λ)}` is finite for α < β — a fan with
  `thr_α < thr_β` contains a point of `B_α \ B_β` (some λ+m, m ≥ thr_α(λ), with
  `ρ₃(λ+m,β) = 0`, which exists by minimality of `thr_β`), a fan with `thr_α > thr_β`
  symmetrically a point of `(B_β ∩ α) \ B_α`, and distinct fans give distinct points of the
  finite set `B_α △ (B_β ∩ α)`. ∎
So **θ(ρ₃) is a coherent, finite-to-one, ω-valued sequence on the fan-top index Λ — a
ρ₁-species object canonically extracted from ρ₃**: Lemma 3.8's clauses (2) and (3) are
exactly "θ is finite-to-one" and "θ is well-defined". Whether θ is *nontrivial* is not
established — named **(Q-thr)** — and neither implication with ρ₃'s nontriviality is
visible: the sub-threshold scatter (ones of `B_β` below its own thresholds) can be infinite
in total (finitely many per column, infinitely many columns), so a θ-trivialization would
not obviously trivialize ρ₃, nor conversely. (Pointer: JIMJ's shift operation `T^{(m)}`
(§2) acts within fans; the suspicion that θ is the invariant connecting `T(ρ₃)` to its
shift chain is natural and unexplored.)

**Theorem N (absorption = threshold domination + scatter alignment) [proved].** Fix
α < β and a fan λ with λ+ω ≤ α. Then
`D⁺(α,β) ∩ [λ, λ+ω) = {λ+n : n ≥ thr_α(λ), ρ₃(λ+n,β) = 0} ∪ {λ+n ∈ B_α : n < thr_α(λ),
ρ₃(λ+n,β) = 0}`, where the first ("tail") set is nonempty **iff** `thr_α(λ) < thr_β(λ)`
(and is then contained in `[thr_α(λ), thr_β(λ))`), and the second is α's sub-threshold
scatter escaping `B_β`. Hence for finite F: `D⁺(α,β) ⊆ F` iff **(A)** every fan with
`thr_α(λ) < thr_β(λ)` has its tail-witnesses inside F, and **(B)** α's scatter escapes
`B_β` only inside F (the top fan, λ < α < λ+ω, is successor territory — Lemma I). So:
> **(Q-rows-lim) is exactly a one-sided uniformization question for θ(ρ₃):** strong
> unboundedness of the limit rows fails at (β, I, F) iff for every α ∈ I the *downward*
> θ-deviations `{λ : thr_α(λ) < thr_β(λ)}` concentrate their witnesses in F and the
> scatters align mod F. The binary absorption game over ρ₃ **descends** to an ω-valued
> domination game over the coherent finite-to-one θ — one level down, landing in ρ₁'s
> species, where the classical finite-to-one machinery (1.15–1.17) lives. The program's
> self-similarity signature (§32, §50, §51) is here an exact identity of games.

**Corollary N1 (cheap window fans leak) [proved].** If `λ_F(α,β) < λ`, `λ+ω ≤ α`,
`W := ρ₁(α,β) ≥ 3`, and `thr_α(λ) ≤ W−2`, then `λ+(W−2) ∈ D⁺(α,β)`. *Proof.* n := W−2 ≥
thr_α(λ) gives `ρ₃(λ+n, α) = 1`; arrival rigidity under (c)+(d) forces `ρ₁(λ+n, α)` = the
last weight ∈ {n−1, 0}, both < W; M(3) prunes. ∎ The deviation witness is *explicit*, at a
controlled column — the CH-adversary's §50 block game meets it head-on.

**Corollary N2 (the necessary geometry) [proved].** Let `c(α, w) := max{λ : λ+ω ≤ α,
thr_α(λ) ≤ w}` (a maximum over a finite set, by T2). If `⋃_{α∈I}(B_α \ B_β) ⊆ F` then for
every α ∈ I with `ρ₁(α,β) ≥ 3`: **`c(α, ρ₁(α,β)−2) ≤ max(λ_F(α,β), max F)`** — all of α's
cheap fans must hide at or below the walk's own trace (or inside F). With M3's diverging
bars, a Q-rows-lim failure needs the trace to chase an ever-growing cheap region along all
of I — the C-sequence must be persistently *front-loaded* along the family. Both sides
look constructible: the condition is not absurd (traces do climb toward sup I) and not
free (T2 makes cheap fans few, but says nothing about *where* they sit). Q-rows-lim is
unresolved this session — but it is now a quantitative C-sequence/walk question, with the
below-trace scatter (B) as its recursive residue.

**Theorem O (CH cannot slam the Q-T gate) [careful-prose].**
Con(ZFC) ⟹ Con(ZFC + CH + "`T(ρ₃)` is special").
*Proof sketch.* First, a level-absoluteness lemma [proved]: for coherent a, in any outer
model with the same ω₁, `T(a)` *is the same set* — a node at level α is a_α plus a finite
patch, finite patches are absolute, so the =*-closure grows no new nodes. Now force over a
CH-model with the Baumgartner–Malitz–Reinhardt specializing poset of `T(ρ₃)` (finite
partial `f : T → ω` injective on chains): ccc for any Aronszajn tree (BMR 1970), and
`T(ρ₃)` is Aronszajn in ZFC (coherent + nontrivial: Handbook 3.4, 3.8 and the remark after
3.11; verified §46–§51). The poset has size ℵ₁ and is ccc, so ω₁ survives and nice-name
counting keeps `2^ω = ℵ₁`; the C-sequence and ρ₃ are untouched, the tree is unchanged by
level-absoluteness, and the generic specializes it. ∎
Consequences for the dichotomy:
- **"CH ⟹ `T(ρ₃)` non-special" is false.** The Theorem-J-contrapositive kill (find a
  CH-model where the gate fails) cannot be won from CH alone: the adversary needs a
  ◊-style construction of a *non-special Lipschitz coherent* tree, and the classical
  mechanism for ◊-non-specialness — Souslin subtrees — is dead for `T(ρ₃)` in ZFC
  (hereditary non-Souslinness, §51 resource 3). A genuinely new mechanism is required;
  independent classical interest, both ways.
- In the specialized model CH holds *and* the necessary gate for fiber-specialness stands
  open — a canonical test model where the sharpened crux "is `D(ρ₃)` fiber-special under
  CH?" has its necessary condition satisfied by force. (Theorem J is not reversible — the
  dips — so nothing further is free.)
- Under MA_ω₁ the gate is trivially open (every Aronszajn tree is special) — consistent
  with the program's MA side.

**Status after the attack.**
- **(Q-rows): resolved, NO** (Theorem L) — the first of §51's subproblems settled, in ZFC,
  by successor riding; benign for the crux (Lemma I′), corrective for two §51 side-remarks.
  The absorption phenomenon the game is about provably *occurs* on canonical rows — but
  only as successor-padding; §50's CH-adversary gains nothing at successor levels, and its
  block-accumulations must be built at limit levels, where **(Q-rows-lim)** is open.
- **The crux descends.** Fiber-specialness of `D(ρ₃)` — Q-rows-lim included — is governed
  (Theorems M, N) by the threshold sequence θ(ρ₃): coherent, finite-to-one, ω-valued on Λ,
  with the pruning bar `ρ₁(α,β)` and the trace `λ_F(α,β)` as the game's two dials, explicit
  leak witnesses (N1), a quantitative front-loading criterion (N2), and the sub-threshold
  scatter as the recursive residue. The regress met at every level of the program is now an
  exact descent: ρ₃'s binary absorption game *is* θ's ω-valued one-sided game.
- **(Q-T): bracketed from one side** (Theorem O) — the gate is consistently open with CH,
  so the CH-kill branch needs strictly more than CH plus a new non-specialness mechanism.
  Q-T's ZFC content stays open, as do (Q-thr) and (Q-rows-lim).
- Verified base extended and corrected: normalizations (a)/(c)/(d) and Def 3.3's weak tie
  convention verbatim; Lemma 1.6 as the factoring engine; JIMJ Lemma 1.9 read (specialness
  a hypothesis there — no hidden dichotomy); resource-2 citations relocated to Handbook
  1.15–1.17; all new walk formulas machine-sampled on a randomized (d)-sequence.

## 53. (Q-thr) falls (answer: NONTRIVIAL) — the finite-to-one engine applies directly; Theorem B has a downward dual; and the dense failure mode of (Q-rows-lim) is killed in ZFC

§52 left three open: **(Q-thr)** (is θ(ρ₃) nontrivial?), **(Q-rows-lim)**, and **(Q-T)**.
One of them was never as hard as it looked. §52 framed (Q-thr) as a question about the
*relation* between θ's nontriviality and ρ₃'s — "neither implication is visible" — and
that framing hid the fact that θ's nontriviality needs no relation to ρ₃ at all: it
follows from (T2) and (T3) alone, by the same three-line argument that makes ρ₁
nontrivial in ZFC. Settling it turns §52's descent from "the game descends to θ" into
"the game descends to a *genuine coherent Aronszajn object*", and — via a downward dual
of Theorem B proved below — kills the natural failure mode of (Q-rows-lim).

**Source round 4 [verified, verbatim].** From `coherent.pdf` (Handbook ch. 1), read
first-hand this session:
- **1.16 Lemma**, verbatim: "For all α < β < ω1 and n < ω, (a) {ξ ≤ α : ρ1(ξ, α) ≤ n} is
  finite, (b) {ξ ≤ α : ρ1(ξ, α) ≠ ρ1(ξ, β)} is finite." Both with full proofs (induction
  on order-type-ω subsets). This is the finite-to-one + coherence pair for ρ₁.
- **1.17 Remark**, verbatim: "the sequence (ρ1)α : α → ω (α < ω1) of finite-to-one
  functions is coherent in the sense that (ρ1)α =∗ (ρ1)β↾α whenever α ≤ β. … The
  corresponding tree T(ρ1) = {t : α → ω : α < ω1 and t =∗ (ρ1)α} is a homogeneous,
  special Aronszajn tree". **Specialness is asserted, not proved, in this source** —
  §51's "resource 2" reading stands, and the engine behind it is not exhibited. Record
  this: 1.17 cannot be *cited as a proof* for any analogue.
- **3.11 Definition** (the coherence/nontriviality vocabulary), verbatim: "We say that a
  is nontrivial if there is no h : ω1 → ω such that h↾α =∗ aα for all α < ω1"; and the
  sentence after: "T(a) … is such an Aronszajn tree whenever a : [ω1]2 → ω is coherent
  and nontrivial." So **coherent + nontrivial ⟹ T(a) Aronszajn** is on the record.
- **3.8 Lemma**, re-verified verbatim: "(1) Bα =∗ Bβ ∩ α for α < β; (2) (Λ + n) ∩ Bβ is
  finite for all n < ω and β < ω1; (3) {λ + n : n < ω} ⊆∗ Bβ whenever λ + ω ≤ β." §52's
  T1/T2 rest on (3)/(2) exactly as claimed.
- **New resource (3.12–3.13), unopened until now.** ρ₃ is *nowhere dense* in the
  Handbook's sense, "for the simple reason that ω1 can be covered by countably many sets
  Λ+n (n < ω) that are orthogonal to ρ3" — i.e. **the index ω₁ has a canonical countable
  decomposition into sets meeting every row of ρ₃ finitely.** This is a σ-decomposition
  of the *index*, not of the fiber order `D(ρ₃)`, so it is not fiber-specialness (§50)
  and does not settle the crux — but it is the exact shape of the object the crux asks
  for, one level down, and it is free in ZFC. Filed as a resource; the gap between it and
  fiber-specialness is precisely the dips.

**Theorem P ((Q-thr) is answered: θ(ρ₃) is NONTRIVIAL) [proved, ZFC].** There is no
`Θ : Λ → ω` with `Θ↾dom(thr_β) =* thr_β` for all β.
*Proof.* Suppose there were. Fix `n < ω` and put `S_n := {λ ∈ Λ : Θ(λ) ≤ n}`. For every
β, `S_n ∩ dom(thr_β) ⊆ {λ ∈ dom(thr_β) : thr_β(λ) ≤ n} ∪ {λ : Θ(λ) ≠ thr_β(λ)}`: the
first set is finite by **(T2)** (finite-to-one, §52 — itself Lemma 3.8(2)), the second by
the assumed trivialization. So `S_n` meets every `dom(thr_β)` finitely; since the
`dom(thr_β)` exhaust Λ, every proper initial segment of `S_n` is finite, so `S_n` has
order type ≤ ω and is countable. Then `Λ = ⋃_{n<ω} S_n` is countable — false. ∎
*Remarks.* (i) The argument uses only **(T2) + (T3)**; it is the classical engine —
verbatim the reason ρ₁ is nontrivial, from 1.16(a) — and needs no walk geometry and no
contact with ρ₃'s own nontriviality. §52 missed it by asking the harder question
(*implications between* θ's and ρ₃'s nontriviality) instead of the direct one. General
form, worth stating once: **a coherent sequence on ω₁ with finite-to-one rows is
nontrivial.** (ii) Consequence, by Handbook 3.11: `T(θ)` is a **coherent Aronszajn tree
in ZFC**. So §52's descent is not a descent into a degenerate object — had θ been
trivial, Theorem N's game would have collapsed and the reduction would have been vacuous.
(iii) *Not* claimed: that `T(θ)` is special. That would be the exact analogue of 1.17,
whose proof this source does not contain (above), so it is **[open]**, filed as
**(Q-T-θ)** — and note it is the same shape as (Q-T) one level down, the program's
self-similarity again.

**Theorem B⁻ (downward dip systems also force triviality) [proved, ZFC].** For coherent
`e` put `D⁻(μ, γ) := {ξ < μ : e_μ(ξ) < e_γ(ξ)}`. If there are finite `X_μ ⊆ μ` with
`V_γ := ⋃_{μ<γ}(D⁻(μ,γ) \ X_μ)` finite for every γ, then `e` is trivial. (Converse as in
Theorem A: `X_μ := {ξ : e_μ(ξ) ≠ E(ξ)}`.)
*Proof.* Call γ *ξ-honest* if `γ > ξ` and `ξ ∉ X_γ ∪ V_γ`.
(1) **Values are non-increasing along honest levels.** If `ξ < μ < γ` with μ, γ both
ξ-honest and `e_μ(ξ) < e_γ(ξ)`, then `ξ ∈ D⁻(μ,γ) \ X_μ ⊆ V_γ`, contradicting γ's
honesty. (2) **Only finitely many ξ have a bounded honest set.** If `H_ξ := {γ : γ
ξ-honest}` is bounded by `δ_ξ`, then `ξ ∈ X_γ ∪ V_γ` for every `γ > δ_ξ`; so for each γ
the set `{ξ : δ_ξ < γ}` is inside the finite `X_γ ∪ V_γ`. These finite sets increase with
γ, and a non-decreasing ω-sequence-of-cardinalities along ω₁ is eventually constant, so
their union `B := {ξ : H_ξ bounded}` is **finite**. (3) For `ξ ∉ B`, the honest values
`e_γ(ξ)` (γ ∈ H_ξ, unbounded) are non-increasing in ω by (1), hence **eventually
constant**; call the value `E(ξ)`, attained above some `σ(ξ)`. Set `E := 0` on B.
(4) Fix γ. Take `δ* > sup{σ(ξ) : ξ < γ}` (a countable sup) with `δ* > γ`. For every
`ξ < γ` outside the finite set `B ∪ X_{δ*} ∪ V_{δ*}`, δ* is ξ-honest and above σ(ξ), so
`E(ξ) = e_{δ*}(ξ)`; and `e_{δ*}↾γ =* e_γ` by coherence. Hence `E↾γ =* e_γ`. ∎
*Why it is worth having.* It is **strictly easier** than Theorem B — step (3) is free
(decreasing ℕ-values stabilize), where Theorem B needed the witness-concentration
argument for unbounded columns. And it is the theorem **matched to ρ₃'s geometry**:
(M1) says all of `D⁻(α,β)` lives at or below the full trace `λ_F(α,β)`, so the downward
side is exactly the side ρ₃'s pruning formula controls. The proof relativizes to a
cofinal set of levels, as Theorem B's does.

**Theorem Q (the dense failure mode of (Q-rows-lim) is impossible) [proved, ZFC].**
Say (Q-rows-lim) *fails densely* if there is a cofinal `C ⊆ ω₁` such that for every
`β ∈ C` there is a finite `F_β` with `⋃_{λ ∈ Λ∩β}(B_λ \ B_β) ⊆ F_β` — i.e. the failure is
witnessed by the **full** family of limit rows below β, cofinally often. This is
impossible.
*Proof.* Fix `β ∈ C`. Put `Λ_{F_β} := {μ ∈ Λ : F_β ∩ [μ, μ+ω) ≠ ∅}`, finite. By
**Theorem N**, if `λ < β` is a limit and μ is a fan with `μ+ω ≤ λ` and
`thr_λ(μ) < thr_β(μ)`, then `D⁺(λ,β)` meets `[μ, μ+ω)`; since that deviation lies in
`F_β`, `μ ∈ Λ_{F_β}`. So `{μ : thr_λ(μ) < thr_β(μ)} ⊆ Λ_{F_β}` for **every** `λ < β` —
that is, with `X_λ := ∅`, `V_β = ⋃_{λ<β} D⁻_θ(λ,β) ⊆ Λ_{F_β}` is finite. Cofinally in
ω₁ this is a downward dip system for θ on the cofinal level set C, so **Theorem B⁻**
(relativized) makes θ trivial — contradicting **Theorem P**. ∎
*What it does and does not settle.* (Q-rows-lim) quantifies over *some* infinite
`I ⊆ Λ∩β`, so its failure only supplies a countable I, and a countable I is not a dip
system. Theorem Q therefore does not resolve (Q-rows-lim); it **removes its natural
shape**. Any counterexample must be *sparse*: for each β only a thin infinite subfamily
can be jointly absorbed, never the full family below β on a cofinal set of levels. In the
CH-adversary's terms (§50), the block-accumulation game cannot be won by a uniform
absorption over all limit rows — the adversary must select, and the selection is itself
the ω₁-obstruction the whole program keeps meeting. Combined with N2's front-loading
criterion, the surviving target is narrow and quantitative.

**Machine-checked this session (`transport-kernel/TransportKernel/OmegaOneCoherent.lean`).**
**Theorem B⁻ is formal**: `omega1_downDip_trivial`, with the structure `DownDip C`
(finite `X μ`, leftover finite at every top) transcribed directly from the statement
above, and `omega1_downDip_iff_trivial` — *a coherent sequence on ω₁ admits a downward
dip system **iff** it is trivial* — the converse supplied by `DownDip.ofTrivial`, which
also settles non-vacuity (the structure is inhabited exactly on the trivial sequences).
The formal proof follows the prose step for step: `honest_antitone` (values
non-increasing along honest levels), `bad_finite` (only finitely many coordinates go
permanently unvouched — by concentrating countably many bounds at one level, regularity
of ℵ₁ again), `eval_eq_of_honest` (stabilization: `≤` by antitonicity, `≥` by leastness
of `sInf`), then the four-finite-sets assembly. **This is the program's first
machine-checked dip theorem**, and it matters here because **Theorem Q depends on it** —
the kill of (Q-rows-lim)'s dense failure mode now rests on a formal theorem plus Theorem
P, not on two fresh prose arguments. *Asymmetry, stated:* the *upward* Theorem B remains
careful-prose only. Its witness-concentration step for unbounded columns is exactly what
B⁻ does not need, and it is the harder half; the Corollary to Question 1′
(level-factored ⟹ trivial) still rests on it unformalized.

Theorem P's engine is also formal at actual ω₁, in the general form:
`omega1_finiteToOne_not_trivial` — *a coherent sequence on ω₁ with finite-to-one rows is
nontrivial* — with `FiniteToOne C := ∀ w n, {u | u < w ∧ C.e w u ≤ n}.Finite` (Handbook
1.16(a) verbatim), proved via `countable_of_segments_finite` (the map
`u ↦ |S ∩ Iio u|` is strictly monotone, so a segment-finite set is countable — order type
≤ ω without building an enumeration) and `bounded_of_countable` (regularity of ℵ₁, reusing
the existing σ-directedness instance). Composed with the existing reps theorem:
`omega1_finiteToOne_no_reps` — **a coherent finite-to-one sequence on ω₁ admits no
monotone representative system**. No `sorry`; standard three axioms.
*The point for the trusted base.* `nontrivial_coherent_no_reps` was conditional on an
imported negative existential ("Todorcevic's walks are nontrivial"), whose proof is
exactly the argument now formalized. What remains cited is only the *positive*,
construction-checkable fact that a coherent finite-to-one sequence exists (Handbook
1.16(a)+(b) for ρ₁ — two induction computations on walks). The obstruction is no longer
conditional on a cited nontriviality theorem. (Honest scope: the Lean statement is an
implication; ρ₁ itself is not formalized, so non-vacuity still rests on 1.16.)

**Status after §53.**
- **(Q-thr): resolved, NONTRIVIAL** (Theorem P, ZFC), machine-checked in general form.
  §52's descent lands on a coherent Aronszajn tree `T(θ)`, not a degenerate object.
- **New tool: Theorem B⁻**, the downward dual of Theorem B — easier, matched to the
  one-sided pruning (M1) that governs ρ₃, and **machine-checked** as an equivalence
  (`omega1_downDip_iff_trivial`): the program's first formal dip theorem. The upward
  Theorem B stays careful-prose.
- **(Q-rows-lim): narrowed, not resolved** (Theorem Q) — the dense/uniform failure mode
  is impossible in ZFC; only sparse failures survive. Open.
- **(Q-T): open** as in §52; **(Q-T-θ)** (is `T(θ)` special?) added as its one-level-down
  twin, with the record that 1.17 asserts specialness for `T(ρ₁)` **without proof**, so
  no analogue can be cited.
- Verified base extended: 1.16 and 1.17 read verbatim (1.17's specialness unproved in
  source), 3.11's nontriviality definition and the coherent+nontrivial ⟹ Aronszajn
  sentence, and the new 3.12–3.13 resource (ρ₃ nowhere dense; ω₁ = ⋃ₙ (Λ+n) with each
  Λ+n orthogonal to ρ₃).

## 54. Going at the central question: the trace formula made explicit, Theorem V (fans above the trace are β-expensive), the thr_β-transfer route closed as vacuous, and (Q-rows-lim) reduced to limits of limits

The central open problem is `ρ₃` under CH, which §50 reduced to **is `D(ρ₃)` fiber-special?**
and §51–§53 reduced further to **(Q-rows-lim)** plus the gate **(Q-T)**. This session went
at (Q-rows-lim) directly. Outcome: one route closed as *vacuous* (worth recording — it is
the natural one), one new ZFC theorem constraining where deviations can live, an explicit
formula for the dial N2 left implicit, and a second reduction of (Q-rows-lim)'s index set.
The question itself remains **open**.

All walk-level formulas below are re-verified numerically by `tools/walk-check.py`
(randomized (a),(c),(d),(e)-conforming C-sequences over ordinals below `ω²·3`, so that
limits *of limits* genuinely exist — §52's model, which stopped below `ω·25`, had none):
trace formula 972 instances, Theorem V 3108, M(3) 36065, Theorem S every limit, all pass.

**The trace formula [proved + numerically checked].** Unfolding Handbook **1.4**
(`F(α,β) = F(α, min(C_β\α)) ∪ ⋃_{ξ∈C_β∩α} F(ξ,α)`, `F(γ,γ) = {γ}`) along the walk gives
`F(λ,β) = {λ} ∪ ⋃_i ⋃_{ξ ∈ C_{β_i} ∩ λ} F(ξ,λ)` over the walk's stops `β = β_0 > … > λ`,
and `max F(ξ,λ) = ξ`, so
> **`λ_F(λ,β) = max_i max(C_{β_i} ∩ λ)`** — the largest ladder point below `λ` occurring in
> the ladder of *any* stop of the walk `β → λ`.
Two riders. (i) The weights are `|C_{β_i} ∩ λ|`, so `ρ₁(λ,β) = max_i |C_{β_i} ∩ λ|`: the
trace is the max of the *positions*, the bar is the max of the *sizes*. (ii) Under
normalization (d) those are the same data — if `max(C_{β_i} ∩ λ) = ν + r + 1` (ν limit),
that element occupies place `r`, so `|C_{β_i} ∩ λ| = r+1` exactly. So N2's two dials are
one object read two ways, and the front-loading question is: *can the stop achieving the
largest position fail to achieve the largest size?* — i.e. can a stop jump over a fan with
a high place but a low landing?

**Theorem V (fans above the trace are β-expensive) [proved + numerically checked].** Let
`μ` be a fan with `μ + ω ≤ λ < β`, let `W := ρ₁(λ,β) ≥ 1`, and suppose
`λ_F(λ,β) < μ`. Then `ρ₃(μ+n, β) = 0` for **every** `n ≤ W`; hence
`thr_β(μ) ≥ W + 1`.
*Proof.* Every `ξ = μ+n` lies in `(λ_F(λ,β), λ)`, so M(3) applies: `ρ₃(ξ,β) = 1` iff
`ρ₃(ξ,λ) = 1` and `ρ₁(ξ,λ) ≥ W`. If `ρ₃(ξ,λ) = 0` we are done. If `ρ₃(ξ,λ) = 1` then
`ρ₁(ξ,λ)` *is* the last weight of the walk `λ → ξ`, and arrival rigidity under (c)+(d)
makes that `n−1` (arrival at `μ+n = μ+(n−1)+1`, intrinsically at place `n−1`) or `0`
(arrival off `C_{ξ+1} = {ξ}`). For `n ≤ W` both are `< W`, so M(3) prunes. ∎
(`W ≥ 1` is needed and sharp: at `W = 0` the statement fails, and the numeric run flagged
exactly those instances before the hypothesis was added.)

**Corollary V1 (front-loading past the β-cheap region is automatic) [proved].** For every
`k` and every limit `λ < β` with `ρ₁(λ,β) ≥ k`: every fan `μ` with `μ+ω ≤ λ` and
`thr_β(μ) ≤ k` satisfies `μ ≤ λ_F(λ,β)`. So the trace *always* dominates the β-cheap
fans below its level — no hypothesis, no C-sequence condition.

**The thr_β-transfer route is VACUOUS — recorded so it is not retried.** The natural
attack on (Q-rows-lim) is to replace N1/N2's dependence on `thr_α` (α's *own* thresholds,
which move with α) by the single fixed `thr_β`. Routing N1's second case through M1 does
give a clean statement — *if `λ_F(λ,β) < μ`, `μ+ω ≤ λ`, and `W ≥ max(3, thr_β(μ)+2)`, then
`μ + (W−2) ∈ B_λ \ B_β`* — and it was worth writing down, because it is **empty**:
Theorem V says `thr_β(μ) ≥ W+1` for exactly those `μ`, so the hypothesis
`thr_β(μ) ≤ W−2` is never met. (The numeric run found 0 firing instances out of ~6600
candidate `(β,λ,μ)` triples, which is what prompted looking for Theorem V.) **Consequence
for the record: N2's open content is genuinely about `thr_α`, and cannot be transferred to
`thr_β`.** V1 is the exact reason — the β-side front-loading N2 asks about is free, so the
question lives entirely on the α-side.

**Corollary V2 (the leak inequality) [proved].** Applying Theorem V inside `λ`: for a fan
`μ` and any limit `ν` with `μ+ω ≤ ν < λ` and `λ_F(ν,λ) < μ`, `thr_λ(μ) ≥ ρ₁(ν,λ)+1`. Since
N1 needs `thr_λ(μ) ≤ ρ₁(λ,β)` to produce a leak at `μ`, a leak requires
> `sup{ ρ₁(ν,λ) : μ+ω ≤ ν < λ, λ_F(ν,λ) < μ } < ρ₁(λ,β)`
— the *inner* walks (down from λ) must be cheaper than the *outer* one (down from β). This
is the surviving quantitative form of N2, now with both sides walk-computable.

**Theorem S (fan-completion riding) [proved + numerically checked].** *Under the extra
normalization* **(e)** `C_{δ+ω} = {δ+n+1 : n < ω}` for every limit `δ`:
`B_{δ+ω} = B_δ ∪ [δ, δ+ω)`.
*Proof.* For `ξ = δ+j` (`j ≥ 1`) the walk is the single step off `δ+j = δ+(j−1)+1 ∈
C_{δ+ω}`, so last = max and `ρ₃ = 1`. For `ξ ≤ δ` the walk steps to `δ+1` (weight
`|C_{δ+ω} ∩ ξ| = 0`), then to `δ` by (a) (weight 0), then walks `δ → ξ`; prepending `⟨0,0⟩`
changes neither the last entry nor the maximum, so `ρ₃(ξ, δ+ω) = ρ₃(ξ,δ)` for `ξ < δ` and
`ρ₃(δ, δ+ω) = 1`. ∎ This is **Lemma I one level up** — where successors ride their fans,
fan-tops ride their whole fan.
*Why (e) is needed, exactly:* without it, write `N_δ := |C_{δ+ω} ∩ δ|`; then the walk
`δ+ω → δ` reads `⟨N_δ, 0, …, 0⟩`, so **`ρ₃(δ, δ+ω) = 1` iff `N_δ = 0`**. (d) forces only
the *tail* of `C_{δ+ω}` into the fan, not its head. (e) is the harmless completion — it is
the standard "ladders of `δ+ω` live in the fan of `δ`" choice, and §51 already noted the
C-sequence is ours to choose.

**Theorem T (the ω-successor limit rows are strongly unbounded) [proved].** Under (e), for
every `β` and every infinite `I₀ ⊆ {δ ∈ Λ : δ+ω ≤ β}`, the set
`⋃_{δ∈I₀} (B_{δ+ω} \ B_β)` is infinite.
*Proof.* `δ ∈ B_{δ+ω}` by Theorem S. By Lemma 3.8(2) at `n = 0`, `Λ ∩ B_β` is finite, so
`δ ∉ B_β` for all but finitely many `δ ∈ I₀`; each such `δ` is a point of
`B_{δ+ω} \ B_β`, and distinct `δ` are distinct points. ∎

**Theorem U ((Q-rows-lim) reduces to limits of limits) [proved].** Every `λ ∈ Λ` is either
a limit of limits or of the form `δ+ω` with `δ ∈ Λ ∪ {0}` (if `sup(Λ ∩ λ) = δ < λ` then
`(δ,λ)` has no limits, forcing `λ = δ+ω`). By Theorem T an infinite family drawn from the
second kind is always strongly unbounded, so a (Q-rows-lim) counterexample family may be
assumed to consist of **limits of limits**. Exactly parallel to Lemma I′ one level up —
and note the same trade: Theorem T costs the crux nothing, it only removes the cheap part
of the index.

**Methodological caveat, recorded because it nearly produced a false verdict.** The
numeric model *cannot* probe (Q-rows-lim) itself. A direct probe over the model reports
that most limit rows are fully absorbed (`B_λ ⊆ B_β` for ~2/3 of rows, and greedy families
of 14 rows out of 17 with a union of size ≤ 4) — which reads as strong evidence that
(Q-rows-lim) **fails**. It is an artefact: truncation destroys Lemma 3.8(2)'s finiteness
(the model has ~17 limits below each β, so "`Λ ∩ B_β` is finite" imposes nothing), and
3.8(2) is precisely Theorem T's engine. **Numeric checks over the truncated model are
sound for identities and formulas and worthless for finiteness phenomena.** §52's uses
were of the first kind; this is the boundary.

**Status after §54.**
- **(Q-rows-lim): still open**, index set reduced to limits of limits (Theorem U) on top of
  §53's Theorem Q (no dense failures), with the surviving criterion now the walk-computable
  inequality V2 and the explicit trace formula behind it.
- **New ZFC facts**: the trace formula and its (d)-rider; Theorem V and Corollaries V1, V2;
  Theorems S, T, U.
- **Route closed**: the `thr_β`-transfer of N1/N2 is vacuous (Theorem V) — N2's content is
  irreducibly on the `thr_α` side.
- **(Q-T), (Q-T-θ), and the central question — is `ρ₃` strongly dip-schedulable under CH —
  remain open.** Nothing here decides them; what changed is that the residual is smaller
  and, for the first time, entirely written in walk-computable quantities.
