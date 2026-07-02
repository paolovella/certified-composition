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
