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

## 5. Verdict (revised after §2′)

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
