# Confidentiality Typing — Lean 4 mechanization

A machine-checked encoding of **Paper 1: the IMP timing instance** of the
confidentiality-typing framework. Every result below is proved in Lean 4
(v4.31.0), mathlib-free, with **no `sorry`** and only the three standard
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) — the
central meta-theorems use none of them.

```
lake build          # builds all four layers
```

## Layout

| File | Doc section | Content |
|---|---|---|
| `ConfTyping/Imp.lean`    | §1–2 | syntax, instrumented semantics (relation **and** evaluator), `determinism` (Sem-Det) |
| `ConfTyping/Obs.lean`    | §3–5 | observations, parametric `J`, `J_NI`, A3 + separability, adversaries, generation (Lemma 1) |
| `ConfTyping/Pleak.lean`  | §7   | the `P_leak` worked example: `wall` constant, `result`/`branch` leak |
| `ConfTyping/Typing.lean` | §6–9 | strata, discharge judgment, T-Reject, conformance + transport, soundness |
| `ConfTyping/Joint.lean`  | framework §4,§8 | joint generation `𝒜̂`, completeness (Thm. 2), separability-equivalence |
| `ConfTyping/TwoSafety.lean` | framework §10 | abstract 2-safety lift; A3-collapse; corrected §10 conjecture |

## Result map

| Lean name | Paper claim |
|---|---|
| `determinism` | (Sem-Det), via `eval`/`Step` equivalence |
| `JNI_postproc` | (A3) post-processing monotonicity for `J_NI` |
| `JNI_separable` | Def. 5 separability holds for `J_NI` (Prop. 2, NI side) |
| `gen_mono` | Lemma 1 (𝒜-monotonicity) |
| `wall_closure` | §7.2 — `wall` discharged at Closure |
| `result_not_closable` | §7.3 — Closure unavailable, Policy *forced* |
| `ReleasesAtMost` / `result_releases_at_most_bit` | §5/§7.3 — the **bounded** Policy obligation: `result` reveals at most the bit `(b≠0)` |
| `result_full_not_bounded_by_bit` | non-vacuity: a full-leak program *fails* the bound (the policy stratum has teeth) |
| `closure_is_const_policy` | framework §5 — Closure is the `φ=const` special case, as a *lemma* not a definitional collapse |
| `branch_not_closable` | §7.4 — residual obligation |
| `reject_Jinvariant` | **Lemma 3** — rejection holds for *every* `J` |
| `Conform` / `transport_JNI` | §6 conformance relation + the §9 gate (Closure half) |
| `transport_releases` | the gate transports the **Policy** half — a proven release bound carries to `deploy` |
| `confidential_transport` | full-strength gate: the *whole* `Confidential` claim (both strata) transports `A → deploy` |
| `pleak_confidential_deploy` | end-to-end: the *running* P_leak leaks at most the bit on `result` |
| `attest_is_not_J_evidence` | §6.1 sharpened — valid attestation coexists with false obligation |
| `soundness` | §9 Boolean soundness |
| `pleak_confidential_local` | §7 end-to-end: `P_leak` confidential vs local adversary, declassifying `result` |
| `branch_residual` | §7.4 — `branch` dischargeable at no stratum |
| `wall_rejection` | §7.5 — attesting a closable obligation is ill-typed |

## The joint layer (Hole 1, localized)

`Joint.lean` mechanizes `𝒜̂ = foldr tup seedObs` and proves, all over `J_NI`,
mathlib-free:

| implication | Lean | mechanism | J_NI | J_ε |
|---|---|---|:--:|:--:|
| joint ⇒ per-channel | `joint_to_perchannel` | projection = A3 | ✓ | ✓ |
| per-channel ⇒ joint | `perchannel_to_joint` | `JNI_separable` | ✓ | **✗** |
| joint ⇒ all post-proc | `completeness_rel_O` (engine) | A3 | ✓ | ✓ |
| primitive factors through join | `mem_is_postproc` (Prop. 1) | projection | ✓ | ✓ |
| joint ⇒ all **derivable** | `completeness_thm2` (Thm. 2) | engine + Prop. 1 | ✓ | ✓ |

`completeness_rel_O` is the *engine* ("every post-processing of the join is
`J_NI`", `∀ f`); Thm. 2 proper needs Prop. 1 (`mem_is_postproc`: real
adversary channels factor through the join) to close the quantifier over
derivable channels rather than all functions. `completeness_thm2` is the
honest statement.

The footprint *is* the story: completeness routes through `JNI_postproc` (A3)
alone — **it never uses the forward direction.** Per-channel generation is
*only* forward, and forward *is* separability (`perchannel_to_joint`, the lone
`JNI_separable` user). So "is per-channel generation sound?" = "is `J`
separable?": yes for `J_NI` (proved), no for `J_ε`.

For *why* the break needs mathlib, and the corrected §10 statement, see the
2-safety characterization below — the naive "separable = 2-safety" coincidence
is **false**, and the corrected version is the actual result.

## The 2-safety characterization — §10 conjecture corrected (`TwoSafety.lean`)

Lift `J` to a binary trace-relation: `J_rel R c o P := ∀ σ≈_Lσ'. R (o⟦c⟧σ)
(o⟦c⟧σ')`, with `J_NI` = `J_rel (·=·)` (`JNI_is_rel`, axiom-free `Iff.rfl`).
Two relation properties: `PairClosed` (congruence for `Val.pair`) and
`PostClosed` (= A3). Then:

| result | Lean | content |
|---|---|---|
| forward over the class | `rel_perchannel_to_joint` | `PairClosed` ⇒ separable |
| backward over the class | `rel_joint_to_perchannel` | `PostClosed` (A3) ⇒ complete |
| **A3 collapse** | `postclosed_collapse` | `PostClosed R` ⇒ `R` total **or** `R ⊆ Eq` |
| **corrected §10** | `qualitative_admissible_is_JNI` | A2 ∧ A3 ⇒ the only nondegenerate 2-safety `J` is `J_NI` |
| **the refutation** | `Rbad_nonseparable` | a deterministic 2-safety `R`, non-`PairClosed`, **non-separable** |
| **k-safety above 2** | `ksafety_above_twosafety` | `notAllDistinct`: admissible (A2∧A3), deterministic, ≠ `J_NI` |
| **k-ary foundation** | `A3_factors_kernel` | simultaneous A3 ⇒ property determined by the *pairwise-equality pattern* (all k) |
| **probe settled** | `no_irreducible_admissible` | no admissible property depends on genuinely k-ary structure |
| **Πₖ characterization** | `simA3_iff_respectsCoarsening` | admissible (sim-A3) ⟺ **up-set of the kernel-coarsening order** (all k) |

**§10's conjecture "separable ⟺ 2-safety" is false.** `Rbad` (equal first
component when both pairs, else blind to non-pairs) is a 2-safety property that
is not `PairClosed`, and `branchO` — non-pair-valued, leaking — gives two
channels each satisfying `J_rel Rbad` whose tuple does not. So **separability
is the congruence-refinement of 2-safety: `separable ⊊ 2-safety`**, no
randomness used.

**The corrected result.** `postclosed_collapse` shows A3 is brutal *at arity 2*
— preservation under *all* unary functions forces a binary `R` to be total or
sub-diagonal (relate one off-diagonal pair, a relabeling drags `R` to total).
A2 (non-triviality) deletes the total relation, reflexivity (A3 again) lifts
`⊆ Eq` to `Eq`. Net (`qualitative_admissible_is_JNI`): **among admissible J, the
only nondegenerate _2-safety_ property is `J_NI`.**

**But this stops at arity 2 — the k-safety hierarchy lives strictly above it.**
A3 is *simultaneous* (one post-processor on the whole observation), and a
function can only *coarsen* a tuple's equality-pattern, never refine it — so A3
closes a property upward to the diagonal but is blind downward, and at arity ≥ 3
that gap is real. `notAllDistinct` (the canonical 3-safety-not-2-safety shape)
is admissible (A2 ∧ A3, `notAllDistinct_postclosed` axiom-free), deterministic,
and satisfied by `branchO` — which `J_NI` rejects. So `ksafety_above_twosafety`
witnesses **admissible 2-safety = `J_NI` ⊊ admissible k-safety (k>2)**, all
qualitative and mathlib-free.

**Three nested regions, not two:**

1. **admissible 2-safety = `J_NI`** (separable) — proved.
2. **proper k-safety, k > 2** (e.g. `notAllDistinct`) — deterministic,
   qualitative, mathlib-free; shown *inhabited* (one witness; not fully
   characterized).
3. **genuine hyperproperties** (not k-safety for any k) = `J_ε` — needs a
   distribution; the *only* region behind the mathlib wall.

So the mathlib boundary is **not** the qualitative boundary and **not** the
2-safety boundary — it is the **k-safety / hyperproperty boundary**, strictly
above both. `postclosed_collapse`, `Rbad`, and `notAllDistinct` are all concrete
relation algebra over `Val`, no distribution. The §10 conjecture is **retired**
(corrected + proved at the 2-safety level), with only "region 3 is inhabited" (a
concrete admissible `J_ε`) deferred to the probabilistic layer.

**What region 2 actually is (the k-ary structure).** It is tempting to call
region 2 "a proper k-safety tower of irreducible properties." That is *wrong*,
and `A3_factors_kernel` proves why: a simultaneous-A3 property of a k-tuple
depends only on the tuple's **kernel** — the pairwise-equality pattern. (The
relabeling sending `x i ↦ x' i` is well-defined exactly when the kernels agree;
A3 transports `P` along it.) So **no admissible property has genuinely k-ary
atoms** (`no_irreducible_admissible`) — everything is a function of the 2-ary
predicates `o_i = o_j`. Yet region 2 is *not* a finite stub: the up-sets of the
partition lattice Πₖ grow with k (`o₁=o₂ ∧ o₃=o₄` is a real k=4 property absent
at k=3), and the k-safety *refutation degree* is unbounded ("at most m distinct
values" needs m+1 traces). So region 2 = **up-sets of Πₖ**: an infinite,
properly-growing, unbounded-refutation-degree family over a **fixed 2-ary atom
basis**. *Mechanized:* admissible ⟹ kernel-determined, all arities
(`A3_factors_kernel`); **the up-set characterization itself** —
`simA3_iff_respectsCoarsening`: a k-safety property is admissible *iff* it is
closed upward under kernel coarsening (an up-set of Πₖ), all k, mathlib-free;
and the k=3 inhabitant (`notAllDistinct`).

*Argued, with the cardinality condition now explicit:* the characterization is
up-sets of the order on **realizable** kernels. For value-rich `Val` (infinitely
many `.int`) every partition of `Fin k` is realizable, so the order is the full
Πₖ and the family grows with k; for a **Boolean-valued channel** only ≤2-block
kernels are realizable and region 2 collapses to a finite stub. So the growth
claim is *conditional on observation cardinality* — "realizable kernels = full
Πₖ" needs `Finset.min'`-style combinatorics that would pull in mathlib, so it
stays argued, the condition pinned rather than hidden. The iff has no such
dependence.

## §11 pre-mechanization checklist (framework doc)

What this instance encodes from the framework's checklist:

- **Item 6 — no `T-Conf-discharges-J`.** The `Discharge` inductive has *only*
  `clo` and `pol` constructors. There is no constructor producing a
  `conformance` discharge or consuming `Ev_attest`. The absence is the
  encoding of "no coercion"; `reject_Jinvariant` proves it holds for all `J`.
- **Policy carries a proof obligation, not a permit.** `pol` requires *both* a
  declared release `φ` (`Pi o φ`, the normative act) *and* a proof
  `ReleasesAtMost c o P φ` that the channel reveals at most `φ`. Declaring a
  channel is **not** a free pass — `result_full_not_bounded_by_bit` shows the
  bound is falsifiable. (v0.1 had the pre-bulletproofing unbounded form
  `o ∈ Π`; that was checklist-item-3 unsound and is fixed in v0.2.)
- **Closure vs Policy is not a signature split.** Both are Σ_sem; the framework
  nests them (`closure_is_const_policy`). We keep three `Stratum` tags anyway,
  so the derivation records *whether a declassification was claimed* — and so
  that nothing tempts folding the genuinely-disjoint Conformance stratum "for
  symmetry".
- **`Admissible` is a property of `J`, used à la carte.** `J` is a bare
  parameter `JTy`; `JNI_postproc` (A3) and `JNI_separable` (Def. 5) are proved
  *about* the `J_NI` instance, never assumed of an abstract `J`.
- **`≅` is 𝒪-observational equivalence; bit-identity ⟹ ≅ needs Sem-Det/Closed.**
  `conform_refl` is exactly that implication, discharged by `eval` being a
  pure total function.
- **The gate transports *both* strata.** `transport_JNI` (Closure) and
  `transport_releases` (Policy) compose into `confidential_transport`, so the
  bounded guarantee proven about `A` holds of the running `deploy` — no
  artifact/deploy asymmetry for the joint layer to inherit.

## Not yet mechanized (the honest residue)

- **`J_ε` and non-separability (Prop. 2).** Mutual information `I(o;High|Low)`
  needs a *distribution over High inputs*, which the deterministic semantics
  here does not have — so the `H⊕r` witness is not a mathlib addendum but a
  probabilistic layer over inputs (entropy, data-processing as a theorem):
  Paper 2 proper. The mathlib-free `Joint.lean` already states *where* it
  fails (the forward cell) without needing any of it.
