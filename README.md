# Certified composition

Three Lean 4 formalizations forming one line of work, unified by a single
discipline:

> **Evidence carries its hypotheses, and composition *accumulates* them —
> never discharges or coerces silently.**

Each sub-project is a self-contained Lean package. All are `no sorry`; the two
mathlib-free ones build instantly, the third needs the mathlib olean cache.

| dir | what | deps | status |
|---|---|---|---|
| [`conf-typing/`](conf-typing) | confidentiality-typing framework (the IMP timing instance + meta-theory) | none (mathlib-free) | closed |
| [`transport-calculus/`](transport-calculus) | a common interface for transport theorems (certified morphisms) | none (mathlib-free) | core proved |
| [`transport-kernel/`](transport-kernel) | mathlib instances of that interface | mathlib | 2 instances received |

## The through-line

The same accountancy appears at three levels of abstraction:

- **`conf-typing`** — a discharge of a confidentiality obligation carries its
  evidence: `Discharge.pol` bundles `(φ, proof that the channel releases at most
  φ)`, *not* bare membership; `confidential_transport` carries **both** strata's
  guarantees across the conformance gate; the assumption ledger tracks which
  theorem consumes which admissibility condition. Nothing composes that silently
  drops a side-condition.
- **`transport-calculus`** — that accountancy made the primitive object. A
  `Bridge` is a map bundled with a certificate; `Bridge.comp` accumulates
  certificates (a monoid action), and dropping the accumulation makes the
  composite's proof fail to type-check. Zero axioms, mathlib-free.
- **`transport-kernel`** — the interface receives objects *someone else built*:
  mathlib's `LipschitzWith` (scalar certificate) and `HolderWith` (a non-scalar
  pair certificate with a semidirect-product law). The generic `Bridge.comp`
  reconstructs each library's own composition lemma.

## What each sub-project actually proves

**`conf-typing`** (mathlib-free; core meta-theorems axiom-free):
- the parametric framework — admissibility (A1–A3), joint generation, bounded
  delimited-release policy, the conformance gate, Boolean soundness;
- the typed rejection of cross-stratum evidence, proved *J-invariant*
  (`reject_Jinvariant`, `∀ J`);
- a corrected §10: among admissible properties, the only nondegenerate
  **2-safety** one is noninterference (`qualitative_admissible_is_JNI`);
  separability is the *congruence-refinement* of 2-safety, not equal to it
  (`Rbad_nonseparable`); the k-safety hierarchy above 2-safety is
  kernel-determined (`A3_factors_kernel`, `simA3_iff_respectsCoarsening`).

**`transport-calculus`** (mathlib-free; `Bridge.comp` axiom-free):
- `GradedAction M D` — a grade monoid `M` acting monotonically on a distance
  order `D`;
- `Bridge.comp` — the composition law, accumulating certificates by the action.

**`transport-kernel`** (mathlib):
- `comp_reconstructs_lipschitz`, `comp_reconstructs_holder` — the generic
  `Bridge.comp` reconstructs `LipschitzWith.comp` and `HolderWith.comp`.

## Scope — what is *not* claimed

- The transport interface is **not** asserted to be the "correct general notion"
  of certified transport. It is a small interface that, so far, two independent
  mathlib theorems instantiate. Whether it deserves a grander status is earned by
  more instances, not by naming.
- The **method** behind this — adversarially attacking one's own *statements*
  (not proofs) and narrowing to a machine-checked theorem — is how the work was
  produced, not a claim being made. Two case studies by one author is a working
  style demonstrated twice, not a validated methodology. It travels only if a
  second hand runs it.
- **Deferred:** the Markov-kernel / Dobrushin (total-variation) instance needs
  the data-processing inequality, which mathlib lacks — a genuine from-scratch
  formalization, and the quantitative frontier. The interface only has to
  *receive* it; accumulation is already proved generically.

## Building

```sh
# mathlib-free — instant
cd conf-typing        && lake build
cd transport-calculus && lake build

# mathlib — needs the olean cache first (multi-GB)
cd transport-kernel   && lake exe cache get && lake build
```

All pinned to Lean `v4.31.0` (see each `lean-toolchain`).

Per-subdir `README.md` and `CHANGELOG.md` carry the detail; the top-level
[`CHANGELOG.md`](CHANGELOG.md) traces the arc across all three.
