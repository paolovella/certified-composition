# Changelog

## [0.9.0] — 2026-06-29

Mechanized the Πₖ up-set characterization — turning Paper 1's last argued
paragraph into a theorem. Mathlib-free, no `sorry`.

### Added
- `kerLE` — kernel coarsening (`ker x ⊆ ker x'`, higher in the partition
  lattice).
- `A3_coarsen` — **simultaneous A3 ⇒ closed under coarsening** (the one-
  directional generalization; `A3_factors_kernel` is now its symmetric
  corollary).
- `RespectsCoarsening` — up-set of the partition lattice (closed upward under
  coarsening).
- `simA3_iff_respectsCoarsening` — **the characterization: admissible (sim-A3)
  ⟺ up-set of the kernel-coarsening order**, all `k`, mathlib-free. Forward is
  `A3_coarsen`; backward is `ker x ⊆ ker (f∘x)` always.

### Pinned (the realizability edge, per review)
- The iff characterizes admissible properties as up-sets of the order on
  *realizable* kernels. The growth to the *full* Πₖ is **conditional on
  observation cardinality**: value-rich `Val` realizes every partition (full Πₖ,
  family grows); a Boolean-valued channel realizes only ≤2-block kernels (region
  2 collapses to a finite stub). "Realizable = full Πₖ for `Val`" needs
  `Finset.min'` (mathlib) and stays argued, the condition explicit not hidden.

## [0.8.0] — 2026-06-29

Settled the "is region 2 a proper hierarchy or a finite stub?" question — it is
neither, and the deciding lemma is mechanized. Mathlib-free, no `sorry`.

### Added
- `SimA3` / `sameKernel` — simultaneous A3 and the kernel (pairwise-equality
  pattern) at arbitrary arity `Fin k → Val`.
- `A3_factors_kernel` — **simultaneous A3 ⇒ the property is determined by the
  kernel** (relabeling `x i ↦ x' i`, well-defined iff kernels agree, transported
  by A3). General over all k.
- `no_irreducible_admissible` — corollary: no admissible property depends on
  genuinely k-ary structure. The "k-irreducible property" probe is settled
  *negatively*, at every arity.

### Resolved
- Region 2 is **up-sets of Πₖ**: every admissible k-safety property is a
  function of the 2-ary atoms `o_i = o_j` (so no irreducible k-ary atoms —
  `A3_factors_kernel`), yet the family grows with k and the k-safety refutation
  degree is unbounded. Not a tower of irreducible atoms, not a finite stub: an
  infinite, properly-growing family over a fixed 2-ary basis. README marks the
  Πₖ bijection / growth / refutation-degree hierarchy as argued-not-mechanized;
  the kernel-determination core and the k=3 inhabitant are proved.

## [0.7.0] — 2026-06-29

Arity-3 result: the k-safety hierarchy lives strictly above 2-safety, so the
v0.6 "qualitative ⟺ J_NI" was itself an overclaim. Mathlib-free, no `sorry`.

### Added
- `J_rel3` / `PostClosed3` — the ternary lift and A3 in *simultaneous* form
  (one post-processor on the whole observation, the faithful reading: the k
  traces are one post-processed channel at k inputs).
- `notAllDistinct` (canonical 3-safety-not-2-safety) with
  `notAllDistinct_postclosed` (A3 holds, **axiom-free**) — a function preserves
  the coincidences that keep a triple not-all-distinct.
- `branch_Pleak_val`, `branchO_J_rel3` — `branchO` is two-valued under
  High-variation, so any three traces are never all distinct.
- `ksafety_above_twosafety` — `notAllDistinct` is admissible (A2∧A3),
  deterministic, satisfied by `branchO` which `J_NI` rejects: a witness that
  **admissible 2-safety = J_NI ⊊ admissible k-safety (k>2)**.

### Corrected (supersedes v0.6)
- The characterization is **admissible 2-safety ⟺ J_NI**, not "qualitative ⟺
  J_NI". `qualitative_admissible_is_JNI` was always correctly typed (binary
  `R`); the prose dropped the "2-safety" qualifier. Three nested regions now:
  admissible 2-safety (= J_NI) ⊊ proper k-safety k>2 (deterministic, mathlib-
  free, shown inhabited) ⊊ hyperproperties (= J_ε, needs a distribution). The
  mathlib boundary is the k-safety/hyperproperty boundary — above both the
  2-safety and the qualitative boundaries.

## [0.6.0] — 2026-06-29

Abstract 2-safety module (`TwoSafety.lean`) — retires §10's conjecture by
**correcting** it. Mathlib-free, no `sorry`.

### Added
- `J_rel R` lift (binary trace-relation), `JNI_is_rel` (`J_NI = J_rel (·=·)`,
  axiom-free), `PairClosed` (congruence / separability condition), `PostClosed`
  (A3 at the relation level).
- `rel_perchannel_to_joint` / `rel_joint_to_perchannel` — forward/backward over
  the *whole* class, generalizing the `J_NI` facts.
- `postclosed_collapse` — A3 forces any `R` to total-or-sub-diagonal (the
  headline lemma; relate one off-diagonal pair, relabel, get the total relation).
- `qualitative_admissible_is_JNI` — among A2 ∧ A3-admissible J, the only
  nondegenerate 2-safety one is `J_NI`.
- `Rbad`, `Rbad_not_pairClosed`, `Rbad_nonseparable` — a deterministic 2-safety
  property that is non-separable, witnessing `separable ⊊ 2-safety`.

### Corrected (supersedes the v0.5 note)
- §10's "separable ⟺ 2-safety" is **false** (`Rbad`). Separability is the
  *congruence refinement* of 2-safety. The reason the two looked coextensive is
  **admissibility, not determinism**: A3 (`postclosed_collapse`) plus A2 pin the
  unique nondegenerate qualitative property to `J_NI`. The v0.5 "four cuts
  coincide / mathlib boundary = 2-safety boundary" claim is withdrawn; the
  correct statement is "among *admissible* J, qualitative ⟺ J_NI ⟺ separable".
- Only deferred to mathlib now: exhibiting that the quantitative non-separable
  region is *inhabited* (a concrete admissible `J_ε`).

## [0.5.0] — 2026-06-28

Closed the Thm. 2 quantifier and corrected the separability framing.

### Added
- `Derivable`, `mem_is_postproc` (Prop. 1: every primitive channel factors
  through the join) and `completeness_thm2` — the *honest* Thm. 2, quantifying
  over adversary-derivable channels, not all functions. `completeness_rel_O`
  is now labelled the engine. `perchannel_covered` routes per-channel coverage
  through Thm. 2, exhibiting `joint_to_perchannel` as its special case.
  `completeness_thm2` is axiom-free.

### Corrected
- The deferral reason for a non-separable `J_toy` was mis-stated as "A3 only
  weakens downward". The real obstruction is **determinism**: with no input
  distribution, `J_NI` means "constant under High-variation", and tuples of
  such are such — separability is *forced*, breakable only with randomness.
  This puts the module exactly on the coincident boundary
  separable/2-safety/qualitative/mathlib-free; the development *proves* the
  easy direction (2-safety ⟹ separable = `perchannel_to_joint`) and is
  evidence for §10's conjecture. Converse + `H⊕r` witness remain open/pending.

## [0.4.0] — 2026-06-28

The joint-generation module (`Joint.lean`) — mathlib-free, all over `J_NI`.
Localizes Hole 1 (synergy) without solving it: proves per-channel ⟺ joint for
the separable case and pinpoints the one implication `J_ε` lacks.

### Added
- `seedObs` / `seed_JNI` — the inert constant seed (constancy makes the nil
  base case go through; chosen over a non-empty precondition / `foldr1`).
- `joint = foldr tup seedObs`, `GenJoint = [joint 𝒜]` (singleton generation).
- `completeness_rel_O` (Thm. 2) — one joint obligation covers every derived
  channel; **no axioms**, pure A3.
- `joint_to_perchannel` (backward, A3 / projections) and `perchannel_to_joint`
  (forward, `JNI_separable`), combined as `separability_equiv`.

### Note
- Axiom footprint encodes the J_ε story: completeness uses no forward step, so
  it survives non-separability; per-channel generation *is* the forward step
  and dies with it. Building a mathlib-free non-separable `J_toy` to prove
  "forward is J-dependent" is hard *for a reason* — A3 only weakens downward,
  so any non-separable `J` must be genuinely quantitative (§10 conjecture).
  Deferred to the probabilistic layer rather than forced synthetically.

## [0.3.0] — 2026-06-28

Shut Hole 2 at the deploy level too. v0.2 bounded the Policy stratum about the
*artifact* `A`, but the gate only transported the Closure half: `soundness_deploy`
concluded `∀ o, J_NI deploy o P` (can't even express declassification) and
covered the policy branch only by assuming `Pi = noPolicy`. The bound was real
about `A` and evaporated at `deploy`.

### Added
- `transport_releases` — the gate carries a `ReleasesAtMost` bound from `A` to
  `deploy` (clean: `φ` is a function of the store, not the program, so
  `φ σ = φ σ'` crosses untouched). **No axioms.**
- `confidential_transport` — full-strength gate: the whole `Confidential` claim
  (both strata) transports `A → deploy`. **No axioms.**
- `pleak_confidential_deploy` — end-to-end via `conform_refl`: the *running*
  P_leak leaks at most the bit `(b≠0)` on `result`. The claim the gate exists
  to make, previously unstatable.
- `A_local_sub_OO` — the obvious subset side-condition.

### Changed
- `soundness_deploy` is now the `Pi = noPolicy` special case of
  `confidential_transport` (kept as a closure-only corollary), and its
  overclaiming doc-comment is corrected.

## [0.2.0] — 2026-06-28

Bounded the Policy stratum (closes checklist item 3 / framework §5). v0.1
mechanized the **instance** doc's pre-bulletproofing Policy, where a discharge
required only `o ∈ Π` — an unbounded permit, vacuous when Π is permissive. The
**framework** doc had already fixed this; v0.2 brings the mechanization in line.

### Changed
- `Discharge.pol` now carries a declared release `φ` (`Pi o φ`) **and** a proof
  obligation `ReleasesAtMost c o P φ`. `Policy` is `Obs → Release → Prop` (a
  declaration relation, so no `DecidableEq` on observations is needed).
- `Confidential` policy branch is now `∃ φ, Pi o φ ∧ ReleasesAtMost c o P φ`.
- The P_leak policy `PiLeak` declares `result ↦ φ_bit`; `pleak_confidential_local`
  is now a substantive guarantee (`result` leaks at most `(b≠0)`), not a fiat.

### Added
- `ReleasesAtMost`, `Release`, and `closure_is_const_policy` (Closure is the
  `φ=const` case — a theorem, keeping the three strata syntactically distinct).
- `result_releases_at_most_bit` — the real bound for P_leak.
- `result_full_not_bounded_by_bit` — non-vacuity: `l := b` fails the bit-bound.

### Still open (unchanged by this fix)
- **Joint generation / synergy (Hole 1).** Per-channel bounds compose to a
  sound *joint* bound only via `JNI_separable`. Bounded policy fixes each φ;
  it does **not** make the channel-*set* complete. That's the joint-generation
  module (framework doc Thm 2), orthogonal to this change.

## [0.1.0] — 2026-06-28

Initial mechanization of **Paper 1 (the IMP timing instance)** in Lean 4.31.0,
mathlib-free, no `sorry`.

### Added
- **Layer 1 (`Imp.lean`)** — IMP syntax; instrumented big-step semantics as
  both a relation (`Step`) and an executable evaluator (`eval`); their
  equivalence (`eval_step`, `step_eval`) yielding `determinism` (Sem-Det).
- **Layer 2 (`Obs.lean`)** — observations over a universal `Val` domain
  (`wall`, `branchO`, `resultO`); `lowEq`; parametric `JTy` with the `J_NI`
  instantiation; A3 (`JNI_postproc`) and separability (`JNI_separable`);
  observation language, the `remote ⊆ local ⊆ physical` adversary chain,
  generation `Gen` with Lemma 1 (`gen_mono`).
- **Layer 3 (`Pleak.lean`)** — the `P_leak` example: `wall_const`/`wall_closure`
  (closable), `result_not_closable`, `branch_not_closable` (genuine leaks).
- **Layer 4 (`Typing.lean`)** — `Stratum`/`EvKind`; the `Discharge` judgment
  (Closure + Policy only — no conformance/attest constructor, by design);
  `reject_Jinvariant` (Lemma 3); `Conform` + `transport_JNI`;
  `attest_is_not_J_evidence` (§6.1); `soundness`; and the end-to-end worked
  results `pleak_confidential_local`, `branch_residual`, `wall_rejection`.

### Notes
- Core meta-theorems (`reject_Jinvariant`, `soundness`, `transport_JNI`,
  `wall_closure`) depend on **no axioms**; the rest use only the standard
  `propext` / `Classical.choice` / `Quot.sound`.

### Next
- Joint generation `G = {J 𝒜̂ H}` and Theorem 2 completeness (framework doc).
- `J_ε` / mutual information and non-separability — requires mathlib (Paper 2).
