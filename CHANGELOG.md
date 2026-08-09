# Changelog — certified composition

Top-level arc across the three sub-projects. Each subdir keeps its own detailed
`CHANGELOG.md`; this traces the line of work as a whole. Dates are when the work
landed.

## conf-typing — the confidentiality-typing framework (mathlib-free)

- **0.1 – 0.3** — mechanized the IMP timing instance: instrumented semantics +
  determinism; parametric `J` with admissibility (A1–A3) and separability;
  the `P_leak` worked example; strata, the no-coercion discharge judgment, the
  J-invariant rejection; the conformance gate; Boolean soundness. Bounded the
  policy stratum (delimited release with a real proof obligation — closing the
  unbounded-permit hole) and made the gate transport *both* strata.
- **0.4 – 0.5** — joint generation and completeness (Thm. 2) via the factoring
  bridge (Prop. 1); separability-equivalence.
- **0.6 – 0.8** — the corrected §10: "separable ⟺ 2-safety" is **false**
  (`Rbad`); among admissible properties the only nondegenerate 2-safety one is
  noninterference; the k-safety hierarchy above 2-safety is kernel-determined
  (no genuinely k-ary admissible atoms).
- **0.9** — the Πₖ up-set characterization (`simA3_iff_respectsCoarsening`):
  admissible ⟺ closed upward under kernel coarsening, with the realizability /
  observation-cardinality condition pinned explicit.

- **Brick 33 — speculative execution, the last OUT-OF-MODEL row
  (`Speculate.lean`).** §0's recipe run a third time, after timing (brick 2) and
  scheduling (brick 32). A transient-execution machine: architectural state that
  rolls back, a microarchitectural **address trace** that does not, and a `brLt`
  branch that may be mispredicted, running its body transiently for a window from
  a **misprediction schedule** — a data parameter, so `∀ misprediction` ranges over
  unbounded windows. `spectre_trace_is_the_secret` (axiom-free) pins the gadget's
  traces at `[8,42]`/`[8,99]` for two memories differing only at the secret, so
  `spectre_leaks`; `leak_needs_window_two` shows the channel has real depth.
  `arch_indistinguishable` is the other half — architecturally the guard is false,
  nothing runs, the two memories are *identical* — and
  `speculative_model_misses_it` pairs them: §0's model gap in its sharpest form,
  the architectural semantics not merely coarse but **silent**. The fix is a
  `fence`, with the strong soundness `specCheck_sound`/`spec_inert`: on a checked
  program the speculative registers *and* trace equal the architectural ones under
  every schedule, so speculation is observationally inert and `arch_ni_transfers`
  carries any architectural noninterference over verbatim — which is what makes
  the row compose. Limits kept explicit: address-trace granularity only; v1 alone;
  perfect rollback; nested speculation excluded **by the syntax** (branch bodies
  are a separate instruction type) rather than dropped by the semantics; and the
  check sufficient-not-necessary, witnessed by `benign_rejected` +
  `benign_transient_is_constant`. Note the class count stays **sixteen**: by the
  §2½ convention a verdict change is not a new class, which is the convention
  doing its job on its first use.

- **Brick 34 — resource exhaustion, the cost bound as a graded certificate
  (`CostBound.lean`).** Row 10's [classified] reduction, proved — and one clause
  of it corrected. `CostAtMost c k` quantifies over **all inputs and all fuel**,
  so algorithmic-complexity DoS is the failure of *uniformity*, not the absence
  of a bound. `costGA : GradedAction Nat Nat` (mul `+`, act `+`, le `≤`) is a
  checked instance of the interface's own accumulation algebra, and `cost_seq` /
  `cost_seq_is_mul` prove budgets add as `costGA.mul` — **the first time a
  security row lands directly in the transport calculus's algebra rather than
  beside it**. `costCheck`/`costCheck_sound` generate budgets for the loop-free
  fragment; `countdown_cost` bounds the canonical countdown by `1 + v·(kc+3)` in
  its counter's initial value, a bound that exists per input and grows with it —
  the DoS surface — and `spinU_cost_lb` turns that into **`dos_unbounded`**: no
  uniform budget exists for a loop counting down untrusted input. What it catches
  that nothing else does: the victim is memory-safe, injection-free and
  noninterferent, so every earlier brick certifies it. `budget_cost` restores
  uniformity from a constant-initialised counter. **Correction of record:** brick
  1's "`Bridge.ofModulus` territory" is wrong — a `Bridge` certifies a *binary*
  quantity and a cost budget is *unary*; the `GradedAction` transfers, the
  contraction does not. Limits kept: halting runs only (availability is
  liveness-shaped, still not claimed), the canonical countdown only (so the
  verdict keeps "REDUCIBLE in general"), instrumented steps not wall clock. Class
  count stays sixteen by the §2½ convention.

- **Brick 35 — complete mediation, and the split row 7 was hiding
  (`Mediation.lean`).** Row 7 carried the map's **last `[classified]` grade**, on
  the reasoning that π's correctness "is not a theorem anywhere". True of policy
  correctness — and it was swallowing a second, different property. CWE-285's
  actual defect, and CWE-306's, is almost never "the policy was wrong"; it is
  **missing mediation**: some path reaches the protected operation without the
  check. That is a program property, all-paths, decidable. `med_victim_bypasses`
  (axiom-free): the unguarded branch reads a resource the policy denies, while
  `victim_guarded_path_is_fine` shows the other branch aborts cleanly — the
  defect is the *route*, not the check. `medCheck` (flow-sensitive, intersecting
  at joins) with `medCheck_sound` generates the guarantee on every path and under
  every policy, via a three-part invariant.
  `policy_correctness_not_witnessed` proves the other half is **not**
  program-decidable — two policies, same checked program, both mediated,
  different reads — so `mediation_generated_policy_carried` states the split as
  one theorem and the CARRIED half is finally demonstrated rather than asserted.
  Limits: nesting excluded by the syntax; the join intersects, so the check is
  sufficient not necessary; no *subject* in the model, so IDOR (CWE-639) is a
  named follow-on. `memStr`/`interStr` defined and proved locally — the package
  is mathlib-free and guessing core lemma names had already cost two build
  rounds. **With this the map has no `[classified]`-only grade left**: every row
  is `[proved]`, `[argued]`, or an explicitly named deferral. Class count stays
  sixteen — a sub-formulation within a row is a verdict, not a class (§2½).

## transport-calculus — the certified-morphism interface (mathlib-free)

- **Set-theory research line, the independence program (notes §40–§52).**
  The terminus decided (§49, sixteenth flip): tree-transport invariance
  retracted at its exact scope (the game's data — deviation sets, value
  comparisons — is value-category, not tree-category; the PFA 0–1 law
  withdrawn), separating the canonical walk sequence ρ₃ from the CH-wild
  trees. Standing picture: Question 1 conjectured **false under MA_ω₁**
  with witness ρ₃ — Todorcevic's `T(ρ₃)` is coherent, nontrivial, and
  Lipschitz in ZFC, so the schedule forcing's ccc is a ZFC question — and
  **open under CH**, where it reduces (§50–§51) to fiber-specialness of
  `D(ρ₃)`: gated by "is `T(ρ₃)` special?" (Theorem J), Tukey-cheap
  (Theorem K: `D(ρ₃) ≡_T [ω₁]^{<ω}` in ZFC). §52 settles one subproblem:
  **Q-rows is false** — successor rows ride their fans
  (`B_{γ+1} = B_γ ∪ {γ}`), every fan's canonical row family is jointly
  absorbed — benignly, since fiber-specialness reduces to limit levels,
  where the absorption game descends to a one-sided domination game for
  the canonical threshold sequence θ(ρ₃) (coherent, finite-to-one,
  ω-valued on fan-tops). Theorem O: Con(CH + `T(ρ₃)` special), so the
  CH-kill needs strictly more than CH. Both ρ₃ sources verified
  first-hand; one in-source typo caught (JIMJ footnote 10).
- **Escapee framework, machine-checked and axiom-free (`EscapeeTheory`
  section).** Theorem I forward (notes §38): `Phi O` — every legal
  constraint system on a directed order has a monotone dominator — follows
  from a monotone dominating retraction (`phi_of_domRetraction`), and the
  three sufficient routes are its instances (`phi_of_top` the ⊤-route,
  `phi_of_join` the bounded-complete/Theorem-H route). Abstract
  (`DirOrder`, `LegalSystem`, `Dominator`, `DomRetraction`) and dependent
  on **no axioms at all** — pure constructive order theory. The converse
  (open uniformization, §39) is deliberately not formalized. The PFA-side
  **forcing bridge** is machine-checked too (`phi_of_generic`, axioms
  `Classical.choice`): a `GenericDom` — the covering, cross-monotone family
  of partial dominators a proper `P(Σ)`'s generic filter provides — yields
  `Φ`; proving `P(Σ)` proper is the open checkpoint and is *not* formalized,
  and the bridge isolates it as the single structure hypothesis. The
  set-theory research line reached the Tukey/cofinal-types frame
  (Todorcevic: 5 types under PFA, `2^{ℵ₁}` under CH) as the correct
  order-theoretic home for the residual (notes §36–§39, fifteen recorded
  verdict flips including two wrong frames caught and corrected).
- **Dip-schedulability skeleton, machine-checked (`DipSchedule` section).**
  Theorem A (trivial ⟹ strongly schedulable) and Lemma F (below-level
  absorption) — two index-agnostic pillars of the set-theoretic
  development — formalized over the `CoherentSeq` abstraction:
  `thmA_leftover_subset`/`thmA_schedulable` (canonical dips route every
  surviving `upDefect` at a top into one finite set) and
  `lemmaF_below_subset`/`lemmaF_below_finite` (the fiber inequality
  `s_x ≤ s_u` transfers through the floors below the element's level;
  the finiteness form is choice-free, `propext, Quot.sound`). These are
  the proved results the open heart (Question 5) rests on; hardening
  them leaves the residual — a `lim¹`-type independence (notes §24–§26)
  — as the only open point. No `sorry`.
- **Set-theory research line (notes §14–§26, problem statement).** The
  qualitative residual driven to a single named question in five
  equivalent forms (wildness cap / finite-row incidence covering /
  finite-fan / profile-diagonal / poset-ccc): Lemma F, Theorems E (the
  game is Φ-complete), F (block-wild cap), G (finite-fan ⟹ coverable);
  the ◊ results C (a non-schedulable coherent sequence) and D (its
  lethal pressure is illegal); and the §22–§26 reductions locating the
  residual as a `lim¹`/derived-limit independence, ccc of the frozen-dip
  realization poset `P(Σ)` against walk oscillation. Eleven recorded
  verdict flips, each argument-forced; the ZFC skeleton is proved, the
  heart handed to set theory in final form.
- **0.1** — first cut: a `Bridge` carrying a certificate, `Bridge.comp`
  accumulating it; existence demonstrated by *composition* of two certified
  bridges (not a single morphism). Zero axioms.
- **0.2 (the eighth catch)** — corrected `Grade` → `GradedAction`: contact with
  mathlib's real `LipschitzWith` revealed that grade and distance are *two*
  types (`ℝ≥0` acting on `ℝ≥0∞`), a conflation the degenerate `Nat` (`M = D`)
  instance had hidden. The first correction delivered by an external object
  rather than internal review.
- field `coeff` → `cert`, and the over-claiming "genus / existence proof"
  framing dropped to "a common interface," once the Hölder instance showed the
  certificate need not be numeric.
- **the qualitative frontier, bracketed** — the non-monotone escapee question
  resolved into: complete lattice ⇒ factors; image-family sups ⇒ factors (and
  are not necessary); non-directed `D` ⇒ escapee (`D3`); directed + finite /
  bounded ⇒ factors; countable cofinality ⇒ factors (cofinal ℕ-ruler,
  cub-monotonized). Residual: uncountable cofinality.
- **the transfinite theorem, proved — "unformalizable" was wrong.** The
  uncountable-cofinality selection, previously called "plausible — unchecked,
  and unformalizable here (transfinite recursion, cardinals)", is now a
  mathlib-free theorem (`prefix_bounded_cofinal_factors`): selection over any
  well-ordered index needs **no limit steps** (`wruler_defeats_bounded_escapee`,
  `Classical.choice` only), and monotonization runs on Lean-core
  `WellFounded.fix` under `PrefixBounded` — `κ`-directedness stated without
  cardinals, weakened to segment-indexed families. `prefixBounded_of_directed`
  proves directedness supplies it at `ω` (re-deriving the countable case);
  uncountably it is not a theorem. The residual is now exactly one hypothesis
  wide: whether `Directed` without `PrefixBounded` admits an escapee.
- **the hunt — two walls proved, no capture.** Candidates die informatively
  (`ω₁ × ℕ` and ideal-of-sets orders are conditionally complete; chain designs
  self-dominate; gap encodings can't force a dominator *under* anything). Wall
  one: `sigma_directed_cofinal_factors` — σ-directedness + an ω₁-like cofinal
  family (`CountableSegments`) forces factorization, so an escapee there must
  contain a countable unbounded family. Wall two: `lists_not_sigma_directed` +
  `lists_bounded_factors` — `List Nat` under membership-inclusion fails
  σ-directedness yet factors everything (filtered bounding list = least upper
  bound), so failing σ-directedness is not sufficient. Residual profile: break
  conditional completeness unovershootably, with only-global failure
  (Aronszajn/gap shape); existence may be independent of ZFC.
- **the coherent-sequence encoding — the profile is realizable, up to set
  theory.** On paper: the fiber order `D_coh(e)` over a nontrivial coherent
  sequence (ZFC, via walks) is directed with finite joins, not σ-directed,
  and join-incomplete (bounded families with *no minimal* upper bound) — the
  first structure passing every wall. The escapee question on it reduces to a
  coherent-sequence uniformization principle (level-monotone bounded coherent
  sequences are provably trivial, so the canonical dominator is obstructed;
  MA/◊-sensitive, plausibly independent of ZFC). Formalized shadow: `Fb`
  (levels ℕ∪{∞}, finite patches over a constant floor) — directed, not
  σ-directed, bounded family with no minimal ub (`fb_no_minimal_ub`,
  choice-free), yet factors via an explicit ladder ruler (`fb_factors`). So
  the dip pathology alone is also non-lethal at countable cofinality; the
  hunt's remaining question lives at ω₁, outside a mathlib-free repo.
- **the ◊-side attempt (`NOTES-coherent-escapee.md`) — canonical dominators
  die; one bridge remains.** Prose rigor: two ZFC lemmas (level-preserving
  systems always factor; representative systems ⇒ everything factors, with
  "trivial ⇒ factors" as corollary) and one ◊ theorem (a coherent sequence
  with *no* representative system — block-diagonal lowering against
  ◊-guessed partial systems). The bridge from rep-death to an escapee did
  not close: pressure needs boundable infinite families, legality makes
  their requirements mod-finite-satisfiable, fibers absorb finite defects,
  and every coherence-extraction from a dominator needs the reps whose
  absence powers the kill. Open core, one sentence: does factors-everything
  imply reps? The note records the legal pressure system `Σ_succ`, the "+1
  trap", the self-obstruction phenomenon, and the two decisive follow-ups.
- **the ◊ theorem collapses to ZFC: reps ⟺ trivial.** Checking whether the
  walk sequences already lack reps answered far more strongly — *every*
  nontrivial coherent sequence lacks representative systems, in ZFC
  (coherence pins pairwise rep-differences finite; level-monotonicity
  concentrates countably many witnesses at one countable level, so movement
  below any α is finite; the escape set has finite initial segments, hence
  bounded; bounded escape trivializes). The ◊ construction is retired as
  unnecessary (kept in the note for the record); "canonical dominators
  exist iff trivial" is a ZFC dichotomy; the independence suspicion
  retreats to non-canonical dominators only; and the Bridge is restated as
  a pure ZFC question over the walks' `ρ₁`. If it holds, the transport
  escapee exists in ZFC.
- **the dip-side attempt — correction, chain-freeness, flipped verdict.**
  `Σ_succ` factors after all (uniform one-level shift dominator) — the
  prior "pressure" claim is retracted; limit-raising systems are legal
  exactly over block-tame sequences, whose tameness builds the dominator
  (absorption pattern, fourth instance). New ZFC theorem: `D_coh(e)` has
  an ω₁-chain with cofinal levels iff `e` is trivial (a chain is a
  club-indexed rep system) — over nontrivial sequences the fiber order is
  provably chain-free, explaining every failed chain-mediated argument.
  Kill schemes close into the legality circle at every entry (per-element
  budgets, countable-union accumulation, slice-illegality under floor
  sabotage). Verdict flipped: evidence now favors ZFC-factoring of all
  fiber orders; the escapee, if anywhere, needs a different species of
  directed order. Missing lemma named: global coordination of per-element
  finite gap-fill corrections.
- **the coordination lemma attempted — residue isolated, verdict
  oscillates.** A ⊑-refining ω₁-recursion with a finite-ledger invariant
  works except at one point; requirement-excess inherits uniformly (ZFC
  lemma — all past `M`-contributions land in one finite set `F_u`); the
  residue is exactly past-floor inversions on gap regions against moving
  targets, with level-overshoot provably useless. Sufficient condition
  named (uniformizing dip system; trivial sequences have one), which
  almost-extracts a rep system (one fiber-control gap). The Bridge is
  squeezed between per-`u` absorption (necessary) and uniform dips
  (sufficient) — one Fodor step and one extraction repair apart. If both
  close: dominator ⇒ trivial, and the escapee exists in ZFC.
- **the Fodor step attempted — the circle proves itself; the core goes
  Aronszajn.** Pressing down is sound; its input is unobtainable: probe
  systems exerting cofinal floor-pressure are legal iff sup-coherence
  already holds (the circle is an equivalence now). New ZFC lemmas:
  single-target dips free; bounded families never obstruct; the
  chain-continuation lemma (dips against a chain's own sup serve every
  continuation — the moving target is fake for chains). But the reduction
  is self-similar under per-element targets; club targets die over the
  ◊-sequence; and §7's "overshoot useless" is corrected — overshooting
  parks values on post-kill floors, making a dominator a `D`-indexed
  rep-like selection whose kill needs chains that chain-freeness forbids.
  Both directions lose their weapon at the last step. Hard core isolated:
  monotone fiber-valued selection with pairwise-finite deviations on the
  chain-free order — Aronszajn-type uniformization. Third flip: lean is
  now independence, one named gap per side.
- **the ◊-side gap attempted — a no-go theorem for the kill template
  (fourth flip).** Kills are structurally thin (coherence: finite below
  every lower level, inherited above), so they never accumulate;
  staggered kills contradict pairwise coherence; committed-value forcing
  needs img-levels cofinal in the kill stage, which legality forbids,
  markers block (infinite markers ∉ fiber), and delayed levels cannot
  reach (coherence caps late deviation at finite). Template no-go: legal
  forcing is bounded-family forcing; bounded families are absorbable;
  kills need unabsorbable forcing — covers all five kill designs tried.
  First one-sided evidence in the arc. Lean, fourth revision:
  ZFC-factoring; the MA-side route re-read as a candidate ZFC proof with
  its missing piece named (forcing-locality).
- **forcing-locality proved; the Bridge becomes a game on `e` alone.**
  The anti-kill (fiberhood-forcing, the one pattern the no-go missed)
  breaks nothing by pairwise coherence — so nothing legal forces values
  above eventual floors. Systems and dominators eliminate: down-sets have
  ⊑-cofinal ω-chains; requirement-sups are legality-bounded; the sole
  residue is floor-baking along chains, finite per pair and fractally
  self-similar across chains. Result: factors-everything(e) ⟺
  dip-schedulable(e), a two-quantifier combinatorial game on the coherent
  sequence alone. The seven-session hunt ends at one line: is every
  dip-schedulable coherent sequence trivial? Handed to set theory in
  final form.
- **`PROBLEM-dip-schedulability.md`** — the standalone problem statement
  for set theorists: definitions from scratch, the strong/weak game, the
  implication diagram with rigor-graded arrows (the strong/weak split and
  the realizability gap presented honestly rather than papered over),
  four numbered questions, four proved ZFC lemmas with proofs, the
  thinness remark (why naive ◊-attacks fail), and the
  independence-boundary discussion. Pure ω₁ combinatorics; no knowledge
  of the program required.
- **the reps theorem machine-checked in shadow.** `reps_implies_trivial`:
  over an abstract index with least witnesses, σ-directedness, and
  countable segments (the three ω₁ properties the proof uses), a coherent
  sequence with a level-monotone representative system is trivial —
  axiom-clean, no sorry, with a mathlib-free pigeonhole and
  totality-from-least-witnesses (axiom-free) as supporting lemmas. Paired
  with the boundary: ℕ fails σ-directedness and the concentration step
  provably fails there (`omega_concentration_fails` — the χ family moves
  at every coordinate). The hunt's engine is now machine-checked, and its
  regularity hypothesis demonstrably load-bearing.
- **Theorem B: uniformizing dip systems ⟺ trivial (ZFC); Question 1′
  proved.** The §7 H-extraction is refuted (wasteful dips hide columns
  below ω-cofinality levels) and replaced by the honest-column argument:
  monotone along honest levels; never-honest points finite per level
  automatically (they sit in `X_γ ∪ U_γ`); unbounded columns killed by
  witness-concentration at one level; the max honest value trivializes,
  sandwiched at a late honest level. Relativizes to cofinal level sets;
  corollary: level-factored strong schedulability ⟹ trivial. Question 1
  of the problem statement is rescoped to element-dependent schedules.
  Phase-0 hygiene: stale Dobrushin claims fixed in transport-calculus
  README; `tools/check-claims.sh` drift guard added.
- **Phase 1 closed; literature first sweep clean.** Lemma E (cofinal
  restriction: schedules push into any cofinal level set via min-above +
  dip absorption; adversaries may attack `ρ₁` on any club). The
  set-based schedule condition has a genuine multiplicity hole (bounds
  leaking coordinates, not values — the recursion can blow up pointwise);
  fixed by the value-form definition, under which strongly-schedulable ⟹
  Φ is written at careful-prose rigor (notes §12) and the diagram arrow
  upgrades. First literature sweep (BLH 1902.02736 §2, Bannister
  2302.07222, derived-limits searches): Definition 2.10 dictionary
  confirmed; BLH's engine is pressing-down, not concentration; Bannister
  is ω^κ/Δ-systems; no uniformization-implies-triviality statement of
  Theorem B's shape found — preliminary no-subsumption verdict, with the
  three named residual reads as the remaining Phase-4 gate.
- **gate cleared; Phase 2 translation layer done.** Second sweep
  (BHL-circle 2411.15856: triviality via cofinality bounds, degenerate at
  ω₁; higher-walks intro 2410.00607: no monotonicity-after-deletions
  machinery, no games; Bannister full HTML: PHₙ is Ramsey/Δ-systems on
  ω^κ, trivialities structural): no subsumption across four probes; one
  footnote — PHₙ's literal statement needs a PDF read of Bannister §5,
  nice-to-have not blocker. Problem statement gains: the Def 2.10
  dictionary with the ω-vs-ℤ remark, the positioning paragraph
  (Theorem B: level-schedules ARE trivializations; Question 1: does
  element-freedom add power), Question 3(b) in H¹-vocabulary with the
  ρ₂ =ᶜ nuance, coherent-tree citations at Lemma D, and a verified
  related-work section. Phase-4 pitch drafted in the notes.

- **§53 — (Q-thr) falls; Theorem B has a downward dual; the dense failure
  mode of the residual dies.** Source round 4 (Handbook 1.16 verbatim — the
  finite-to-one + coherence pair for ρ₁; 1.17 read and recorded as *asserting*
  `T(ρ₁)` special **without proof**, so no analogue may be cited; 3.11's
  nontriviality definition and "coherent + nontrivial ⟹ `T(a)` Aronszajn"; the
  previously-unopened 3.12–3.13, ρ₃ nowhere dense with `ω₁ = ⋃ₙ (Λ+n)` each
  orthogonal to ρ₃ — a free ZFC σ-decomposition of the *index* shaped exactly
  like what fiber-specialness wants of the *fiber order*). **Theorem P: θ(ρ₃)
  is nontrivial in ZFC** — (T2)+(T3) alone, by the classical engine that makes
  ρ₁ nontrivial; §52 had missed it by asking only about implications between
  θ's and ρ₃'s nontriviality, where the direct argument needs neither. So §52's
  descent lands on a coherent **Aronszajn** tree `T(θ)`, not a degenerate
  object. **Theorem B⁻**: downward dip systems (`D⁻(μ,γ) := {ξ < μ : e_μ(ξ) <
  e_γ(ξ)}`) also force triviality — strictly easier than Theorem B (decreasing
  ℕ-values stabilize; no witness-concentration), and the form matched to (M1)'s
  one-sided pruning. **Theorem Q**: combining them, the *dense* failure mode of
  (Q-rows-lim) is impossible in ZFC — joint absorption of the full family of
  limit rows below β, cofinally often, would be a downward dip system for θ and
  trivialize it. Any counterexample is **sparse**; the CH-adversary must select
  rather than absorb uniformly. New named open: **(Q-T-θ)**, is `T(θ)` special.
  Machine-checked alongside: `omega1_finiteToOne_not_trivial` /
  `omega1_finiteToOne_no_reps` (see transport-kernel Tier 5).

- **§54 — going at the central question: the dial made explicit, one route
  closed as vacuous, the index set halved.** Unfolding Handbook 1.4 gives the
  **trace formula** `λ_F(λ,β) = max_i max(C_{β_i} ∩ λ)` over the walk's stops,
  against `ρ₁(λ,β) = max_i |C_{β_i} ∩ λ|` — under (d) the same data read as
  position vs place, so N2's two dials are one object. **Theorem V**: a fan
  above the trace is β-expensive — `ρ₃(μ+n,β) = 0` for every `n ≤ ρ₁(λ,β)`,
  hence `thr_β(μ) ≥ ρ₁(λ,β)+1` (M(3) plus arrival rigidity; `W ≥ 1` is sharp).
  **Corollary V1**: front-loading past the β-cheap region is automatic. **So the
  natural attack — transferring N1/N2 from the moving `thr_α` to the fixed
  `thr_β` — is VACUOUS**, its hypothesis contradicting V; recorded as a closed
  route, with **Corollary V2** the surviving walk-computable criterion (a leak
  needs the inner walks cheaper than the outer one). Under the harmless extra
  normalization (e) `C_{δ+ω} = {δ+n+1}`: **Theorem S** `B_{δ+ω} = B_δ ∪
  [δ,δ+ω)` — Lemma I one level up, fan-tops ride their whole fan (and without
  (e), `ρ₃(δ,δ+ω)=1` iff `|C_{δ+ω} ∩ δ| = 0`, so (e) is exactly what is needed)
  — whence **Theorem T** (those rows are strongly unbounded, by 3.8(2) at n=0)
  and **Theorem U**: **(Q-rows-lim) reduces to limits of limits**, parallel to
  Lemma I′ one level up. New `tools/walk-check.py` re-verifies every walk
  formula on randomized (a),(c),(d),(e)-conforming C-sequences below `ω²·3` —
  the first model in this program with limits *of* limits (§52's stopped below
  `ω·25`): trace formula 972 instances, Theorem V 3108, M(3) 36065, all pass.
  Recorded methodological caveat: a direct numeric probe of (Q-rows-lim) reports
  that most limit rows are absorbed — **an artefact**, since truncation destroys
  the 3.8(2) finiteness that is Theorem T's engine; numeric checks over the
  model are sound for identities and worthless for finiteness phenomena. **The
  central question — is `ρ₃` strongly dip-schedulable under CH — is not
  decided.**

- **§55 — the frames audited; two move.** **Theorem W**: for coherent trees
  *special ⟹ Lipschitz* (Lipschitz-maps Lemma 1.10, an unmarked ZFC iff, plus
  footnote 9). Hence **`T(ρ₁)` is a coherent ZFC-Lipschitz tree** — correcting
  **§46**, whose search for that resource ran ρ₂→ρ₃ and never examined ρ₁. The
  MA-side ccc argument needs only Lipschitz-ness, so it now has two witnesses;
  and Theorem J's necessary gate "`T(e)` special" is **open for `ρ₃`** but
  **passed in ZFC for `ρ₁`**, so `ρ₃` may be dead at the gate while `ρ₁` is not.
  Cost stated: the entire §50–§54 apparatus is ρ₃-specific and does not transfer.
  Caveat: Handbook 1.17 asserts `T(ρ₁)` special without proof, so the ρ₁ line is
  graded accordingly. **PID landscape** (Kuzeljević–Todorcevic, verified
  first-hand): PID is independent of CH and implies SH, but is consistent with a
  non-special Aronszajn tree — so **PID cannot supply the gate**. It can speak
  where MA_{ω₁} cannot (MA contradicts CH, PID does not): PID on the fiber order,
  with the ideal generated by the down-sets, makes alternative (2) *exactly*
  fiber-specialness, reducing the CH-side consistency question to **(Q-PID)** —
  is that ideal a P-ideal in the mod-finite sense? — which is strictly weaker
  than the σ-directedness of `D(e)` that provably fails. Two further frames named
  with first steps (build the witness by recursion under CH/◊; audit whether
  fiber-specialness is actually *sufficient*, §50's unaudited "plausibly"). Also
  recorded: a down-set of `D(e)` meets every single level infinitely often, so no
  level-organised decomposition can be fiber-special. Central question open.

- **§56 — the sufficiency claim audited, and it fails.** §50's load-bearing
  step, "fiber-special ⟹ the block game dies ⟹ `ρ₃` *plausibly* schedules",
  **does not hold as stated**. Writing the diagonal ranking down as an explicit
  dip assignment and computing the leftover `L_u` gives `L_u ∩ (Λ+k)` finite for
  **every k** — the block-localized form of condition (i), strictly weaker than
  (i), which demands `L_u` finite. A leftover spread over infinitely many blocks,
  finitely in each, violates (i) and is invisible to §50's permanent-leak
  mechanism (which needs infinitely many points in *one* block). So the crux is a
  **conjunction**: (C1) fiber-specialness — all §51–§54 narrowed — **and** (C2)
  block-spread control. **Theorem A4** (proved; 9432 instances in
  `tools/walk-check.py`) localizes (C2): an above-trace drop `ξ = μ+n` of `α`
  against `β` has `n ≤ ρ₁(α,β)` or `ρ₁(ξ,α) = 0`, and the latter set is finite by
  Handbook 1.16(a) and foldable into the dips — so above the trace **(C2) ⟺ the
  ranking dominates the walk bars along every down-set**, both sides divergent
  (bars by M3, rank by fiber-specialness). Named **(Q-spread)**; it is once again
  a monotone dominating selection, the program's own signature. **Consequence:
  settling (Q-rows-lim) or (Q-T) affirmatively would not settle schedulability** —
  §51–§54 remain correct mathematics aimed at half the target. Discharged
  positively on the way: for binary-valued `e` the value-form (ii) is
  *equivalent* to the set-form (i), so §50's "modulo the value-form bookkeeping"
  hedge costs nothing over `ρ₃`. Method note recorded: the gap survived four
  sections because "finite in every block" and "finite" read the same in prose —
  every "⟹ plausibly" should be cashed out as an explicit construction before the
  next section builds on it.

- **§57 — (Q-spread) localized, and its level-factored side refuted.**
  Assuming (C1), **(C2) ⟺ the level-minima `m_u(α) := min{rank(x) : x ⊑ u,
  γ(x)=α}` dominate `ρ₁(α,γ(u))` off finitely many levels, for every `u`** — at
  each level all but finitely many elements of `↓u` already outrank any fixed
  bar, so (C1) does most of (C2) for free and the whole content is the minima.
  Down-sets are level-full (`(α, B_α ∩ C) ⊑ (β,C)`), so the reduction bites.
  **Theorem X [ZFC]**: there is **no** `g : ω₁ → ω` with `{α<β : g(α) <
  ρ₁(α,β)}` finite for every `β` — Handbook 1.16(a) plus regularity of ℵ₁, the
  same three lines as `ρ₁`'s nontriviality and Theorem P, now in a third role.
  **Corollary X2**: the domination (C2) requires cannot come from any *level*
  function, so all of (Q-spread) lies in per-element freedom — **Question 1's own
  dichotomy one level down**, with the level-factored side refuted on both sides
  (Theorem B's corollary there, Theorem X here); first time the program's
  self-similarity is proved rather than observed. **Corollary X1**:
  `{α : sup_β ρ₁(α,β) = ∞}` is infinite below every large `β`, so the bars
  diverge in the second argument too — whence a checkable **necessary condition**:
  any (C2)-rank has exceptional sets growing without bound along every
  ⊑-increasing ω-chain, which kills every fixed-`k` block-guarding scheme.
  Second numeric caveat recorded: the truncated model shows `ρ₁(α,·)` eventually
  constant, which would make the whole section vacuous — an artefact, refuted in
  ZFC by Corollary X1, and caught only because the proof was already in hand.

- **The bundle layer: `GradedAction.prod` / `Bridge.pair`.** Five instance
  families inhabit the interface, and the security program added cost budgets —
  but each accumulates *one* certificate, so the interface could not express
  "this artifact is 2-Lipschitz **and** costs at most 40 **and** mediates every
  access". The product supplies it, and the content is that the composition law
  is unchanged: **`Bridge.pair_comp_cert`** proves composing a bundled bridge is
  componentwise composition — no interaction term, no extra hypothesis — so
  carrying `n` guarantees costs `n` independent accumulations and nothing more.
  Non-vacuity is witnessed with two genuinely different monoids on one carrier
  (`bundle_accumulates_componentwise`): a single composition advances an additive
  budget `3 + 4 = 7` and a worst-case bound `max 5 2 = 5` side by side. Axioms:
  `propext` (plus `Quot.sound` where `omega` is used); no `sorry`. **This is the
  first stage of the composable-core work** — the security program is currently
  16 separate toy languages with zero cross-brick composition, and this is the
  algebra the unification needs.

## transport-kernel — mathlib instances

- **Tier 1** — mathlib olean cache stood up (the infra that gates importing
  anything).
- **Tier 2a** — `comp_reconstructs_lipschitz`: the genus receives mathlib's
  `LipschitzWith` and reconstructs `LipschitzWith.comp`.
- **Tier 2b** — `comp_reconstructs_holder`: a *non-scalar* pair certificate
  `(C, r)` with a semidirect-product law; the same `Bridge.comp` reconstructs
  `HolderWith.comp`. Two accumulation algebras, one composition law.
- **Tier 3** — Markov-kernel / Dobrushin (total variation), finite state spaces:
  the data-processing inequality `dpi` proved from scratch (coupling/overlap
  argument — mathlib has no DPI), `Bridge.ofKernel`, and
  `comp_reconstructs_dobrushin`: advanced composition as generic certificate
  accumulation. The quantitative centre, no longer prose.
- **Tier 3b** — the measure-theoretic Dobrushin contraction, arbitrary
  measurable state spaces: `tvDist` (TV distance for measures — absent from
  mathlib) and `tvDist_comp_le`, the DPI for `ProbabilityTheory.Kernel`
  pushforward `κ ∘ₘ μ`, via Hahn decomposition + the coupling argument in
  additive integral form (subtraction-free; no Fubini). Lands in the *same*
  graded action as Lipschitz (`lipGA`), and `Bridge.comp` reproduces
  submultiplicativity (`comp_reconstructs_dobrushin_measure`), also at kernel
  level through mathlib's own `∘ₖ` (`tvDist_kernel_comp_le`). The "finite-state
  only" caveat is discharged.
- **Tier 3c** — the discretization consistency lemma: `Dist.toMeasure` (Dirac
  embedding) with `tvDist_toMeasure` proving the finite `tvd` and the
  measure-theoretic `tvDist` are the same number, `toMeasure_push` matching the
  finite pushforward with `κ ∘ₘ ·`, and `dpi_via_measure` re-deriving the finite
  DPI as a corollary of the measure-theoretic one. The "not yet formally
  linked" caveat is discharged; the two Dobrushin developments provably agree
  where they overlap.
- **Tier 4 recon (Q0) — the quantum slot, gap confirmed.** Physlib
  (leanprover-community, ex Lean-QuantumInfo + PhysLean) inventoried:
  `MState`, `TrDistance` (basic properties only), strong `traceNorm` API,
  first-class PTP-vs-CPTP distinction, Jordan pos/neg parts via cfc, and
  a sandwiched-Rényi DPI — but **no trace-distance contractivity and no
  Dobrushin coefficient**. Same toolchain as this repo (v4.31.0). The
  mathlib-had-no-DPI situation replays one level up; Q1 (PTP-generality
  trace-distance DPI) is a confirmed open slot with all ingredients
  present. Plan Q0–Q5 recorded in `NOTES-quantum-tier4.md`; drift guard
  extended to transport-kernel notes.
- **Tier 4 (Q1+Q2) — the quantum DPI, done and received.**
  `QuantumDobrushinReceive.lean` against Physlib (pinned; mathlib revs
  identical, cache shared): the Jordan form of the trace norm
  (`‖A‖₁ = tr A⁺ + tr A⁻`), the quantum DPI at positive-trace-preserving
  generality (`traceNorm_map_le` — complete positivity not assumed;
  Ruskai), trace-distance contraction for `PTPMap`s on states, the
  quantum Dobrushin bound with the DPI as its η = 1 instance, and the
  reception `Bridge.ofPTPChannel` + `comp_reconstructs_quantum_dobrushin`
  in `dobrushinGA` — the same graded action as the finite classical tier.
  Finite kernels, measure kernels, quantum channels: one composition law.
  Axiom-clean (standard three) against the full Physlib cone — none of
  Physlib's 48 sorries are in it. Q3 (diagonal consistency) and Q4
  (quantum-DP two-row check) remain.
- **Tier 4 complete (Q3–Q5).** Q3: `QuantumDobrushinConsistency.lean` —
  diagonal embedding `Dist.toMState`, `trDistance_toMState` (quantum
  trace distance on diagonals = classical `tvd`), `Kernel.toQChannel`,
  intertwining, and `classical_contraction_via_quantum`; the tower
  closes — finite ↪ measure and finite ↪ quantum, all machine-checked to
  agree; axiom-clean. Q4 (research pass): quantum (ε,δ)-DP is the
  hockey-stick condition; HRSF's sequential composition is a product of
  contraction coefficients — exactly this tier's certificate
  accumulation — but no general adaptive composition theorem and no
  tensorizing f-DP analogue exist: literature gap or genuine interface
  boundary, deliberately left open. Q5 decision: the five DPI-core
  declarations (zero TransportKernel dependencies) are PR-shaped for
  Physlib upstreaming; the Bridge reception stays in-repo.
- **Tier 5 — the reps theorem at actual ω₁ (`OmegaOneCoherent.lean`).**
  `TransportCalculus` added as a lake path dependency; `OmegaOne :=
  ω₁.ToType` (Type 0) models the abstract index: least witnesses from
  well-foundedness, σ-directedness from the regularity of ℵ₁
  (`Ordinal.iSup_lt_of_lt_cof`), countable segments from `#o.ToType =
  o.card` below ℵ₁, no top from countability under successors.
  `finiteP_iff_finite` bridges list-coverage finiteness to `Set.Finite`,
  so the statement reads in standard vocabulary:
  `omega1_reps_implies_trivial` — every coherent sequence on ω₁ with a
  pointwise level-monotone representative system is trivial;
  contrapositive `nontrivial_coherent_no_reps`. To our knowledge the
  first machine-checked theorem about coherent sequences on ω₁. The
  mathlib-free engine and its mathlib model are verified separately and
  compose. Axiom-clean.
- **Tier 5b — the obstruction made unconditional (`omega1_finiteToOne_not_trivial`).**
  `nontrivial_coherent_no_reps` was conditional on an imported negative
  existential — "Todorcevic's walk families are nontrivial" — whose proof is
  precisely the classical finite-to-one argument. That argument is now
  machine-checked at ω₁: `FiniteToOne C := ∀ w n, {u | u < w ∧ C.e w u ≤
  n}.Finite` is Handbook Lemma 1.16(a) verbatim, and
  `omega1_finiteToOne_not_trivial` proves **coherent + finite-to-one rows ⟹
  nontrivial**, via `countable_of_segments_finite` (a segment-finite set of
  countable ordinals is countable because `u ↦ |S ∩ Iio u|` is strictly
  monotone into `ℕ` — order type ≤ ω with no enumeration constructed) and
  `bounded_of_countable` (regularity of ℵ₁, reusing the existing σ-directedness
  instance). Composite: `omega1_finiteToOne_no_reps` — a coherent finite-to-one
  sequence on ω₁ admits **no** monotone representative system, with no cited
  nontriviality. What remains cited is only the positive,
  computation-checkable existence of such a sequence (Handbook 1.16(a)+(b) for
  ρ₁); the Lean statement is an implication, so non-vacuity still rests on
  that. Axiom-clean (standard three), no `sorry`. Set-theoretic side: notes §53
  (Theorem P).
- **Tier 5c — Theorem B⁻ machine-checked (`omega1_downDip_iff_trivial`).** The
  program's first formal *dip* theorem: `DownDip C` bundles finite per-level
  corrections whose leftover is finite at every top, and the equivalence says
  such a system exists **iff** the sequence is trivial. Substantive direction
  `omega1_downDip_trivial` follows the §53 prose step for step —
  `honest_antitone`, `bad_finite` (regularity of ℵ₁ concentrating countably many
  bounds), `eval_eq_of_honest` (stabilization by `sInf` leastness plus
  antitonicity) — with `DownDip.ofTrivial` the converse, which also settles
  non-vacuity. This matters because notes §53's **Theorem Q** (the kill of
  (Q-rows-lim)'s dense failure mode) depends on B⁻: that kill now rests on a
  formal theorem plus Theorem P rather than two fresh prose arguments. The
  *upward* Theorem B stays careful-prose — its witness-concentration step for
  unbounded columns is exactly the part the downward dual avoids. Axiom-clean,
  no `sorry`.

## Consolidation

- Merged the three previously-separate repos into this monorepo with a top-level
  README and CHANGELOG. Aligned the `cert` field name and the framing across
  `transport-calculus` and `transport-kernel` (the two had drifted —
  `coeff`/`cert` and stale "genus" language — while developed separately).
