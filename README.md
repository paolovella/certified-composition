# Certified composition

Three Lean 4 formalizations forming one line of work, unified by a single
discipline:

> **Evidence carries its hypotheses, and composition *accumulates* them —
> never discharges or coerces silently.**

Each sub-project is a self-contained Lean package. All are `no sorry` and
axiom-audited; the two mathlib-free ones build instantly, the third needs the
mathlib olean cache (and compiles its Physlib dependency locally).

| dir | what | deps | status |
|---|---|---|---|
| [`conf-typing/`](conf-typing) | confidentiality-typing framework (the IMP timing instance + meta-theory) + the security seam/reception modules | `transport-calculus` (path; mathlib-free) | core closed; security program active (`VULN-COVERAGE.md`) |
| [`transport-calculus/`](transport-calculus) | the transport interface, its qualitative frontier, and the set-theoretic research line it opened | none (mathlib-free) | core proved; frontier reduced to one open question, shipped to its community |
| [`transport-kernel/`](transport-kernel) | instances of the interface against libraries other people built | mathlib, Physlib, `transport-calculus` (path) | tiers 1–5 done |

## The through-line

The same accountancy appears at every level:

- **`conf-typing`** — a discharge of a confidentiality obligation carries its
  evidence: `Discharge.pol` bundles `(φ, proof)`, not bare membership;
  `confidential_transport` carries both strata across the conformance gate;
  the assumption ledger tracks which theorem consumes which condition.
- **`transport-calculus`** — that accountancy made the primitive object. A
  `Bridge` is a map bundled with a certificate; `Bridge.comp` accumulates
  certificates (a monoid action on a distance order), and dropping the
  accumulation makes the composite's proof fail to type-check. Zero axioms.
- **`transport-kernel`** — the interface receives objects *someone else
  built*, and the receptions compose under **one generic law**: mathlib's
  `LipschitzWith` and `HolderWith`, finite Markov kernels, measure-theoretic
  kernels, and quantum channels all land in graded actions served by the same
  `Bridge.comp`. Advanced composition — classical, measure-theoretic, and
  quantum — is certificate accumulation, as theorems.

## What each sub-project actually proves

**`conf-typing`** (mathlib-free; core meta-theorems axiom-free):
- the parametric framework — admissibility (A1–A3), joint generation, bounded
  delimited-release policy, the conformance gate, Boolean soundness;
- the typed rejection of cross-stratum evidence, proved *J-invariant*;
- the corrected §10: among admissible properties the only nondegenerate
  2-safety one is noninterference; separability is the congruence-refinement
  of 2-safety; the k-safety hierarchy above 2 is kernel-determined.

**`transport-calculus`** (mathlib-free; `Bridge.comp` axiom-free):
- `GradedAction M D` and `Bridge.comp` — the interface and its composition law;
- `GradedAction.prod` / `Bridge.pair` — **bundles**: several certificates carried
  by one artifact, with `Bridge.pair_comp_cert` proving composition is
  componentwise (no interaction term), witnessed by two different accumulation
  laws advancing side by side (`bundle_accumulates_componentwise`);
- the **qualitative frontier**, bracketed by theorems: complete-lattice /
  image-sup / bounded / directed-finite factorization; the `D3` escapee; the
  cofinal-ruler and countable-cofinality theorems; the transfinite selection
  theorem (`prefix_bounded_cofinal_factors`) with `PrefixBounded` as the
  cardinal-free κ-directedness; the hunt's walls
  (`sigma_directed_cofinal_factors`, `lists_bounded_factors`, `Fb`);
- the **reps engine, machine-checked**: over an abstract index with least
  witnesses, σ-directedness, and countable segments, a coherent sequence with
  a level-monotone representative system is trivial
  (`reps_implies_trivial`), paired with the ω-boundary witness showing the
  regularity hypothesis is load-bearing (`omega_concentration_fails`);
- the **research line** the frontier opened, in prose at graded rigor:
  [`NOTES-coherent-escapee.md`](transport-calculus/NOTES-coherent-escapee.md)
  (fifty-seven sections: reps ⟺ trivial in ZFC, chain-freeness of the fiber
  order, the no-go for kill templates, forcing-locality, Theorem B —
  uniformizing dip systems ⟺ trivial — and its downward dual Theorem B⁻,
  the reduction of the whole question
  to one game invariant, the game's Φ-completeness, the ◊-side kill of
  "everything schedules" (Theorem C), the descent of the crux to a
  threshold sequence θ(ρ₃) whose nontriviality is now settled in ZFC
  (Theorem P) — killing the dense failure mode of the residual question
  (Theorem Q), the explicit trace formula and Theorem V — which closes the
  natural `thr_β`-transfer route as vacuous and reduces the residual to
  limits of limits — the frame audit (§55: *special ⟹ Lipschitz* for coherent
  trees, so `T(ρ₁)` clears in ZFC the gate that is open for `ρ₃`; and PID as a
  CH-compatible route), **the correction of the reduction itself** (§56: the
  crux is a *conjunction* — fiber-specialness controls the leftover only block
  by block, so §51–§54 narrowed one conjunct), its residual (Q-spread)
  localized to level-minima and its level-factored side refuted (§57,
  Theorem X) — and the two-sided independence
  program whose standing open problem is the canonical walk sequence ρ₃
  under CH), and the standalone problem statement for set theorists,
  [`PROBLEM-dip-schedulability.md`](transport-calculus/PROBLEM-dip-schedulability.md):
  **is every strongly dip-schedulable coherent sequence on ω₁ trivial?** —
  level-factored case proved, toolbox machine-checked; conjectured false
  under MA_ω₁ with canonical witness ρ₃ (the hard part, a ccc, is in ZFC),
  open under CH.

**`transport-kernel`** (mathlib + Physlib + `transport-calculus`):
- **Tier 2** — `comp_reconstructs_lipschitz`, `comp_reconstructs_holder`: the
  generic `Bridge.comp` reconstructs mathlib's own composition lemmas, for a
  scalar and a non-scalar (semidirect-product) certificate algebra.
- **Tier 3** — the Dobrushin data-processing inequality for finite Markov
  kernels, proved from scratch (mathlib has no DPI), with
  `comp_reconstructs_dobrushin` and `coeff_submul`.
- **Tier 3b** — the measure-theoretic DPI over arbitrary measurable state
  spaces (`DobrushinMeasureReceive.lean`: `tvDist`, `tvDist_comp_le`,
  `comp_reconstructs_dobrushin_measure`), built on mathlib's
  `Measure`/`Kernel`.
- **Tier 3c** — discretization consistency: the finite and measure-theoretic
  developments provably agree (`tvDist_toMeasure`, `dpi_via_measure`).
- **Tier 4** — the **quantum** DPI against Physlib
  (`QuantumDobrushinReceive.lean`): trace-distance contraction at
  positive-trace-preserving generality (`traceNorm_map_le` — complete
  positivity not assumed), the quantum Dobrushin bound, the reception in the
  *same* graded action as the finite classical tier
  (`comp_reconstructs_quantum_dobrushin`), and diagonal consistency
  (`classical_contraction_via_quantum`): the finite development embeds into
  both generalizations, all machine-checked to agree. The DPI core is
  PR-shaped for Physlib upstreaming.
- **Tier 5** — the reps theorem at **actual ω₁** (`OmegaOneCoherent.lean`):
  mathlib's `ω₁.ToType` models the abstract index (σ-directedness *is* the
  regularity of ℵ₁), giving `omega1_reps_implies_trivial` — every coherent
  sequence on ω₁ with a pointwise level-monotone representative system is
  trivial — and its contrapositive for nontrivial sequences. To our knowledge
  the first machine-checked theorem about coherent sequences on ω₁. The
  mathlib-free engine and its mathlib model are verified separately and
  compose. **Now unconditional**: `omega1_finiteToOne_not_trivial` machine-checks
  the classical ZFC engine — a coherent sequence on ω₁ with *finite-to-one rows*
  (Todorcevic's Handbook 1.16(a) for ρ₁, verbatim) is nontrivial — so
  `omega1_finiteToOne_no_reps` needs no imported nontriviality theorem; what
  stays cited is only the positive existence of such a sequence. And
  `omega1_downDip_iff_trivial` machine-checks **Theorem B⁻** — a coherent sequence
  on ω₁ admits a *downward dip system* iff it is trivial — the program's first
  formal dip theorem, and the one Theorem Q rests on.

## The security claim (the original goal)

The program's origin is a framework for coding that is *inherently* free of
vulnerabilities. The honest form of that claim — which real vulnerability classes
are excluded by construction, relative to which model, spec, and TCB, and which are
merely carried, assumed, or out of scope — is maintained as a verdict-per-class map
in [`VULN-COVERAGE.md`](VULN-COVERAGE.md), built on the proved classification
machinery (`qualitative_admissible_is_JNI`, `simA3_iff_respectsCoarsening`,
`summary_not_composable`, `confidential_transport`, `Bridge.comp`) and the
integrity module it forced into existence (`taint_is_JNI` — integrity NI is a
relabeling, axiom-free; `blacklist_not_admissible` — output-blacklist
sanitization fails A3, axiom-free). Thirteen classes, eight verdicts, every verdict
graded; the popular-but-wrong formulations (output blacklists,
`(ε,δ)`-composition) are rejected by theorems, not by taste. The seam row is
proved end-to-end: certified components compose with *computed* certificates
(`releases_seq`, axiom-free; the non-scalar `seqRelease`), the reception into
the transport interface is an equivalence (`bridge_iff_releases`), the generic
`Bridge.comp` reconstructs the seam theorem (`comp_reconstructs_seq_release`),
and both seam hypotheses are proved load-bearing by explicit failure witnesses
(`broken_seam`, `channel_certs_do_not_compose`). And the flow-property verdicts
are **generated, not hand-proved**: a syntax-directed checker (`secCheck`,
`secCheckD`) manufactures the boundary certificates, so a component earns its
verdict by `decide` — `checker_rederives_pleak_bound` reproduces the hand-proved
Paper-1 release bound as checker output (choice-free), multi-tenant isolation is
checked both ways (`multiplex_isolates_A/B`), and two syntactic checks compose
into one certified Bridge in the transport interface (`certified_pipeline`). And
every guarantee carries its **trusted base** as a composable ledger: a component's
assumptions (`CondBoundary c P Γ`) accumulate by union under the same `Bridge.comp`
(`ledgerBridge_comp_ledger`), can never be silently laundered into evidence
(`ledger_no_silent_discharge`), and are surfaced automatically for a composed
supply chain (`supply_chain_ledger`) — the bill of materials as a theorem. And the
clock is a certified channel, not just a caveat: a timing-sensitive checker
(`secCheckT`) forbids secret-dependent branching and certifies the whole
instrumented outcome — store, running time, and branch trace (`secTyT_sound`) —
rejecting the store-checker's timing-leak witness (`ptime_rejected_T`) — and a
secret branch whose duration is *declared* released is bounded rather than forbidden
(`ptime_timing_released`), so the clock is closed by construction or opened exactly
as far as declared. And the language now has **loops**: a fuel-indexed semantics
opens the *termination* channel (a secret-guarded loop leaks its bit through
whether it halts), which a termination-sensitive checker closes (`wsecTy_sound`),
with the loop-free fragment embedding faithfully (`wexec_embed_eq`) — the model
grew rather than forked. And the seam composes looping components too
(`WOutNI_seq`), with divergence threading through the boundary in lockstep — the
composition differentiator now covers unbounded iteration. And looping components
land in the transport interface itself (`Bridge.ofWComponent`,
`wbridge_iff_sound`), with a **halting query** making termination a first-class
coordinate of the distance — so termination-sensitive security is literally a
contraction, in the same `GradedAction` as Lipschitz and Dobrushin. And the model
now grows to a **heap**: a machine that can get *stuck* on a wild dereference, with
a flow-sensitive checker whose programs provably never do (`mcheck_safe`) — memory
safety generated by construction, not merely carried, and the first *safety*
property (vs. the confidentiality channels) in the framework — extended to rule
out **use-after-free and double-free** (`fcheck_safe`) via a liveness-tracking
machine and a linearity checker. And the two halves of the framework — the
confidentiality channels and the memory machine — **unify**: noninterference now
holds over a labeled heap (`hsecTy_ni`), so a secret in a High heap cell cannot
leak into a Low variable, with memory safety and information flow as two
independent, composable invariants of one machine. And one channel is made
**real**: injection is no longer an abstract property shape but an actual query
with a real tokenizer — string concatenation is proved injectable
(`concat_injectable`, `' OR …` as a theorem) and parameterized queries proved
injection-safe by construction (`param_immune`), the real attack and the real fix
— and connected to a running program by a flow-sensitive taint checker
(`qcheck_ni`) that rejects the injectable sink with acceptance proved sound, the
shape of a real SQL-injection static analyzer — extended to **stored
(second-order) injection** over a persistent database, where per-cell taint
catches what the per-request shortcut misses (`dbcheck_ni`, the shortcut proved
unsound). The same "make a channel real" method then generalizes to a second
class: **path traversal** (CWE-22) — the `../../etc/passwd` attack proved
(`traversal_escapes`) and the leaf-name API proved safe by construction
(`openLeaf_contained`). And the confidentiality core is generalized past binary
High/Low to an arbitrary **security label lattice**: noninterference holds for any
lattice and any observer level (`latSecTy_ni`), with a diamond-lattice witness of
two mutually-incomparable secret compartments that the binary model cannot express.
And **pointer aliasing** is handled: exact-address tracking rules out
use-after-free through an alias (`acheck_safe`) — `alloc p; copy q p; free p;
access q` is caught (`alias_uaf_rejected`), dropping the no-copy restriction that
kept brick 12's `free` sound. And memory safety extends to **loops**: when
allocation addresses stop being static under `while`, a fixed-point (loop-invariant)
checker keeps it sound (`hlcheck_safe`, by fuel induction) — brick 11's heap meets
brick 7's loops. Finally, the injection guarantee attaches to **source text**: a
recursive-descent parser with a proved round-trip theorem (`parse_print`) chains
through the checker to an end-to-end result (`source_injection_free`) — a security
claim about parsed source, not a hand-built AST — and a **lexer** (`lex_print`)
takes it down to a character string, so the whole chain string → lex → parse →
check → theorem is machine-checked. Finally, the last hard memory combination:
**free under loops** (`flsafe`) — `free` and unbounded iteration coexist soundly
via linearity carried as a loop invariant, with the fixed-point rule catching the
cross-iteration double-free. The named depth follow-ons then land: **may-alias
under loops** (`alsafe`) — a may-alias partition makes pointer `copy` + `free` +
loops sound, the aliasing case linearity forbade; **a richer alphabet**
(`rich_source_injection_free`) — multi-character lexemes under a maximal-munch
scanner with a proved longest-match round trip; **a fuller query grammar**
(`param_correct_N`) — parameterization proved injection-safe over a template with
`n` literal slots; and **a second real sink** (`argv_correct`) — OS command
injection (CWE-78) closed by the same data-not-structure discipline as SQL
injection and path traversal; and **decimal identifiers** (`ofDigits_toDigits`) —
a verified mathlib-free decimal codec so the lexer reads real multi-digit numbers,
closing brick 25's last residual; and **log injection** (`field_correct`) — a
fourth made-real sink (CWE-117), the newline record-separator, with structured
logging immune by construction; and **fixpoint may-alias** (`ALInv_coarsen`) — the
may-alias loop analysis now infers a coarsening invariant by iterating to a fixed
point (the iteration proved to terminate, `loopFix_terminates`, and complete for the
lattice top, `loopSearch_complete`), folded into a full recursive checker
(`alsafe2`) — mutually recursive with the fixpoint iterator, so a whole program
containing such a loop, nested to any depth, is proved safe end to end (`prog_safe`,
`nested_prog_safe`), with a body-guided merge (`findMerge2`) that unifies the classes
the loop actually aliased — reaching the strict-intermediate fixed points a blind
heuristic misses (`weak_prog_safe`) — accepting alias-maintaining loops the one-pass
rule rejected; and **string literals with escapes** (`segsE_buildEsc`) — the last
injection-axis follow-on: complete escaping is proved sound for every value and
faithful to it, the unescaped-escape-character bug is proved injectable
(`escBad_injectable`) and located (`escBad_noBS_ok`), and — the point — each escaper
is injectable against the *other* dialect's tokenizer
(`escaping_is_convention_relative`), so escaping carries a load-bearing assumption
that lands in brick 4's ledger (`escaping_no_silent_discharge`) while
parameterization needs the empty one (`escaping_reducible_parameterization_in`);
and **complete mediation** (`medCheck_sound`) — brick 35 splits row 7's
last `[classified]` grade in two: missing authorization is a decidable
all-paths program property, generated and proved, while policy correctness is
proved *not* to be program-decidable (`policy_correctness_not_witnessed`), so
the CARRIED half is now demonstrated rather than asserted;
and **resource exhaustion** (`cost_seq_is_mul`, `dos_unbounded`) — brick 34
proves row 10's reduction: a uniform cost budget whose accumulation is a
`GradedAction`, so a security row lands in the transport calculus's own algebra;
algorithmic-complexity DoS is proved to admit *no* uniform budget, and a
constant-initialised budget restores one; and **speculative execution** (`spec_inert`) — brick 33 closes the
**last** OUT-OF-MODEL row by running the same recipe a third time: a
transient-execution machine where Spectre-v1 really does leak the secret as a
touched address (`spectre_leaks`) while the architectural machine sees nothing at
all (`arch_indistinguishable`), and a fence check whose soundness makes
speculation *observationally inert*, so every architectural guarantee transfers;
and **races / TOCTOU** (`racefree_all_schedules`) — the last wholly-unmodelled
common class, closed by building the map's named extension: a demonic-scheduling
small-step machine where the check-then-act withdrawal really does go negative
(`toctou_interleaving_unsafe`) while every *sequential* schedule of it is safe
(`sequential_model_misses_races` — the model gap as a theorem), the atomic fix is
proved safe under every interleaving, and the decidable race-freedom check reduces
the concurrent obligation to a sequential one per critical section.

### The composable core (in progress)

The security program's bricks were, structurally, sixteen separate toy languages with no
cross-brick composition — so no program could carry two guarantees at once, which is the
one place the repo's own headline most needs to hold. Two stages have landed:
`GradedAction.prod` / `Bridge.pair_comp_cert` (bundles accumulate componentwise, no
interaction term) and `ConfTyping/Unified.lean` (`UCmd` = `WCmd` + `check`/`access`, with
`uexec_embed_eq` proving the While development is a *fragment* of it, so brick results
transfer — `ucost_of_cost` — instead of forking). Stage 1c has landed
(`ConfTyping/Bundle.lean`): one checker `ucheck` emitting a bundle, one soundness
theorem, and a worked request handler carrying a **cost budget and complete
mediation at once** (`handler_bundle_end_to_end`) — the first program here holding
two guarantees simultaneously, with the two halves composing by *different* laws
(budgets add, authorization sets thread, no interaction term). Stage 1d adds the
third (`ConfTyping/UnifiedNI.lean`): noninterference lifts to `UCmd`, and because
resource names are syntactic constants `check`/`access` add no flow channel at all.
`handler_three_certificates` is the deliverable — **one program carrying a budget,
mediation and noninterference**, composing by three different laws. Stage 1e then tested whether the
mechanism *scales*: a fourth component — the **trusted base**, accumulating by
`++` — slotted in with a four-line lemma (`UCertL.seq`), and carried a real
payload: row 7's CARRIED half stopped being prose and became a load-bearing
ledger entry (`row7_carried_is_a_ledger_entry`). Still loop-free, and the NI
result is bought by having no store-dependent resource selection
(`access_is_static_by_design` records the price).

## Scope — what is *not* claimed

- The transport interface is **not** asserted to be the "correct general
  notion" of certified transport. It is a small interface that five
  independent instance families now inhabit under one composition law —
  status earned by instances, revisable by counterexamples.
- The qualitative frontier's last question — dip-schedulability — is **open**,
  not settled: the notes record sixteen verdict flips, each forced by a proof
  or a refutation, and the problem statement grades every arrow ([proved] /
  [argued] / [open]). The MA side of the independence program is a conjecture
  on a cited ccc, not a theorem; the CH side is one standing open problem
  (ρ₃), not a verdict.
- The quantum-DP row (Q4) is a research-pass verdict with two live readings
  (literature gap vs. genuine interface boundary), deliberately unresolved.
- "First machine-checked theorem about coherent sequences on ω₁" is a
  to-our-knowledge claim after an adversarial literature pass (notes §13),
  not a certainty.
- The **method** — adversarially attacking one's own statements and narrowing
  to machine-checked theorems — is how the work was produced, not a validated
  methodology. It travels only if a second hand runs it.

## Building

```sh
# mathlib-free — instant
cd conf-typing        && lake build
cd transport-calculus && lake build

# mathlib + Physlib — needs the olean cache; Physlib's modules compile locally
cd transport-kernel   && lake exe cache get && lake build
```

All pinned to Lean `v4.31.0` (see each `lean-toolchain`); transport-kernel
pins Physlib to a fixed commit sharing this repo's mathlib revision, so the
cache is shared.

`tools/check-claims.sh` guards the READMEs against status drift (retired
claims resurfacing, modules or notes going unmentioned); run it after landing
anything. Per-subdir `README.md` and `CHANGELOG.md` carry the detail; the
top-level [`CHANGELOG.md`](CHANGELOG.md) traces the arc across all three.
