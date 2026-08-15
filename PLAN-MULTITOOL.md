# Using the other six tools on *this* project

*Written 2026-08-14. **Retargeted the same day** — see §0.*

## 0. What this plan was, and what it is

The first version of this file planned to **integrate a different project's verification
estate** (`sentinel/formal`) into this repo as a source of foreign certificates. That was a
misreading of the request. The ask was to **use alloy, coq, kani, lean, tla and verus *for
this project*** — as tools brought to bear on `certified-composition`'s own claims, not as
producers whose output this repo consumes.

Retargeted accordingly. What survives unchanged is **stage E**, the emission census: what
each tool actually emits when you run it is worth knowing either way, and two of its
findings (Kani's `unwind` annotation is not a bound; Alloy's scope lives in `receipt.json`)
bear directly on the new plan. What is dropped is every stage framed around receiving
sentinel's artifacts. Sentinel is not touched by this repo and is not a dependency of it.

The prior-art section (§2) is kept because it still bounds what a *claim* here could be.

## 1. The point

The repo is **Lean-only**, and its central claim is that certified programs exclude named
vulnerability classes. Two things follow that no amount of further Lean can supply:

1. **A proof is only as good as its model.** `leakSafe_sound` is a theorem about `uexec`.
   If `uexec` is the wrong model, the theorem is true and beside the point — the repo has
   its own name for this (`sequential_model_misses_races`). An **independent
   implementation** searched exhaustively by a *different* tool is the only cheap way to
   attack that.
2. **A bulletproof framework needs a checker you can run**, and `certcheck` is currently
   trusted extraction. A *verified implementation* is a different artifact.

So the six tools are used here as **adversaries and as implementations**, in that order.

## 2. The stages

Same discipline: falsifiable milestone, kill criterion. Letters continue from F.

### Stage G — Kani as an adversary against the newest theorem. *(1–2 sessions. First.)*

`LeakCert.lean` is hours old and its soundness proof is the least battle-tested thing in
the repo. Port `uexec`'s memory fragment and `lcheck` to Rust, and let Kani search
exhaustively over symbolic programs for one the checker **accepts** that **leaks**.

Note what this is *not*: it is not re-proving `leakSafe_sound`. It is attacking the gap
between the theorem and the intent — a modelling error, which is the class of error Lean
cannot see. Precedent: the `alloc p ; check r ; free p` hole was found **by hand** while
writing the module; a model checker should have found it in seconds, and this stage is the
test of whether it finds anything *else*.

- **Milestone:** either a program Kani produces that `lcheck` accepts and that leaks — which
  is a defect in `LeakCert.lean` and the best possible outcome — or an exhaustive
  no-counterexample result at a stated program size, recorded with that size.
- **Kill criterion:** if the Rust port has to diverge from `uexec` to be checkable, it is
  testing a different semantics and proves nothing. Say so and stop.
- **Done, first pass** (`cross-check/leak-kani/`). An independent Rust re-implementation of
  `uexec`'s memory fragment and `lcheck`, written from the Lean and matching it rule for
  rule on the modelled fragment.
  - **No counterexample.** Over symbolic 5-node programs, 2 variables, 3 addresses and
    symbolic branch decisions, Kani found no program that `leakSafe` accepts and that leaks
    (447 checks, 0 failed, 877 s). The assertion is `SUCCESS`, not `UNREACHABLE`.
  - **And the negative is not vacuous — checked, not assumed.** A second harness asserts
    that no accepted program allocates; Kani **refutes** it, producing an accepted,
    completing program that really does allocate (1104 s). A "no counterexample" result
    without this beside it would be worth nothing.
  - Two concrete witnesses run in CI: `alloc p ; free p` is accepted and allocates, and
    `b06` is **refused by the independent port and really does leak** on the `skip` arm —
    the Lean finding reproduced by code that shares nothing with it.
  - **Kill criterion not tripped, and the divergences are argued rather than waved at.**
    `assign`/`load` write a non-address where Lean writes a value: accepted programs never
    free through an alias (a free requires the variable to be tracked, and tracking comes
    only from `alloc` into it), so the difference cannot hide a leak. `hop .store`,
    `deref`, `access` and `sop` are omitted because none touches `live` or the pointer
    store. `pickAddr`'s reuse-before-fresh **is** modelled, since address reuse is exactly
    where an ownership invariant could break.
- **What it does not cover, and both are real.** The port is **loop-free**, so `lcheck`'s
  fixpoint rule is untested by this. And 5 nodes / 2 variables / 3 addresses is a **bound** —
  a clean run at size 5 is a statement about size 5, which is what stage F exists to say.

### Stage H — Alloy against the algebra. *(1–2 sessions.)*

`GradedAction`'s laws and `bmul`'s composition are relational and small — Alloy's home
ground. Model the grade monoid and its claimed laws, and search small scopes for
counterexamples to associativity, to `bounded_comp_sound`, and to
`bounded_grade_does_not_factor`.

- **Milestone:** an Alloy model whose `check`s pass at a stated scope, with the scope
  recorded — plus a deliberately broken variant that Alloy *does* refute, so the model is
  known to have teeth.
- **Kill criterion:** if the laws are so directly expressible that Alloy finds nothing and
  could find nothing, this duplicates the Python search already done. Record and drop.
- **Done, first pass** (`cross-check/alloy/BoundedGrade.als`). Four checks at `for 6 Int`,
  two expected to pass and two expected to **fail** — a model in which everything passes has
  not been shown able to refute anything.
  - `S2_BoundIsMinOfBounds` and `S3_BoundFactors` are **refuted**, independently confirming
    `min_unsound` and `bounded_grade_does_not_factor` from a tool with different arithmetic
    and a different engine (sat4j). `S1_BoundAssociative` and `S4_MinSoundWhenNonGrowing`
    find no counterexample, matching `bmul_assoc` and `min_sound_when_nongrowing`.
  - **The finding is the first run, which was wrong.** Alloy initially reported a
    counterexample to **associativity** — a theorem proved in Lean and brute-forced over
    42 875 triples. It was an artifact of **Alloy's own wrapping integer arithmetic**:
    `plus[g1,g2]` overflows bitwidth 6 and comes back negative. Constraining every value and
    intermediate well inside the bitwidth turns S1 UNSAT.
  - **That is the session's theme biting the method rather than the object.** A bounded model
    finder used as an adversary will manufacture a false refutation out of its own bounds,
    and the bound is not in the verdict — `SAT` said "counterexample", not "counterexample,
    modulo my integers wrapping". Both runs are kept in `captures/`, the artifact one under
    its own name, and a guard fires if the overflow constraint is removed.

### Stage I — Coq for kernel diversity on the load-bearing theorem. *(2–3 sessions.)*

Re-prove **one** theorem in Coq: the one the most claims rest on. Not a port of the repo —
a second kernel's opinion on a single statement. ETB names "diversity" as a distinct kind
of evidence, and this is the cheapest honest instance of it.

- **Milestone:** the same statement, proved in Coq, with `Print Assumptions` showing what it
  rests on — directly comparable to Lean's `#print axioms`.
- **Kill criterion:** if the Coq statement has to be weakened to go through, that difference
  *is* the finding; record it rather than papering over it.

### Stage J — TLA+ for the discharge protocol. *(2–3 sessions.)*

The ledger's lifecycle — assumptions accumulate, are discharged, must never be silently
dropped — is a **protocol**, not an algebraic law, and TLC checks protocols. Model
accumulate/discharge/compose and check that no reachable state discharges an assumption
without a proof.

- **Milestone:** `ledger_no_silent_discharge` as a TLC invariant, exhaustive over a stated
  instance.
- **Kill criterion:** if the protocol is a one-line invariant with no interesting state
  space, fold it into stage I.

### Stage K — Verus for a checker you can run. *(4–6 sessions. The real deliverable.)*

`certcheck` is trusted extraction. A bulletproof framework needs an implementation whose
correspondence to the spec is itself verified. Verus verifies real Rust.

- **Milestone:** a Rust `lcheck` with a Verus proof that it agrees with the Lean
  specification on a stated fragment, and a binary that runs.
- **Kill criterion:** if the Verus spec is a transliteration of the Rust rather than of the
  Lean, it proves the code equals itself. That is the failure mode to watch, and it kills
  the stage.
- **Done, first pass** (`cross-check/verus/lcheck.rs`, 15 verified / 0 errors, and a binary
  that runs).
  - **The kill criterion was designed against, not merely avoided.** The specification tracks
    outstanding allocations as a mathematical `Set<nat>` with `insert`/`remove`/`contains`,
    and its rules are `ConfTyping.lcheck`'s clause for clause. The implementation carries a
    `u8` machine word. `word_set` is the bridge, and the theorem is that the word always
    *denotes* the set — a refinement between two different objects, not an identity.
  - **It agrees with Lean.** The compiled binary and `ConfTyping.leakSafe` return the same
    verdict on all four demonstration programs (`alloc p ; free p` accept, `alloc p` refuse,
    `alloc p ; assign p` refuse, two-allocation accept), checked both ways.
  - `ops_valid` discharges the precondition at runtime, so the binary has a total entry
    point rather than an assumed one.
  - CI verifies the file and runs the binary whenever Verus is present, and a guard fires if
    the spec's signature stops being set-valued — which is exactly the transliteration the
    kill criterion names, and which would still verify.
- **Not done.** The verified fragment is **straight-line**: `seq` is a fold, and `ite`/`loop`
  are Lean-only. The branch-agreement rule — the one that catches `b06` — is therefore *not*
  in the verified implementation, and that is the next pass, not a detail.

### Not scheduled

**refinement** — the estate's `refinement/` was one markdown file, and this repo has no
refinement-typed artifact. Nothing to use it on yet.

## 3. What this plan does not claim

- It does not claim six tools will be used. Stage G's result decides whether the adversarial
  direction is worth continuing at all.
- It does not claim any of this makes the language more expressive. The 17% of corpus tasks
  that are inexpressible stay inexpressible; that is the freeze, and it holds.
- It does not claim independent search is proof. An exhaustive Kani result at size *n* is a
  statement about size *n*, which is exactly what stage F says to be careful about.

---

## 4. Appendix: the estate that prompted this (not a dependency)

`/home/paolo/.vella-workspace/sentinel/formal` — measured 2026-08-14, not estimated:

| tool | artifacts | guarantee shape |
|---|---|---|
| Verus | **59** `verified_*.rs` | unbounded proof, **axiom-carrying** |
| Kani (CBMC) | **124** harnesses | ~~bounded~~ → **unbounded here** (stage E: unwinding assertions on) |
| TLA+ | **48** specs + cfgs | TLC: exhaustive **over a finite instance**, + a probabilistic caveat |
| Coq | 8 `.v` | unbounded proof, axiom-carrying |
| Lean | 6 `.lean` | unbounded proof, axiom-carrying |
| Alloy | 2 `.als` | **bounded** — explicit scope; **the only genuinely bounded one** (stage E) |
| refinement | 1 `.md` | prose |
| tools | 11 scripts | the glue, and the interesting part |

And crucially, it already has **the hand-rolled version of everything this repo formalises**:

- `ASSUMPTION_REGISTRY.md` — named assumption families (`VERUS-ESCAPE-1`, `MERKLE-HASH-1/2`,
  `MERKLE-CODEC-1`, `AUDIT-FS-1…5`, `FLOAT-CONV-1…4`) with a canonical registration rule.
  **This is `Ledger`, in markdown.**
- `trusted-assumptions.allowlist` — 17 machine-checked escape hatches, enforced by
  `check-formal-trusted-assumptions.sh`. **This is `needs`, in bash.**
- `verus/assumptions.rs` — each kernel bound to *the narrowest trust boundary it needs*.
  **This is the computed-rather-than-fixed base, by hand.**
- `check-kani-parity.sh`, `check-verus-parity.sh` — the extracted code must not drift from
  production. **This is stage C's `hmap`, as a shell script.**

The estate is not a beginner's pile of tools. It is a disciplined trust practice that has
outgrown the notation it is written in.

### The one entry that defines the whole plan

`ASSUMPTION_REGISTRY.md`, line 25:

> `MERKLE-CODEC-1` … **partially discharged** — K141 (per-byte roundtrip, all 256 byte
> values, Kani CBMC) + K142 (length invariant: N bytes → 2N chars) prove the per-byte
> correctness **from which the 32-byte roundtrip follows by byte-independence**

Read what that sentence does. A **bounded, exhaustive Kani result** over one symbolic byte
is being used to **discharge a trusted axiom** that **Verus proofs depend on**, via an
**English lemma** ("by byte-independence") that *neither tool proved*. Three tools, one
trust boundary, and the load-bearing step is a phrase in a markdown table.

That is heterogeneous certificate composition happening in production. It is exactly the
object stages B–D built machinery for, and formalising *this one discharge* is worth more
than receiving all eight tools.

---

## 5. Prior art, kept because it still bounds the claim

This space is occupied. Pretending otherwise would be the same error `PLAN-2026-08.md` §2
was written to correct.

**Evidential Tool Bus** (Rushby, ICFEM 2005; Cruanes, Hamon, Owre, Shankar, VMCAI 2013) is
the closest thing and it is close. It is explicitly *"an architecture that allows
opportunistic use of whatever is out there… and should deliver evidence"*, operating as a
distributed Datalog framework over claims, rules and evidence, aimed at assembling
*"the ingredients for a safety or assurance case"*.

**What ETB deliberately does not do** — and this is from its own slides, not a strawman:
its notion of evidence is intentionally permissive. *"Could be proof objects… Could be
reputation ('Proved by PVS')… Could be diversity… Could be declaration by user ('Because I
say so')."* ETB is a **bus and an evidence ledger**. It does not claim an algebra in which
guarantees accumulate by *proved laws*, and it does not compute a trusted base with
theorems that the omissions are earned.

**Assurance cases with bounded results** (Springer 2016, *On Using Results of Code-Level
Bounded Model Checking in Assurance Cases*) addresses the bounded-guarantee problem
directly — and answers it with **confidence arguments**: complement the incomplete result
with classical testing and argue confidence. That is a qualitative answer to a question
that has an algebraic one.

**Assume-guarantee compositional verification** decomposes *one* property across
components. Different object: this repo accumulates *different* properties from *different*
tools over one artifact.

**De Bruijn criterion** — separate proof generation from proof checking — is the principle
the ledger work sits inside, not a competitor.

### The gap, stated so it can be attacked

Nobody has a **machine-checked algebra** in which

1. heterogeneous per-artifact certificates from different tools accumulate by **proved
   laws** (not by a Datalog script's say-so),
2. the trusted base is **computed from the artifacts** with theorems that omissions are
   earned, and
3. **bounded guarantees are first-class algebraic objects** — Alloy scope, CBMC unwinding,
   TLC instance bounds composing as *grades*, rather than being downgraded to "confidence"
   in an assurance argument.

(1) and (2) exist here already (`Bridge.pair_comp_cert`, `needs`, `cn_base_strictly_smaller`).
**(3) does not exist anywhere I can find.**

*Amended after stage E ran:* "and the estate is full of it" was **wrong**, and was written
before any tool was run. Kani's results here are unbounded, TLC's are exhaustive over a
finite instance, and Coq/Lean are proofs. **Alloy is the only genuinely bounded producer in
the estate** — two models. The claim in (3) stands; the claim that this estate is a rich
source of instances for it does not.

---

## 6. The superseded stage list (kept for the stage E record)

Same discipline as `PLAN-2026-08.md`: every stage has a falsifiable milestone and a kill
criterion. Stage letters continue from D.

### Stage E — The emission census, for eight tools. *(1–2 sessions. Do this first.)*

Stage D's method, generalised: for each tool, **what does it actually emit**, and is it a
statement of what was established or something else? Answered by looking, not assuming —
CN's JSON turned out to be a timing log.

Per tool, record: emission format; is it consumable; guarantee shape (unbounded / bounded /
axiom-carrying); and what its trusted base is. Known starting points: Coq `Print
Assumptions` and Lean `#print axioms` are **real machine-readable trusted-base emissions**;
Kani/CBMC emits structured results with its bounds; Alloy's scope is in the `check`
statement itself.

- **Milestone:** `corpus/estate/EMISSION.md` — eight rows with evidence, in the style of
  `corpus/jasmin/EMISSION.md`, including the tools that emit nothing usable.
- **Kill criterion:** if fewer than three tools emit consumable artifacts, the multi-tool
  pipeline is a manual encoding exercise at eight times the cost, and stages F–H should be
  rescoped to the tools that do emit.
- **Done** (`conf-typing/corpus/estate/EMISSION.md`, real bytes in `captures/`). Every row was
  produced by **running the tool on the estate's own artifacts**, not by reading docs.
  **Six of eight emit something consumable — the criterion did not fire.**
  - **Coq and Lean are the best reception targets in the estate**, and that was a surprise.
    `Print Assumptions` / `#print axioms` emit *exactly* the object `Ledger`/`needs` is
    about, per theorem, already computed. "Does not depend on any axioms" is
    `condBoundary_nil` in the tool's own output.
  - **Kani: the `unwind(N)` annotation is not the bound.** It is a search parameter; the
    epistemic status is a separate check (`.unwind.N`), and with unwinding assertions on —
    the default — an insufficient bound makes verification **FAIL** rather than silently
    return a bounded result. Both cases were run. **The estate disables unwinding checks
    nowhere, so all 124 of its harnesses carry *unbounded* guarantees** and stage F's bound
    gap does not touch them. The naive reading is wrong here.
  - **Alloy is the genuinely bounded one, and its certificate is split across two files**:
    the verdict on stdout, the scope in `receipt.json`. Neither half is a certificate alone,
    and **the estate's own wrapper discards both**, reducing the run to a boolean. That is
    the seam stage H would have to change.
  - **TLC** is exhaustive over a finite instance (`0 states left on queue`) and emits a
    **numeric** soundness caveat — the probability a state was skipped through a fingerprint
    collision. **`Ledger = List Prop` has nowhere to put a probability.** New gap, found by
    running.
  - **Verus** was not assessed: not on `PATH` in this environment. Recorded as unassessed
    rather than guessed.

### Stage F — Bounded guarantees as grades. *(3–5 sessions. The novel one.)*

Make "verified up to bound *b*" a first-class object in the algebra. `check … for 4
AbacPolicy` and a Kani unwind bound and a TLC finite instance are all the same shape: **a
guarantee quantified by a budget**.

The question the algebra must answer: given *f* safe to scope 4 and *g* safe to scope 7,
what is the composite? The tempting answer is `min`. **The tempting answer is probably
wrong**, and that is the content: a counterexample to the *composite* may require more
atoms than a counterexample to either part, so `min` is necessary but not obviously
sufficient.

- **Milestone:** either (i) a `GradedAction` for bounded guarantees with a proved
  composition law and a **condition** under which it is sound, plus a counterexample showing
  it fails without that condition; or (ii) a counterexample showing bounded guarantees do
  **not** compose at all, which retires the naive reading and is equally publishable.
- **Non-vacuity requirement:** the witness must be drawn from `alloy/CapabilityDelegation.als`,
  whose comments already reason about scope adequacy and vacuity (*"scope 5 made this
  vacuously true"*) — real scopes, not invented ones.
- **Kill criterion:** if bounded composition turns out to be exactly `min` with no side
  condition and no interesting failure, this is a definition rather than a theorem. Say so
  in one paragraph and fold it into stage E.
- **Done, first pass** (`conf-typing/ConfTyping/BoundedCert.lean`). **The kill criterion did
  not fire, and the outcome is stronger than milestone (i).**
  - **`min` is unsound, and totally.** `min_unsound`: `f x = x + 20`, `g` well-behaved only
    below 10. Both parts correctly certified; the rule claims the composite safe below 11;
    **the composite fails at every input, including 0.** No bound exists for which it is
    safe. Neither certificate is wrong — the rule that combined them discarded the growth.
  - **The grade is the pair `(bound, growth)`**, composing as
    `bmul ⟨b₂,g₂⟩ ⟨b₁,g₁⟩ = ⟨min b₁ (b₂ - g₁), g₁ + g₂⟩`. Sound (`bounded_comp_sound`) with
    **no side condition**, because the bound is stored strictly so the vacuous certificate
    is `0` and truncated subtraction lands on it. Associative (`bmul_assoc`), and **tight**
    (`bounded_comp_tight`) — safe below 8, broken at 8.
  - **The unexpected result: `bounded_grade_does_not_factor`.** The composite bound is not a
    function of the two bounds; it reads the inner growth. So a bounded certificate **cannot
    be presented as a product of independent components**, and `Bridge.pair_comp_cert`'s
    free componentwise composition does not cover it. Stage 1j found two properties that
    cannot be independently *derived* while bundling stayed free; **this is the first grade
    whose composition is itself coupled** — a real limit on the repo's central claim, found
    by the first example not built to fit it.
  - Method note: `min`'s unsoundness, the corrected law's soundness (1 803 random claims
    against brute-force semantics) and its associativity (42 875 triples) were all
    established by exhaustive search *before* anything was proved in Lean.
- **Second pass, not done.** `GrowsBy` is a **constant** growth bound. Input-dependent
  growth needs the grade to carry a monotone map — `universalGA`'s `Mono`, already in
  `TransportCalculus`. And nothing is yet transcribed from Alloy or CBMC: connecting this to
  real emitted bounds is stage E's job.

### Stage G — The cross-tool discharge, formalised. *(3–5 sessions. The highest-value one.)*

Formalise `MERKLE-CODEC-1`. Kani's K141 (bounded, exhaustive over all 256 byte values) and
K142 (length invariant) are certificates; the Verus axiom is a ledger entry; the step
between them is currently the English phrase *"by byte-independence"*.

Make that step a theorem, or find out it cannot be one.

- **Milestone:** a machine-checked statement of the form *"K141 ∧ K142, plus an explicit
  byte-independence lemma, discharge `MERKLE-CODEC-1`"*, with the ledger of every Verus
  kernel that depended on it shrinking accordingly — `condBoundary_discharge_head`, applied
  across a tool boundary for the first time.
- **Kill criterion, and it is the interesting outcome:** if the byte-independence step
  requires an argument **neither tool's output supports**, then the registry's "partially
  discharged" is an overclaim, and the honest result is a new irreducible trust entry plus a
  correction to `ASSUMPTION_REGISTRY.md`. **That outcome is a finding about a production
  trust boundary and is worth more than the positive one.**

### Stage H — The estate ledger. *(5–8 sessions.)*

`certcompose`, generalised from one tool to the estate: for a named end-to-end property of
sentinel, emit the composite guarantee and the **computed** trusted base across every
contributing tool, re-checkable by a third party, with the Lean proof object behind it.

- **Milestone:** one real end-to-end property whose computed base is **strictly smaller**
  than the union of all 17 allowlist entries plus every tool's fixed base — the
  `pureProg_deployed_with_nothing` result at estate scale.
- **Kill criterion:** if the computed base for every real end-to-end property equals the
  union of everything, then "computed rather than fixed" buys nothing at this scale, and the
  contribution is the bounded-composition algebra (stage F) alone.

---

## 4. Repository boundaries

Keep them separate, for the same reason stages B–D kept CN and Jasmin at arm's length:

- **`certified-composition`** stays the algebra and the receivers. It grows a
  `corpus/estate/` and receiver modules. It does not vendor sentinel's proofs.
- **`sentinel/formal`** stays the artifact estate and the source of truth for its own
  assumptions. It is not restructured to suit the algebra.
- The bridge is **emission consumption**, exactly as `certcompose` consumes
  `accept.expected`. If the algebra needs sentinel to change to be applicable, that is
  evidence against the algebra, not against sentinel.

---

## 5. What this plan does not claim

- It does not claim ETB is superseded. ETB is a bus and this is not a bus; if the two ever
  met, this would be a *cargo type* for that bus.
- It does not claim eight tools will be integrated. Stage E may show that most emit nothing
  consumable, and the plan is built to survive that.
- It does not claim the bounded-composition law exists. Stage F's milestone explicitly
  admits the negative outcome as a result.
- It does not claim any of this verifies sentinel. Every receiver is a hand encoding
  unchecked against its tool, as `CNReceive.lean` has said since stage B, and no stage here
  changes that.
- It does not claim novelty for graded monads, assurance cases, or compositional
  verification as such. The claim is narrow: **bounded guarantees as grades, with a computed
  trusted base, machine-checked.**

---

## Sources

- J. Rushby. *An Evidential Tool Bus.* ICFEM 2005; slides, VSTTE 2005.
  <https://www.csl.sri.com/users/rushby/slides/vstte05.pdf>
- S. Cruanes, G. Hamon, S. Owre, N. Shankar. *Tool Integration with the Evidential Tool
  Bus.* VMCAI 2013. <https://link.springer.com/chapter/10.1007/978-3-642-35873-9_18>
- *On Using Results of Code-Level Bounded Model Checking in Assurance Cases.* SAFECOMP
  workshops 2016. <https://link.springer.com/chapter/10.1007/978-3-319-45480-1_3>
- Local estate, measured 2026-08-14: `/home/paolo/.vella-workspace/sentinel/formal`
  (`ASSUMPTION_REGISTRY.md`, `trusted-assumptions.allowlist`, `verus/assumptions.rs`,
  `kani/src/merkle_codec.rs`, `alloy/CapabilityDelegation.als`, `tools/check-*.sh`).
