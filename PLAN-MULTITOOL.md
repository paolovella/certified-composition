# The eight-tool estate, and the one thing that would be a breakthrough

*Written 2026-08-14, after `PLAN-2026-08.md` stages A–D closed.*

## 0. The concern, stated first

**"Use all the tools" is the wrong objective function, and adopting it would repeat the
mistake stage A was written to stop.** Eight shallow receptions — one `GradedAction` per
tool, eight hand encodings, a README table with eight rows — would be *less* valuable than
one machine-checked cross-tool discharge theorem, and would look like more. The repo has
already measured what happens when breadth is chosen over evidence: 25 author-written
programs found nothing, and twelve transcribed ones found the real defect immediately.

The plan below is therefore organised around **the discharge relation between tools**, not
around tool count. Tools enter the plan when they carry weight in a specific theorem, and
`Stage E` exists to find out which ones can.

That said — the instinct behind the request is right, and better than it may look. The
estate is real, and it contains the artifact this repo has been missing.

---

## 1. What is actually there

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

## 2. The prior art, honestly

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

## 3. The plan

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
