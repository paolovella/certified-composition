# Language design precedents for a security-certified language + compiler

(Intended path: .../scratchpad/research_notes/Secure compiler planning/language_design_precedents.md.
Plan mode allowed writing only this file.)

Date: 2026-10-23. Tags: [V] = checked against the primary source this session; [R] = from recall of the
primary source, not re-fetched; check before quoting.

## 0. Thesis

The languages that were adopted (SPARK, Jasmin, Rust) share one recipe:
(a) **remove the hard thing from the language** instead of proving it (no aliasing, no general pointers, no
secret branches, no GC);
(b) make the default property cheap and automatic (flow analysis / type checking), and leave expensive proof
opt-in and graduated;
(c) certificates are **per-procedure contracts**, checked modularly;
(d) when the tool cannot prove something it says so with a precise, local message, and suppression is an
explicit, auditable justification.
The languages that failed (Jif, FlowCaml) put a general lattice-label type system on a general-purpose
language with exceptions, objects and the heap, and showed the cost of that generality to every programmer on
every line.

## 1. Precedents

### SPARK / GNATprove
- Levels [V, SPARK UG section 8.1 "Levels of SPARK Use"]:
  - **Stone**: valid SPARK subset.
  - **Bronze**: flow analysis. No reads of uninitialized data, no unintended global access, no
    parameter/global aliasing.
  - **Silver**: proof of absence of run-time errors (AoRTE).
  - **Gold**: key integrity properties, via predicates and pre/postconditions.
  - **Platinum**: full functional correctness, which the guide says is "rare" and done on small parts of an
    application.
  - The UG warns that Bronze flow analysis "may require a substantial effort to deal with the false alarms",
    because it has "no knowledge of values (only code paths)". At Silver, "precise types and simple contracts"
    avoid most false alarms, and the rest are justified with pragmas.
  - https://docs.adacore.com/spark2014-docs/html/ug/en/usage_scenarios.html
- Info flow:
  - `Global` (which state each subprogram reads or writes) and `Depends` (output <- inputs) contracts are
    checked by flow analysis, not proof [R].
  - This is a dependency relation, not a lattice-label noninterference type system. There is no first-class
    declassification. Users write the policy as a `Depends` contract per subprogram.
  - Lesson: a *dependency contract on the interface* is writable. A label on every variable is not.
- Integers [V, UG section 5.7]:
  - Every arithmetic operation produces an overflow verification condition (VC).
  - Overflow modes are STRICT (base type), MINIMIZED (wider type) and ELIMINATED (arbitrary precision).
    General code and assertions can be set separately; `-gnato13` gives STRICT for code and ELIMINATED for
    assertions.
  - A Big_Integers library is used for mathematical specifications.
  - Range subtypes (`type Index is range 1..N`) do most of the work: the bounds become free hypotheses for the
    provers.
  - Lesson: fixed-width machine integers in code, unbounded integers in specs, and range types to carry
    bounds.
- Pointers:
  - Forbidden until about 2019. They were then added with Rust-style ownership: move, plus "observers" and
    "borrowers" (shared and mutable borrows), enforcing Concurrent-Read-Exclusive-Write [V, Jaloyan-Moy-Paskevich
    arXiv 1805.05576; AdaCore blog Oct 2019 "Pointer-based data structures in SPARK"].
  - Cyclic structures are not supported: no doubly-linked lists.
  - The paper reports that idiomatic Ada needed only minor changes.
  - Lesson: ownership was retrofittable *because* SPARK already banned aliasing.
- Compiler trust [R]:
  - GNATprove proves the source. The GNAT compiler is trusted, qualified under DO-178C/ISO 26262 processes,
    not verified.
  - Proof lets run-time checks be removed. NVIDIA reported generated assembly "nearly identical" to C
    [V, devclass 2022 summary of the AdaCore/NVIDIA case study].
  - Gap for us: the certificate does not survive compilation in any formal sense.
- Industry:
  - NVIDIA moved security-critical firmware from C/C++ to SPARK. The motivation was too few security experts
    and too many firmware attacks
    [V, https://www.adacore.com/case-studies/nvidia-adoption-of-spark-new-era-in-security-critical-software-development].
  - At DEF CON 29, an attack on SPARK firmware went through the RISC-V ISA via glitching, below the language
    level [V, AdaCore blog "When the ISA is the weakest link"].
  - Earlier: Tokeneer (NSA), iFACTS (NATS), C130J. King et al., "Is Proof More Cost-Effective Than Testing?",
    IEEE TSE 2000 [R].

### Jasmin
- Design [V, Almeida et al., CCS 2017 "Jasmin: High-Assurance and High-Speed Cryptography"]:
  - The programmer controls instruction selection and (mostly) register vs stack placement (`reg`/`stack`).
  - Arrays have static sizes. Memory is accessed only through `[ptr + off]` on externally provided regions.
    There is no allocation and no general heap.
  - The compiler is verified in Coq. Some passes are proved, others are translation-validated (register
    allocation).
- CT and cost preservation [V, Barthe-Grégoire-Laporte-Priya, CCS 2021, ePrint 2021/650]:
  - "Structured leakage" proves that the Jasmin compiler **preserves both cryptographic constant-time and
    cost**.
  - This is the closest existing precedent for carrying a CT and bounded-cost certificate through compilation.
- Spectre [V, Shivakumar et al., S&P 2023, ePrint 2022/1270; docs at jasmin-lang.readthedocs.io/en/latest/tools/sct.html]:
  - Security types are `#public`, `#secret` and `#transient` (public architecturally, possibly secret under
    speculation).
  - A misspeculation flag (MSF) is managed with `init_msf` (lfence), `update_msf` (cmov) and `protect`
    (mask with msf).
  - `#declassify` gives `transient`, which must be `protect`ed before it becomes public. `#nomodmsf` marks
    functions that leave the MSF alone.
  - Overhead is under 1% for Kyber and about 0 for X25519. Extended to all Spectre classes in ePrint
    2024/1070, with under 2% overhead for most primitives and 5-7% for Kyber.
  - POPL 2025 work (hal-04663857) shows that speculative CT is *not* preserved by GCC/Jasmin in practice, and
    gives a Coq-verified proof-of-concept compiler.
  - Lesson: *the leakage model is part of the language spec and has to be versioned.*

### FaCT (Cauligi et al., PLDI 2019) [V, paper PDF]
- Secrecy type system. The compiler automatically rewrites secret `if`, early `return` and `break` into
  straight-line code (ctselect/masking).
- It has `declassify(e)` and `assume(e)`. Arrays with `len`, `view` and `zeros` replace pointer arithmetic.
- **Public safety**:
  - Naive CT transformation can introduce memory errors or undefined behaviour, because a branch that was
    guarded is now executed.
  - So the program must be memory-safe and UB-free using only public path conditions.
  - Division needs `e2 != 0`, and shifts need `0 <= e2 < width`.
  - => **Secret-guarded safety conditions are not allowed.** This is a direct lesson for overflow and abort
    semantics.
- **Trust gap**:
  - Only *unoptimized* output is formally CT. It is 16-346% slower than C.
  - clang -O output is 5% slower to 21% faster than C, but it is checked only *empirically* with dudect.
  - Lesson: compiling through an unverified optimizer such as LLVM breaks the certificate chain.
    Choose a verified backend (Jasmin, CompCert-style) or translation validation of the CT property.
- User study:
  - 77 of 129 students. 57% found FaCT easier than C and 15% found C easier.
  - Comprehension scores: 57% vs 53% on one function, and 40% vs 32% on the other.

### Low* / Vale / HACL* / EverCrypt [R]
- Low* (Protzenko et al., ICFP 2017 "Verified Low-Level Programming Embedded in F*"):
  - A shallowly embedded C-like subset of F*, with regions/stack via the HyperStack memory model and
    explicit `push_frame`/`pop_frame`. KaRaMeL extracts it to C.
  - Secret integers are an abstract type with no comparison or branch operations, which gives CT by typing
    (HACL*, CCS 2017).
  - Lesson: **CT by abstract secret-integer types with a restricted operator set** is very cheap to use.
- Vale (Bond et al., USENIX Security 2017): verified assembly with a taint-based CT/leakage analysis.
- Trust: KaRaMeL and the C compiler are trusted. This is the same gap as FaCT.

### Cogent [R] (O'Connor et al., ICFP 2016 / JFP; Amani et al., ASPLOS 2016)
- Linear types, no GC. The certifying compiler emits C *plus* an Isabelle proof that the C refines a purely
  functional semantics.
- Unsafe or recursive parts go in C via an FFI that carries proof obligations.
- Lesson: **certifying compilation (per-run proof) instead of verifying the compiler.** Linearity makes the
  semantics pure, so equational proofs are possible.

### Checked C / CHERI-C [R]
- Checked C (Elliott et al., SecDev 2018; Ruef et al., POST 2019 "Achieving Safety Incrementally with Checked
  C"):
  - Checked pointer types (`_Ptr`, `_Array_ptr` with bounds) and checked regions.
  - Its blame theorem: a failure is attributable to unchecked code.
- CHERI: hardware capabilities give spatial safety (and temporal safety with revocation) without changing the
  source.
- Lessons: incremental adoption plus a blame theorem is the model for FFI. Hardware capabilities are a
  *defence in depth* target, not the primary mechanism.

### Rust safe subset [R]
- Ownership and borrowing are the memory model. Soundness depends on `unsafe` blocks being correct, which
  RustBelt proves for key libraries (Jung et al., POPL 2018).
- Governance:
  - Editions (RFC 2052) allow breaking surface syntax but keep crates interoperable across editions.
  - Stability guarantee (RFC 1122 permits breakage *for soundness fixes*).
  - The `I-unsound` label tracks known soundness holes publicly. Some are long-lived, e.g. #25860 (implied
    bounds, open since 2015, exploited by cve-rs).
  - Lesson: soundness bugs *will* exist. Track them publicly, make soundness fixes the one allowed breaking
    change, and version the certificate format.

### Austral, Pony, Wyvern, E, Joe-E [R]
- Austral (F. Borretti): linear types plus capability-based security. Authority to do I/O is a linear value
  passed down from `main`. Its spec explicitly prioritises a simple, fits-in-head language.
- Pony (Clebsch et al., AGERE 2015 "Deny Capabilities for Safe, Fast Actors"): reference capabilities
  (iso/val/ref/box/trn/tag) give data-race freedom. Pony also has an object-capability ambient-authority ban
  (`AmbientAuth`).
- Wyvern (Melicher et al., ECOOP 2017 "A Capability-Based Module System for Authority Control"):
  - Resource modules vs pure modules. Authority is visible in module types, so it can be checked from
    signatures.
  - Wyvern also has TSLs, type-specific languages for safe embedded syntax such as SQL/HTML.
- Joe-E (Mettler, Wagner, Close, NDSS 2010): a Java subset with no ambient authority and no mutable statics.
  It enables reasoning "this method can only affect what it was passed".
- E (Miller 2006, thesis "Robust Composition").
- Lesson for complete mediation:
  - With no ambient authority, every effect needs a capability argument, so the call graph *is* the mediation
    graph.
  - "Complete mediation" then becomes: every capability for resource R is minted only by the reference
    monitor M. This is checkable by type, not by whole-program analysis.

### Hacspec [R] (Merigoux, Kiefer, Bhargavan 2021, "hacspec: succinct, executable, verifiable specifications
for high-assurance cryptography embedded in Rust")
- A Rust subset for executable specs, with secret-integer types. Translated to F*/Coq/EasyCrypt (now hax).
- Lesson: **specs written in a subset of the implementation language** cut the "spec language" learning cost.

### Jif / FlowCaml (the failure mode)
- Jif (Myers, POPL 1999; Jif 3.x):
  - Decentralized labels on every type, principals, `declassify`/`endorse`.
  - Exceptions (including NullPointerException) are implicit flows, so programmers must catch or prove away
    run-time exceptions everywhere.
- Usability evidence is thin and mostly qualitative:
  - JPmail (Hicks et al., PLAS 2006 "Trusted declassification"/"Implementing a secure email client") [R].
  - Jifclipse (Hicks et al., PLAS 2007), built *because* label errors were hard to diagnose [R].
  - An archived proposal (cps-vo node 34142) states plainly that IFC "has failed to achieve traction among
    developers" because of lattices and implicit-flow scrubbing [V, search hit].
- **No rigorous measured false-positive or annotation rate for Jif was found.** Do not cite numbers.
- FlowCaml (Simonet 2003): full inference of labels, but inferred constraint types were unreadable, and there
  was no clean story for the effects/exceptions channel [R].
- CT tool usability: Fourné et al., USENIX Security 2024 ("These results must be false") [V].
  - 24 participants, 6 tools. Every tool had usability issues.
  - Recommendations: clear output that maps to violations, minimal invasive markup, easy install, and
    examples.
  - Jancar et al., S&P 2022 (survey of crypto library developers) found the tools are rarely used [R].

## 2. Cross-cutting design lessons (actionable)

### L1. Memory model
- Prefer, in order:
  - (i) **no heap**: static arrays plus externally provided buffers (Jasmin);
  - (ii) arenas/regions with lexical lifetimes (Low* frames);
  - (iii) affine ownership plus borrows (SPARK 2019+, Rust);
  - (iv) linear values (Cogent, Austral).
- Use indices into typed arenas instead of raw pointers wherever possible. Bounds become range types (SPARK)
  and proofs stay arithmetic.
- NI interaction:
  - If allocation size or count depends on a secret, the address/allocator state is a channel. The free list
    and reuse order leak allocation history.
  - Rule: **allocation (size, count, order) must be typed public** (FaCT's public-safety discipline extended to
    allocation). Fresh memory must be zeroed: the `zeros` primitive in FaCT.
  - Addresses must be opaque. No pointer-to-int casts, no address comparison or ordering on handles.
- Ban cycles (SPARK) or provide arenas for them. Do not add GC, since GC timing is a secret-dependent channel.

### L2. Integers
- Fixed-width integers in code. Unbounded `Big` integers only in specs/ghost code (SPARK `-gnato13` model).
- Default `+` is **checked statically**: an overflow VC proved at compile time (SPARK Silver), with a range
  type carrying the bounds. Explicit `wrapping_add` and `sat_add` are separate operators (Rust naming).
- **No dynamic trap on secret operands.** A trap is a termination/timing channel. FaCT forbids safety
  conditions that depend on secrets.
  - Rule: an operation on secret operands must be either total (wrapping/saturating) or have its overflow VC
    discharged *statically*.
  - The type checker rejects a runtime-checked op whose operands are secret.
- Division, modulo and variable shifts are variable-time on many CPUs, so a secret divisor is a CT violation
  (KyberSlash 2023/24 [R], kyberslash.cr.yp.to).
  - Make the secret-integer type expose only a CT operator set (HACL* secret ints): no `/`, `%`, `==`→bool
    branch, or table lookup by secret.

### L3. Control flow and CT
- Two viable choices:
  - (a) **reject** secret branches, loops and indices (Jasmin, HACL*): simple, and the user writes masking;
  - (b) **auto-transform** secret `if`/`return` into selects (FaCT): writable, but requires public safety.
- Recommendation: (b) for `if`/early return/`break`, and (a) for secret loop bounds and secret indices.
- The leakage model (which instructions are variable-time; whether speculation is in scope) is a **versioned
  part of the language spec**. Jasmin needed new types (`transient`) and primitives when Spectre was
  admitted.

### L4. Carrying certificates through compilation
- FaCT through LLVM lost the formal CT guarantee at -O. GNAT is trusted, not verified.
- Viable models:
  - (i) verified compiler with a leakage-preservation theorem (Jasmin: CT plus cost, CCS 2021);
  - (ii) certifying compiler that emits a per-run proof (Cogent);
  - (iii) translation validation of the property on the output (Jasmin regalloc; binary CT checkers).
- Cost/WCET: Jasmin's cost-preservation result is the existing precedent. Require loops with
  public, statically bounded trip counts (or variant plus bound), and no recursion or bounded recursion.

### L5. Modularity = contracts as certificates
- Every exported procedure carries its certificate in its signature:
  - `Global`/`Depends` (flow), pre/post (safety), security types (CT), capabilities (authority), cost bound.
- Callers rely only on the contract, as in SPARK modular proof and Jasmin `export` signatures.
- Separate compilation checks contract-against-body once and contract-against-use at link time.
- Bodies get **inference by default** (SPARK generates `Global`/`Depends` when absent). Contracts are
  mandatory only at the module or export boundary. This is the key anti-Jif move.

### L6. FFI / linking
- Treat C as an attacker: robust compilation (Abate et al., CSF 2019 "Journey Beyond Full Abstraction";
  Patrignani-Ahmed-Clarke survey, CSUR 2019) [R].
- FFI imports carry *trusted* contracts that are logged as assumptions in the certificate, with Checked C's
  blame theorem as the model.
- Exported entry points defensively assume the worst. Jasmin assumes misspeculation on entry to `export`
  functions [V].
- Runtime-validate every value crossing the boundary into a refined type (validate-at-the-boundary, as in
  EverParse) [R].

### L7. Authority / complete mediation
- Object-capability discipline, with **no ambient authority** (Joe-E, Wyvern, Austral, Pony):
  - no globals with effects;
  - I/O only through capability values;
  - capabilities are linear or affine where revocation or single-use matters.
- Mediation theorem shape: "every operation on resource R takes a `Cap<R>`, and `Cap<R>` is constructible only
  inside module M". This is a type-abstraction property, checkable separately. Wyvern puts authority in module
  types.

### L8. Errors / abort
- Abort is observable (termination channel). Under termination-insensitive NI (TINI), a secret-dependent abort
  leaks one bit per run (more with repetition).
- Rule: abort may only depend on public data; secret-dependent failure is returned as a value
  (`Result` with a secret tag, CT-selected).
- No exceptions. Jif's exception channel is a large part of its annotation burden, and SPARK forbids
  propagating exceptions in proved code [R].

### L9. I/O, strings, injection
- Output is typed by context:
  - Google safe types (`SafeHtml`, `SafeUrl`, `TrustedResourceUrl`): constructible only via escapers or
    builders (Kern, CACM 2014 "Securing the Tangled Web") [R].
  - W3C Trusted Types: sinks accept only typed values [R].
  - Context-sensitive auto-escaping in templates (Samuel, Saxena, Song, CCS 2011) [R].
  - Wyvern TSLs [R].
- "Injection-free" then becomes a typing theorem: sinks take only context-typed values, and constructors are
  the escapers.
- The same type-abstraction pattern as L7.

### L10. Declassification
- Explicit, syntactically scoped, and audited: Sabelfeld-Sands "Declassification: Dimensions and Principles",
  JCS 2009, covers the what/who/where/when dimensions [R].
- Restrict *where* declassification can appear: only in modules marked as trusted declassifiers, or
  policy-named (JPmail "trusted declassification" [R]).
- Jasmin/FaCT show a minimal `declassify(e)` is enough for crypto (e.g. revealing a MAC check result).
- The certificate must list every declassification site, because an auditor reviews that list.

### L11. Writability (anti-Jif)
- **Label only the boundary**: function signatures and `secret` on inputs. Infer everything inside.
- **Two-level lattice** (public/secret), plus `transient` only if Spectre is in scope. No general DLM.
- Error messages must point at the flow path (Fourné et al. recommendation; Jifclipse existed for this
  reason).
- **Graduated levels** à la Stone→Platinum, so teams adopt incrementally and get value at Bronze.
- **Justification mechanism**: a named, reviewed suppression that is recorded in the certificate as an
  assumption, never silent.
- Remove the false-positive sources by construction: no aliasing, no exceptions, no secret-dependent
  safety checks. Do not try to analyse them away.

### L12. Evolution / governance
- Version the language, the leakage model and the certificate format separately. Use editions (Rust) for
  surface changes.
- Soundness fixes may break code. Keep a public soundness-bug tracker (Rust `I-unsound`), and certificates
  name the checker version so revocation is possible.
- Grow by lifting restrictions: SPARK added pointers 25 years in, only once an ownership model existed that
  kept the existing proofs. Start small and restrictive.

## 3. Gaps (not verified this session)
- Exact Jif/FlowCaml annotation or false-positive rates: none found. They are probably unmeasured.
- The SPARK release that first shipped pointers (thought to be SPARK Pro 19 / GNAT Community 2019).
- Measured SPARK Silver "proved automatically" percentages: AdaCore case studies exist, but their numbers
  were not fetched.
