# Secure compilation theory: notes for a certificate-carrying compiler

(Plan mode was active, so these notes are here instead of at the requested scratchpad path
`/tmp/claude-1000/-home-paolo-certified-composition/cbe1e5c5-1c8d-4aa0-b648-aecd0fe50c94/scratchpad/research_notes/Secure compiler planning/secure_compilation_theory.md`.
Copy this file there once plan mode is off.)

Date: 2026-10-23. Tags: [V] means checked against a primary source in this session. [K] means background knowledge, cited but not re-read this session.

---

## 0. Framework: the preservation criteria and which property needs which

### 0.1 The lattice (Abate et al., CSF 2019 [V]; Patrignani, Ahmed, Clarke, ACM CSUR 2019 [K])
- **Plain (non-robust) preservation.** Whole program, no adversarial context.
  - TP: trace properties. Implied by backward simulation / refinement, tgt behaviours ⊆ src behaviours. This is CompCert's main theorem.
  - SP: safety. Implied by refinement of finite prefixes.
  - HP: hyperproperties, e.g. NI and constant-time (CT). **Refinement does NOT give this.** A refined target can choose a *different* src behaviour per secret, which is the refinement paradox. For **deterministic** src and tgt, plus "tgt behaviour = f(src behaviour)" for a fixed *public-only* f, 2-safety *is* preserved. That is the leakage-transformer idea. In CompCert, determinism of src plus forward simulation turns into behaviour equality, but only for the *functional* trace, not the leakage.
  - 2HP / 2SP / 2rSP: relational, i.e. k-safety or k-hypersafety.
- **Robust variants (R·P).** "For every target context C_T there exists a source context C_S such that…" (back-translation). These quantify over linked adversarial code or an FFI.
  - RTP ⇔ RTC; RSP ⇔ RSC (robustly safe compilation, Patrignani & Garg ESOP 2019 [K]).
  - RHP: robust hyperproperty preservation. It is ⇔ a property-free criterion where one source context C_S must simulate C_T for *all* programs at once.
  - RrHP: robust relational hyperproperty preservation. It is the strongest, and is strictly stronger than full abstraction in the order. Full abstraction (FA) is *incomparable* with most of the robust criteria. **FA does not imply RSP**, so FA by itself does not guarantee robust safety.
  - Collapse/separation: RHP > R2HP > … ; RSP is much cheaper to prove than RHP because it uses a per-trace-prefix back-translation.
- **Trace-relating compiler correctness** (Abate, Blanco, Ciobâcă, Durier, Garg, Hriţcu, Patrignani, Tanter, Thibault, ESOP 2020, arXiv 1907.05320 [V-listing]). It generalises CC to *different* src/tgt trace alphabets via a relation ~. You get "τ̃-preservation" of src properties as transported properties. **Use this to state precisely how fuel exhaustion, UB, or overflow on the source side maps to traps or divergence on the target.**
- **Composition** (Kruse, Backes, Patrignani, arXiv 2307.08681 [V-listing]). Composing a pass that preserves P1 with one that preserves P2 does not automatically preserve P1∧P2. The paper gives "upper/lower composition" conditions and builds a multi-pass compiler preserving memory safety plus CT. This matches the repo finding that minimality composes across different tools but not for the same tool twice.

### 0.2 Which criterion each of the 9 classes needs

| # | Property | Class | Whole-program criterion | Adds if FFI/linked attacker |
|---|---|---|---|---|
|1| TS-NI over store | 2-hyperproperty. Termination-sensitive NI is **not** 2-safety: divergence vs termination is a liveness-flavoured hyperproperty. TINI is 2-safety. | HP-preservation for deterministic langs = "src-NI ⇒ tgt-NI" via 2-simulation / indistinguishability simulation | RHP (or R2HP). Needs back-translation of contexts, and target memory must be isolated (SECOMP-style). |
|2| CT (PC+addr trace) | 2-safety over leakage traces | Leakage-transformer simulation (CT-simulation) | R2SP. The attacker sees the leakage of the whole program, so the context must be CT too, or be isolated. |
|3| SCT (Spectre v1, v4, RSB) | 2-safety over *speculative* semantics; Rosemann et al. note it is a 4-trace property in some formulations | SCT-preservation needs a speculative semantics at every IR level, or at least a proof that the target speculative semantics refines the src one | Contract-aware (Guarnieri & Patrignani, arXiv 2012.14205 [V]); robust speculative NI (Patrignani & Guarnieri CCS 2021 [V]) |
|4| Memory safety | trace/safety property, if UAF/double-free/wild deref are made *observable failing events* (or stuck states) in the src semantics. Leak-freedom at exit is a property of the final state, which is safety at termination. | TP/SP via backward simulation, plus src semantics where unsafe = UB/stuck and is proved absent | **RSP is the real goal.** Memory safety only means something against linked code if the target enforces it (CHERI, compartments, SFI). SECOMP proves an RSP variant for compartmentalised CompCert to RISC-V (CCS 2024 [V]). |
|5| Complete mediation | trace safety property over events (`check(r)=deny` ⇒ no later `read(r)`) | SP. Needs authorisation checks and protected reads to be **trace events**, not internal steps, so CC preserves them. | RSP. The context can't forge or skip checks, so this needs capability or compartment isolation. |
|6| Injection-freedom of emitted strings | trace property over output events, a predicate on each emitted string | TP. Output events are preserved verbatim by CC. If the property is about *provenance* (taint), it becomes a hyperproperty and needs HP. | RTP |
|7| Bounded cost | quantitative trace property: "cost(trace) ≤ B" is safety | Cost-preserving simulation, i.e. a leakage transformer whose cost is ≤ k·src_cost + c (Jasmin structured leakage, CCS 2021 [V]; CompCert stack bounds, Carbonneaux et al. PLDI 2014 [V]; CakeML space, OOPSLA 2020 [V]) | Cost of context excluded or bounded per call |
|8| Concurrent NI | 2-hyperproperty under a scheduler; value-dependent classification | Concurrency-aware security-preserving refinement (Murray et al. CSF 2016 [K]; Sison & Murray ITP 2019 / JFP 2021 [V]) | Scheduler is part of the adversary. Need scheduler-independence, or fix the scheduler as part of the observation. |
|9| Declassification / bounded release | Hyperproperty relative to an escape-hatch set. Robust declassification is a 4-trace property (Cecchetti et al. 2017, as cited by Rosemann et al. [V]). | HP-preservation where the indistinguishability relation is "equal on public ∧ equal on released expressions". Same proof shape as NI, with leakage = declassified values allowed. | RHP / RrHP. **Mostly an open area.** No mechanised compiler for declassification policies turned up in the searches. |

**Key insight for planning.** 4, 5, 6 and 7 (as an upper bound) are *trace* properties. Standard CompCert-style backward simulation preserves them **if and only if** the relevant actions are visible trace events. 1, 2, 3, 8 and 9 are *hyperproperties* and need a security-specific simulation. With a *deterministic* source and target, all the hyperproperty cases can be reduced to the **leakage-transformer** discipline.

---

## 1. Proof techniques

### 1.1 Forward/lockstep simulation and why it isn't enough
CompCert gives forward simulation on a deterministic src; with a receptive and determinate target, that flips to backward simulation, which gives behaviour inclusion/equality [K]. It says nothing about events the semantics does not record: branch targets, addresses, timing, residue in registers or stack. The repo already knows the fix: **extend the observation (trace) with leakage**, then prove leakage-preservation.

### 1.2 CT-simulation (Barthe, Grégoire, Laporte, CSF 2018 [V]; ePrint 2017/1233)
- 2-simulation: two src runs in lockstep (they have equal leakage, and CT forces the same control flow), two tgt runs, and a src→tgt simulation on each. The obligation: when the src runs are related and take a step with equal leakage, the tgt runs produce equal leakage. They also need a **"manysteps" variant** where the number of tgt steps per src step depends only on public data.
- Passes covered: constant folding, CSE-like steps, register allocation, etc. Most passes only need the simpler sufficient condition "**leakage of tgt is a function of leakage of src**" (leakage transformer). That condition is enough when the src is deterministic.
- Coq mechanised.

### 1.3 CompCert-CT (Barthe, Blazy, Grégoire, Hutin, Laporte, Pichardie, Trieu, POPL 2020 [V]; ePrint 2019/926)
- A "mildly modified" CompCert that preserves CT; leakage = branch conditions + memory addresses.
- Main difficulties [K, consistent with the abstract]:
  1. CompCert's memory model gives pointers as (block, offset), so leaking addresses requires deterministic, public-only allocation.
  2. **Most passes use the cheap leakage-transformer condition. Only a few need full CT-simulation.** Rosemann et al. 2025 quote the authors calling the linearisation proof "not especially pleasant".
  3. Some optimisations were disabled or adapted.
- Lesson: **design every pass's simulation to emit an explicit leakage transformer from the start.**

### 1.4 Jasmin
- CCS 2017 (Almeida et al.) [K]: verified compiler + CT checker.
- **Structured leakage (Barthe, Grégoire, Laporte, Priya, CCS 2021 [V]; ePrint 2021/650).** Leakage is a *tree* that follows the program's syntax (seq/if/loop/call), not a flat list. Each pass ships a **leakage transformer** that maps src leakage trees to tgt leakage trees. CT and **cost** preservation both follow from that one artefact. *This is the most directly reusable design for the project.*
- **SCT preservation (Arranz Olmos, Barthe, Blatter, Grégoire, Laporte, POPL 2025 [V]; PACMPL 9:1293–1325; ePrint 2024/1203).** GCC -O0/-O1 and Jasmin had counterexamples: secure src, non-SCT tgt. They give a Coq proof-of-concept compiler that preserves SCT, and patch Jasmin's SCT checker.
- **Spectre-RSB / all known variants (Arranz Olmos et al., ASPLOS 2025 [V]; ePrint 2024/1070).** Value-dependent IF type system + a compiler transformation proved in Coq to preserve SCT; overhead below 2% (Kyber 5–7%).
- **Zeroization (TCHES 2024(1):375–397 [V]; ePrint 2023/1713).** Stack and register clearing on return, integrated into the verified compiler and its correctness proof. `Stack_zeroization` modules, now with a RISC-V variant. **This is the residue fix.**
- **Probabilistic countermeasures / masking (Barthe et al., ePrint 2026/2510, IEEE S&P'27 [V]).** A *deterministic* leakage-preservation relation that implies d-NI, d-SNI and CT preservation. Covers the value-probing model with glitches, Jasmin core pipeline plus optimising passes, in Rocq.

### 1.5 Hyperproperty simulations / NIFTY (Rosemann, Hack, Garg, OOPSLA 2025, PACMPL 9 OOPSLA2 art. 323 [V])
- Generalises CT-simulation to k-simulations with synchronisers `(syncStep, maxStall)` that guarantee eventual progress on all k lanes. This is a generalised Namjoshi-style ranking.
- **Indistinguishability simulation.** Assume src-NI, then prove only a *src→tgt* simulation annotated with **local leakage transformers** (per program point: `id`, `rm`, …). With no secret branches, adhering to a local transformer annotation ⇒ CT preserved. Per pass this is a 1-src/1-tgt proof, not 4 traces.
- **Global leakage transformers (Jasmin-style) cannot handle DCE**, even on public branches: DCE removes leakage at one program point and keeps it at another. Local transformers fix this.
- NIFTY: optimise inside secret branches; at the control-flow rejoin, check that the local leakage transformer sequences agree on both sides; if not, **roll back** to a fallback pass that has a global transformer. Instantiated for DCE, common-branch factorisation and linearisation, mechanised in Rocq.
- Caveat: the semantics stutters the terminal state, so the step function is total. Termination sensitivity has to be checked per model; it is not a headline result.

### 1.6 Residue / memory-probing (Besson, Dang, Jensen: PLAS 2018 "Securing compilation against memory probing"; CSF 2019 "Information-flow preservation in compiler optimisations", pp. 230–242 [V])
- Attacker model: at chosen observation points, the attacker may read *arbitrary memory and registers*. That is stronger than an I/O observer.
- An IFP (information-flow preserving) transformation means the tgt is no more vulnerable than the src.
- Compositional proof principle, plus **translation validation** that *detects and closes* leaks introduced by DSE and register allocation. Closing a leak means inserting erasure.
- The direct answer to "register/stack/temporary residue" and "slot collision": the observation must include the whole machine state at the observation points (call/return/syscall), *or* the compiler must zeroise.

### 1.7 Concurrency (Sison & Murray ITP 2019, LIPIcs 141:27 [V]; JFP 31 e18, 2021 [V]; Murray et al. CSF 2016 [K]; arXiv 2511.06862, 2025 [V-listing])
- Value-dependent, mixed-sensitivity shared memory with mutex sync. CSF 2016 gives a "compositional security-preserving refinement" with *coupling invariants* and a *pacing* requirement. Pacing: corresponding src and tgt steps must take the same number of tgt steps, unless that number is determined by public data. Without it the scheduler sees timing differences.
- ITP 2019 / JFP 2021: a **decomposition principle** that separates semantics preservation from security preservation, for a compiler to RISC-style asm, in Isabelle/HOL. This is the "CoCo" line (covern.org).
- 2025: generalised security-preserving refinement for interleaving systems with intransitive NI, arXiv 2511.06862. It is not a compiler paper.

### 1.8 Translation validation / certifying compilation
- Necula (PLDI 2000) translation validation [K]; Namjoshi & Tabajara, "Witnessing secure compilation", VMCAI 2020 (arXiv 1911.05866) [V-listing]. Per-run *witnesses* (refinement relations) for hyperproperties: the compiler emits a relational witness, and a small checker validates it.
- Cogent (O'Connor et al. ICFP 2016; Rizkallah et al. ITP 2016) [K]: a per-program certifying compiler that emits Isabelle refinement proofs down to C, then relies on seL4's C→binary validation (Sewell, Myreen, Klein PLDI 2013) [K].
- Besson et al. 2019 also use translation validation for IFP.
- For Lean: the cheapest strong option is **per-program validation**. The compiler emits the tgt *and* a leakage-transformer / simulation certificate, and a verified Lean checker validates them. This avoids proving every optimisation once and for all.

### 1.9 Product programs / relational Hoare logic transfer [K]
Barthe, D'Argenio, Rezk (CSFW 2004) self-composition; Barthe, Crespo, Kunz (FM 2011) product programs; certificate translation (Barthe, Grégoire, Kunz, Rezk). If src certificates are *relational Hoare logic* derivations, one can try to **translate the proof** instead of the program semantics. This is cheap for non-optimising passes and brittle for optimising ones. Prefer the semantic route (simulation ⇒ hyperproperty).

---

## 2. Optimisations that break which property

| Optimisation | Breaks | Mechanism | Fix / proof obligation |
|---|---|---|---|
| Dead store elimination | residue NI (memory probing), zeroisation | `memset(secret,0)` before free/return is dead to the functional semantics (Yang et al. USENIX Sec 2017 [K]; Simon, Chisnall, Anderson EuroS&P 2018 [K]) | Make erasure an *observable* event or volatile; or use a Besson-style IFP validator; or a zeroisation pass after regalloc (Jasmin TCHES 2024) |
| DCE inside branches | NI / CT with value-leakage | Rosemann Fig 1a: removes leakage asymmetrically across secret branches | NIFTY: local leakage transformers + rejoin check + rollback |
| Branch → cmov (if-conversion) | Usually *helps* CT; can break SCT. The reverse, **cmov/select → branch** (LLVM select lowering, `x86-cmov-conversion`), breaks CT | Schneider et al. "Breaking Bad", arXiv 2410.13489 (2025 paper) [V]: 44,604 targets, 8 libraries, 6 ISAs; Geimer & Maurice "Fun with flags", arXiv 2507.06112, PriSC 2026 [V]: a few GCC/LLVM passes cause most leaks, so disable those flags | Treat `select` as an opaque primitive with fixed leakage; prove that no pass introduces a secret-dependent branch (leakage transformer must be public-only) |
| Register allocation / spilling | residue (spilled secret persists in stack slot), slot collision (secret and public share a slot, so a later public read reveals stale secret at a probing point) | Besson et al. CSF 2019 | Erase spill slots at observation points; or typed slots (security level in the allocator interference graph); or zeroise the stack on return |
| CSE / GVN | Can merge a secret-dependent load with a public one, changing the address pattern; mostly safe for CT if leakage transformer is per-point | CompCert-CT handles CSE with the leakage-transformer condition | Leakage transformer `rm` on eliminated loads is fine only if src leakage at that point was public (follows from src CT) |
| Loop unrolling, strength reduction | CT is preserved if the trip count is public. **Timing/cost**: changes cost, so a cost bound needs a transformer with ≤ | Structured leakage handles this with a cost transformer | Prove cost_tgt ≤ f(cost_src) with public f |
| Removal of constant-time padding (dummy ops, balanced branches) | CT / cost-NI | Padding is semantically dead | Padding must be *leakage-visible* in the src semantics, so removing it changes the leakage transformer and the proof fails. Or forbid the optimisation on annotated regions |
| Lazy/short-circuit evaluation, `&&` lowering | CT | Boolean ops on secrets get compiled to branches | Lower to bitwise ops; or reject secret operands in the type system |
| Division / variable-latency instr. selection | timing | `div`, some `mul`, FP subnormals vary in latency | Target observation must include operands of variable-time instructions (Jasmin/CompCert-CT leak them or forbid them) |
| Speculative: removing redundant bounds checks, reordering loads past branches, SLH elision | SCT | POPL 2025 counterexamples with GCC -O0/-O1 and Jasmin | SCT-preservation proof per pass with a speculative semantics; preserve fences and `protect`/MSF ops as leakage-visible |
| Inlining / tail calls across trust boundaries | robust properties (RSP) | SECOMP forbids cross-compartment inlining and tail calls [V] | Do not inline across the FFI boundary |
| Stack layout / frame merging | slot collision, residue | — | Zeroise, or prove slot-typing invariants |

---

## 3. Termination, abort and trap channels

- **Classification.** TINI is 2-safety, so simulations handle it easily. TSNI is not safety: it needs divergence of one run ⇔ divergence of the other. CompCert's behaviours (Terminates t r / Diverges t / Reacts T / Goes_wrong t) preserve divergence [K]. Because of that, **CompCert-style behaviour equality preserves TSNI for deterministic programs when the observation is "trace + termination status"**: tgt_beh = src_beh for each secret, so if src_beh(s1) ≈ src_beh(s2) then tgt_beh(s1) ≈ tgt_beh(s2). The catch is that the *source* proof must be of TSNI over *infinite* behaviours, not over fuel-truncated runs.
- **Fuel-indexed source.** A fuel semantics `eval n σ = some σ' | none(out-of-fuel)` gives you, per fuel:
  - TINI: ∀n, both runs return some ⇒ equal low parts.
  - "Fuel-TSNI": ∀n, (eval n σ1).isSome ↔ (eval n σ2).isSome. That is strictly stronger than TSNI. It is *step-count* equality, so it is in fact a **timing NI** (cost leaks secret ⇔ fuel threshold differs).
  - Bridge to the target: if the compiler's simulation has a *public* step transformer (tgt_steps = g(src_steps, public)), then "fuel-TSNI at source" ⇒ "tgt step counts equal" ⇒ target termination-and-timing NI. **This is the same proof object as the CT/cost preservation.** Recommendation: state source NI as fuel-uniform (`∀n`, with equal-or-both-none), and require each pass's simulation to carry a step-count transformer that depends only on public data. Pure TSNI is then a corollary via `∃n` adequacy.
- **Abort/trap channels.**
  - Checked overflow, bounds check, div-by-zero and failed allocation are all *events*. If they depend on secrets, src NI must already account for them. Either the src semantics makes the trap an observable outcome, so NI forbids secret-dependent traps, or the src type system forbids checked ops on secrets.
  - Compiler-side: the trap must compile to **the same observable event**. Use a trace relation à la trace-relating CC: `src_trap ~ tgt_trap`, not `src_UB ~ anything`. **Never let source-level UB be the encoding of a trap.** CompCert lets the target do anything after UB, so a secret-dependent UB could become a secret-dependent leak.
  - Constant-time overflow checks: compute an overflow *flag* branch-free, accumulate it, and trap once at a public point. Or trap with the trap time padded. The trap point's location in the leakage tree must be public.
  - Out-of-memory / stack overflow: in CompCert these are target-only failures, so stack bounds are needed (Carbonneaux et al. PLDI 2014: quantitative CompCert, x86, Coq [V]). CakeML: space cost semantics carries out-of-memory *liveness* to machine code (Gómez-Londoño et al. OOPSLA 2020, PACMPL 4 [V]).

---

## 4. Recommended end-to-end architecture for a fuel-indexed deterministic Lean source

### 4.1 One observation type for everything
Make every IR's semantics produce:
```
Obs := { io      : List Event        -- I/O, emitted strings, auth-check events, protected reads, alloc/free events
       , leak    : LeakTree          -- structured leakage: branch outcomes, mem addresses, variable-time operands, call/ret
       , cost    : Nat               -- or derivable from leak
       , outcome : Done σ_pub | Trap code | OutOfFuel }
```
- Properties 4, 5, 6 and 7 are predicates on `io`/`cost`/`outcome`, so they transfer through `io` equality, outcome relation and a cost inequality.
- Properties 1, 2, 3, 8 and 9 are relational predicates over two Obs that are equal on `io` (public part) and `leak`, and for 9 also equal on declassified values.

### 4.2 Per-pass obligation: a "leakage-transformer simulation"
For each pass `P : IR_i → IR_{i+1}` provide:
1. **Functional:** forward simulation, with determinism ⇒ `io_tgt = io_src` and `outcome_tgt ~ outcome_src`. `~` is the trace relation, e.g. `OutOfFuel n ↦ OutOfFuel (g n)`.
2. **Leakage:** a function `T_P : (prog, public-annotations) → LeakTree → LeakTree` with `leak_tgt = T_P(leak_src)`. Use *local* transformers (per program point, Rosemann et al. 2025) where DCE-like passes need them. `T_P` may inspect the program and *public* data only.
3. **Cost:** `cost_tgt ≤ c_P(cost_src)`, or `=` for timing NI. Exact equality is needed for timing-NI, an inequality suffices for budgets.
4. **Residue/erasure:** at each observation point (return, syscall, FFI call), the *full* target state restricted to the attacker-readable part (registers, stack below sp, freed heap) is a public function of the src public state. In practice, discharge this with a final zeroisation pass and its own proof (Jasmin TCHES 2024).
- **Composition is trivial.** Transformers compose, `T_{Q∘P} = T_Q ∘ T_P`, and so do trace relations and cost bounds. Then src NI (`leak_src(s1) = leak_src(s2)`) ⇒ tgt NI. This is the Jasmin CCS 2021 / ePrint 2026 "deterministic leakage preservation relation" argument. It sidesteps the Kruse et al. composition pitfalls, because every pass preserves the *same* strongest relation rather than different properties.
- For passes where a global transformer is impossible (DCE inside secret branches), either restrict the pass to public regions, or use NIFTY (check + rollback) with an indistinguishability simulation.
- For aggressive passes, prefer **translation validation**: the untrusted pass emits `T_P` plus a simulation witness, and a verified Lean checker validates them per program.

### 4.3 What must be stated about the target's observation
1. **Architectural state at observation points:** all GPRs, flags, vector registers, the stack region below/above sp that the callee touched, and freed heap. Either it is fully in the attacker view (Besson memory-probing model) and erased, or it is explicitly excluded by a hardware isolation assumption.
2. **PC trace + memory-address trace + operands of variable-time instructions:** the baseline CT leakage, as in CompCert-CT and Jasmin.
3. **Timing model:** state as an *assumption* "time = f(leakage trace)", i.e. a hardware-software contract (Guarnieri et al. S&P 2021 [K]; contract-aware compilation, arXiv 2012.14205 [V]). Never claim cycle-exactness. Cost bounds are in abstract units mapped by a stated per-instruction table.
4. **Speculation contract:** for SCT, the target semantics needs a speculative oracle/directive model (Cauligi et al. PLDI 2020 [K]; Jasmin POPL 2025) and the passes must preserve SCT. Otherwise state explicitly that Spectre is out of scope.
5. **Linking/FFI:** for robust claims, state the isolation mechanism (compartments + shadow stack as in SECOMP, or CHERI) and prove RSP for the safety-class properties. Hyperproperty robustness (RHP) against arbitrary C code is currently out of reach for realistic targets, so restrict it to well-typed or CT contexts.
6. **Fuel ↔ divergence:** an adequacy lemma tying fuel-uniform src statements to the target's infinite behaviours.

### 4.4 Route choice
- **Via CompCert:** you inherit 20+ verified passes but must re-prove leakage preservation (CompCert-CT exists for CT only, is a fork, and is Coq, not Lean). The C semantics has UB, so trap/UB distinctions get lost unless the C you emit is UB-free by construction. Residue is not handled. SCT is not handled.
- **Via Jasmin:** the closest match in design (structured leakage, zeroisation, SCT, cost). It is Coq, the source language is Jasmin, and it targets x86-64/ARMv7/RISC-V. A plausible pragmatic route: compile the Lean IR to Jasmin source, prove *that* translation is a leakage-transformer simulation in Lean, and trust or reuse Jasmin's Coq theorems across the prover gap.
- **Direct Lean-native compiler:** a small number of passes (no aggressive optimisation), each a leakage-transformer simulation, then a final zeroisation pass, then an assembly printer validated by translation validation. This is the cleanest for carrying *all nine* certificates in one framework. Cost: no optimisation and an unverified assembler/printer.

---

## 5. Open gaps (as of 2026-10)
- Mechanised compilers that preserve **declassification policies** (bounded release, robust declassification): no hit in the searches.
- RHP for realistic C-level targets: not achieved. SECOMP reached an RSP variant only.
- TSNI preservation as a headline result: implicit via CompCert behaviour equality plus determinism, but no paper found that states it with a fuel-indexed source.
- Concurrent NI + optimisation: CoCo is a single-pass, non-optimising compiler.

## Sources (primary)
- Abate et al., Journey Beyond Full Abstraction, CSF 2019: https://arxiv.org/abs/1807.04603 , https://www.mpi-sws.org/~dg/papers/csf2019.pdf
- Abate et al., Trace-Relating Compiler Correctness and Secure Compilation, ESOP 2020: https://arxiv.org/abs/1907.05320
- Kruse, Backes, Patrignani, Secure Composition of Robust and Optimising Compilers: https://arxiv.org/abs/2307.08681
- Barthe, Grégoire, Laporte, CSF 2018: https://members.loria.fr/VLaporte/files/CSF2018_ConstantTimePreservation.pdf , https://eprint.iacr.org/2017/1233
- Barthe et al., Formal verification of a constant-time preserving C compiler, POPL 2020: https://eprint.iacr.org/2019/926
- Barthe, Grégoire, Laporte, Priya, Structured Leakage, CCS 2021: https://eprint.iacr.org/2021/650
- Barthe, Blazy, Hutin, Pichardie, Secure Compilation of Constant-Resource Programs, CSF 2021: https://hal.archives-ouvertes.fr/hal-03221440
- Arranz Olmos et al., Preservation of SCT by Compilation, POPL 2025: https://eprint.iacr.org/2024/1203 , https://hal.univ-lorraine.fr/hal-04663857v2
- Arranz Olmos et al., Protecting Cryptographic Code Against Spectre-RSB, ASPLOS 2025: https://eprint.iacr.org/2024/1070
- High-assurance zeroization, TCHES 2024: https://eprint.iacr.org/2023/1713
- Barthe et al., Secure Compilation of Probabilistic Side-Channel Countermeasures, S&P'27: https://eprint.iacr.org/2026/2510
- Rosemann, Hack, Garg, Non-interference Preserving Optimising Compilation, OOPSLA 2025: https://doi.org/10.1145/3763101 , https://compilers.cs.uni-saarland.de/papers/rosemann_ni_preserving_oopsla25.pdf
- Besson, Dang, Jensen, IFP in compiler optimisations, CSF 2019 (slides): https://web.stevens.edu/csf2019/presentations/dang.pdf ; Securing compilation against memory probing, PLAS 2018
- Sison & Murray, ITP 2019: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.27 ; JFP 2021: https://doi.org/10.1017/S0956796821000162
- Thibault et al., SECOMP, CCS 2024: https://arxiv.org/abs/2401.16277
- Patrignani & Guarnieri, Exorcising Spectres with Secure Compilers, CCS 2021: https://arxiv.org/abs/1910.08607
- Guarnieri & Patrignani, Contract-Aware Secure Compilation: https://arxiv.org/abs/2012.14205
- Namjoshi & Tabajara, Witnessing Secure Compilation, VMCAI 2020: https://arxiv.org/abs/1911.05866
- Schneider et al., Breaking Bad: https://arxiv.org/abs/2410.13489 ; Geimer & Maurice, Fun with flags: https://arxiv.org/abs/2507.06112
- Carbonneaux et al., stack-space bounds, PLDI 2014: https://www.cs.yale.edu/homes/hoffmann/papers/veristack2014.pdf
- Gómez-Londoño et al., CakeML space cost, OOPSLA 2020: https://doi.org/10.1145/3428272
- Conoly, Erbsen, Chlipala, Smooth integrated CT proofs (Bedrock2→RISC-V), PLDI 2025: https://arxiv.org/abs/2504.15550
- Also cited from background knowledge (not re-fetched): Patrignani/Ahmed/Clarke CSUR 2019; Patrignani & Garg ESOP 2019 (Robustly safe compilation); Murray et al. CSF 2016; Necula PLDI 2000; Cogent (ICFP/ITP 2016); Barthe/Crespo/Kunz FM 2011; Yang et al. USENIX Sec 2017; Simon et al. EuroS&P 2018; Guarnieri et al. S&P 2021; Cauligi et al. PLDI 2020; Cecchetti et al. CCS 2017.
