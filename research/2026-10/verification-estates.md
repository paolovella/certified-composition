# Multi-tool formal verification estates (candidate inputs for certified-composition)

NOTE: Plan mode was active, so these notes are in the plan file instead of the requested path
(.../scratchpad/research_notes/Certified composition field refresh/verification_estates.md).
Copy them there once plan mode ends. Repo facts below come from the GitHub API (`gh api`), checked 2026-10-23.

## Q1. Best 1-3 targets for "two different tools certify two components, composed, with a stated seam assumption", ranked by how machine-readable the evidence is

### Takeaway
**mlkem-native is the clear #1.** CBMC certifies the C code (memory and type safety, coefficient bounds). HOL Light with s2n-bignum certifies the AArch64/x86_64 assembly (functional correctness, memory safety, constant time). At each C-to-asm call site the seam is a CBMC `__contract__` that copies part of the HOL Light spec by hand. Each contract carries a `/* must be kept in sync with ... .ml */` pointer, and SOUNDNESS.md documents the seam assumption explicitly. **#2 is AWS-LC importing mlkem-native and s2n-bignum.** It adds a third seam: AWS-LC's own FIPS-202 glue replaces mlkem-native's Keccak, so it now fills the contract that CBMC assumed. **#3, a different shape: verify-rust-std.** Kani and ESBMC (through goto-transcoder) check the same `#[requires]/#[ensures]` contracts in core, alongside VeriFast, Flux, KMIR and RAPx. It publishes JSON metrics. libcrux has the most tools on paper, but its Jasmin-to-Rust seam is undocumented: the README is TODO stubs.

### Cited Findings
**mlkem-native** (https://github.com/pq-code-package/mlkem-native): licence Apache-2.0 OR ISC OR MIT (SPDX headers; GitHub reports NOASSERTION). Last push 2026-10-21.
- SOUNDNESS.md ("Formal Verification in mlkem-native: Scope, Assumptions, Risks") states two stacks. **CBMC** covers the C code: memory safety, type safety, no UB. **HOL Light + s2n-bignum** covers the assembly: functional correctness, memory safety, secret-independent execution. The doc is organised as Gap A (spec faithfulness), Gap B (model fidelity) and Gap C (prover TCB). — [SOUNDNESS.md](https://github.com/pq-code-package/mlkem-native/blob/main/SOUNDNESS.md)
- Coverage claim: "All C code in the core library has CBMC contracts". All AArch64 and x86_64 assembly has HOL Light specs. The RISC-V RVV, Armv8.1-M MVE and PowerPC backends are not covered. There is "currently no automatic coverage check for CBMC or HOL Light" (issues #1423, #1594). — [SOUNDNESS.md §A1](https://github.com/pq-code-package/mlkem-native/blob/main/SOUNDNESS.md)
- The CBMC proofs do NOT cover functional correctness or constant-time for the C code. Constant time is only tested with valgrind (ct-tests.yml). — [SOUNDNESS.md §A2](https://github.com/pq-code-package/mlkem-native/blob/main/SOUNDNESS.md)
- **The seam, verbatim:** "Where C code calls into assembly, the assembly function has both a HOL Light specification (proved against the object code) and a CBMC contract (assumed by CBMC when proving the C caller). These two specifications are written in different languages and are currently kept in sync by hand." The CBMC contract is "typically a subset of the HOL Light specification obtained by removing aspects of functional correctness". Alignment constraints "cannot be faithfully expressed in CBMC's object model, and are currently omitted". — [SOUNDNESS.md §A4 "The bridge between CBMC and HOL Light"](https://github.com/pq-code-package/mlkem-native/blob/main/SOUNDNESS.md)
- Worked seam example, AArch64 NTT:
  - HOL Light proves: `abs(ival(x i)) <= &8191` ⇒ `abs(ival zi) <= &23594` and `ival zi == forward_ntt(...) mod 3329`. It assumes `ntt_constants z_12345 z_67 s`.
  - The CBMC contract has `requires(array_abs_bound(p,0,MLKEM_N,8192))`, `ensures(array_abs_bound(p,0,MLKEM_N,23595))` and `requires(twiddles12345 == mlk_aarch64_ntt_zetas_layer12345)`.
  - Source: [SOUNDNESS.md](https://github.com/pq-code-package/mlkem-native/blob/main/SOUNDNESS.md). I confirmed the contract in [mlkem/src/native/aarch64/src/arith_native_aarch64.h](https://github.com/pq-code-package/mlkem-native/blob/main/mlkem/src/native/aarch64/src/arith_native_aarch64.h). It has the comment `/* This must be kept in sync with the HOL-Light specification in proofs/hol_light/aarch64/proofs/mlkem_ntt_aarch64_asm.ml */`, and that .ml file contains `MLKEM_NTT_CORRECT`, `MLKEM_NTT_SUBROUTINE_CORRECT` and `MLKEM_NTT_SUBROUTINE_SAFE` (the CT + safety proof via `s2n_bignum/arm/proofs/consttime.ml`).
- Named residual seam risks: a transcription error (off-by-one bound, missing aliasing constraint), an ABI mismatch, and a signed/unsigned semantic gap. HOL Light alignment assumptions are not checked against callers. A tracked issue covers a machine-checked HOL-Light-to-CBMC link: #1601. Alignment checking in CBMC: #1932. — [SOUNDNESS.md](https://github.com/pq-code-package/mlkem-native/blob/main/SOUNDNESS.md)
- Mitigations: constant tables for both sides are generated from `scripts/autogen` in CI. `scripts/check-contracts` finds contracts that have no proof. CBMC bounds are mirrored by runtime debug asserts. — [SOUNDNESS.md](https://github.com/pq-code-package/mlkem-native/blob/main/SOUNDNESS.md)
- Gap B: the HOL Light proofs are on object-code bytes, which takes the assembler out of the TCB. There is a "reassembly risk" for downstream consumers such as AWS-LC, with no systematic byte check yet (#1602). ISA-model fidelity is inherited from s2n-bignum's co-simulation CI. — [SOUNDNESS.md §B1-B2](https://github.com/pq-code-package/mlkem-native/blob/main/SOUNDNESS.md)
- Gap C, per-tool TCB:
  - HOL Light: ~400-line kernel, 10 rules, 3 axioms, plus OCaml. It can be independently rechecked with Candle or HOLTrace.
  - CBMC: CBMC itself, the SMT solvers (Z3, Bitwuzla) and the C preprocessor. The doc calls this "orders of magnitude larger" and notes there is no independent proof checking.
  - Source: [SOUNDNESS.md §C1-C2](https://github.com/pq-code-package/mlkem-native/blob/main/SOUNDNESS.md)
- Artifacts in the repo:
  - `proofs/cbmc/` has about 190 per-function proof dirs, each with a Makefile, plus `list_proofs.sh` and `Makefile.common`, which lists the UB classes checked.
  - `proofs/hol_light/{aarch64,x86_64,common}/proofs/*.ml`.
  - `proofs/hol_light/s2n_bignum_allowlist.txt` is a structured list of the s2n-bignum files the proofs may `needs`: arm/x86 `base.ml` and `consttime.ml`.
  - `proofs/hol_light/aarch64/proofs/subroutine_signatures.ml` is a structured OCaml list of per-function C signatures with input, output and temp buffer sizes. It is effectively a machine-readable ABI side of the seam.
  - CI workflows: `cbmc.yml`, `hol_light.yml`, `ct-tests.yml`, `integration-awslc.yml`.
  - Source: GitHub tree of [pq-code-package/mlkem-native](https://github.com/pq-code-package/mlkem-native/tree/main/proofs)
- Sibling **mldsa-native** (https://github.com/pq-code-package/mldsa-native, last push 2026-10-22) has the same CBMC + HOL Light structure plus `proofs/isabelle/` (Barrett-division `compress` and `neon_ntt` math). Its SOUNDNESS.md defers to mlkem-native's analysis and adds rejection-sampling risks. The Isabelle developments are standalone math lemmas, not a third seam. — [mldsa-native proofs/isabelle/README.md](https://github.com/pq-code-package/mldsa-native/blob/main/proofs/isabelle/README.md)

**AWS-LC** (https://github.com/aws/aws-lc, last push 2026-10-22; Apache-2.0/ISC per its LICENSE, NOASSERTION on GitHub):
- `crypto/fipsmodule/ml_kem/META.yml` records the import of mlkem-native at branch `v2.0.0`, commit `d1b2fe78...`, `imported-at: 2026-08-17`. — [META.yml](https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/ml_kem/META.yml)
- The ml_kem README says the importer brings in "only the C-only version". It also says mlkem-native's FIPS-202 is not imported: AWS-LC's own FIPS-202 sits behind `fips202_glue.h` / `fips202x4_glue.h`. Config remaps zeroize to `OPENSSL_cleanse` and randombytes to `RAND_bytes`. — [ml_kem/README.md](https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/ml_kem/README.md). **Conflict:** the current tree also has `crypto/fipsmodule/ml_kem/mlkem/native/{x86_64,aarch64}/` (26 files under x86_64/src), so the "C-only" sentence looks stale. Verify which is right.
- s2n-bignum is vendored at `third_party/s2n-bignum/s2n-bignum-imported/{arm,x86_att}/...`, covering p256, p384, p521, curve25519, secp256k1, sm2 and mldsa. Import metadata is in `third_party/s2n-bignum/META.yml`. — AWS-LC tree (gh api)
- SAW/Cryptol proofs of AWS-LC live in a separate repo, https://github.com/awslabs/aws-lc-verification (Apache-2.0, last push 2026-03-26, so less active). I did not inspect its contents this pass.
- A 2026 SOS-VO abstract says the verified ML-KEM was integrated into AWS-LC's FIPS validation cycle and that AI tools helped propose HOL Light proof strategies. It reports 2.08x–2.78x speedups on Graviton (secondhand abstract). — [sos-vo.org/node/109616](https://sos-vo.org/node/109616)

**s2n-bignum** (https://github.com/awslabs/s2n-bignum, Apache-2.0 OR ISC OR MIT-0, last push 2026-10-22):
- SOUNDNESS.md has sections A1-A4, B1-B3 and C1, plus **Gap D "Integration and cross-cutting concerns"**: D1 global execution-environment assumptions, D2 C header/assembly interface, D3 compositional use in higher-level libraries. — [s2n-bignum SOUNDNESS.md](https://github.com/awslabs/s2n-bignum/blob/main/SOUNDNESS.md)
- `non_ct_functions.txt` at the repo root is a plain-text, machine-readable list of functions that are NOT constant-time (e.g. `p256/bignum_mod_n256o:`). — [non_ct_functions.txt](https://github.com/awslabs/s2n-bignum/blob/main/non_ct_functions.txt)

**verify-rust-std** (https://github.com/model-checking/verify-rust-std, Apache-2.0/MIT like Rust, last push 2026-10-22):
- CI workflows: `kani.yml`, `kani-metrics.yml`, `verifast.yml`, `verifast-negative.yml`, `flux.yml`, `kmir.yml`, `rapx.yml`, `goto-transcoder.yml`. Tool docs are in `doc/src/tools/{kani,verifast,flux,kmir,rapx,goto-transcoder}.md`. — repo tree (gh api)
- goto-transcoder converts Kani's CBMC GOTO binaries for ESBMC. PR #710 (2026-10-04) is "Check contracts with ESBMC's native CBMC goto reader". This is two independent back-ends checking the *same* contracts. — [goto-transcoder.md](https://github.com/model-checking/verify-rust-std/blob/main/doc/src/tools/goto-transcoder.md); commit log
- Machine-readable metrics: `scripts/kani-std-analysis/metrics-data-{core,std,alloc}.json`, refreshed about weekly ("Update Kani Metrics" PRs #665…#724, Aug–Oct 2026). `scripts/find-contracts.sh` and `autoharness_analyzer` also exist. — [PR #724 files](https://github.com/model-checking/verify-rust-std/pull/724)

### Inferences
- Ranking by machine-readable evidence:
  1. mlkem-native. Structured per-function seam pairs: a C contract plus a sync-comment path to a HOL Light theorem name, the `subroutine_signatures.ml` ABI list and the allowlist. SOUNDNESS.md is prose but itemised.
  2. AWS-LC + mlkem-native + s2n-bignum. META.yml import pins make the composition auditable at the commit level. The FIPS-202 glue seam is a real case where a CBMC-assumed callee contract is met by code that is not verified, or is verified elsewhere.
  3. verify-rust-std. Machine-readable JSON, but the multi-tool story is "same contract, two checkers" (redundancy), not "two components composed".
- For certified-composition, mlkem-native's seam maps directly onto "certificate A (HOL Light, TCB = HOL kernel + OCaml + ISA model + ELF loader) assumed as an axiom by certificate B (CBMC, TCB = CBMC + Z3/Bitwuzla + C frontend), glued by a hand-synced contract". The accumulated TCB is the union of both plus the hand-sync obligation. #1601 is exactly the gap the project could close.
- Parsing route: each CBMC contract with a `kept in sync with ... <file>.ml` comment can be paired automatically with the `*_SUBROUTINE_CORRECT` / `*_SAFE` theorems in that file. CBMC run output can be emitted as JSON (`cbmc --json-ui`). I did not confirm whether mlkem-native's CI publishes JSON.

### Gaps
- I did not confirm whether `hol_light.yml` / `cbmc.yml` upload logs or JSON as CI artifacts, or what retention they use.
- I did not read s2n-bignum SOUNDNESS §D2/D3 in full.
- I did not inspect aws-lc-verification (SAW) contents or check whether any SAW proof meets an s2n-bignum or mlkem-native component.

## Q2. Do any publish their assumptions in a structured form?

### Takeaway
Yes, though it is uneven. The most structured examples are:
- s2n-bignum's `non_ct_functions.txt` and mlkem-native's `s2n_bignum_allowlist.txt` / `subroutine_signatures.ml` (plain-text and OCaml lists).
- dalek-lite's Verus `tracked_functions.csv` (has_spec/has_proof), `stats_history.jsonl` and a probe-verus spec JSON with `kind` / `has_trusted_assumption`.
- SymCrypt's Lean `Intrinsics/Axioms/**`, where trusted intrinsic semantics are isolated as Lean axioms, so `#print axioms` gives a machine-derived list.
- libcrux's `verification_status.md`, a script-generated Markdown table.

The two SOUNDNESS.md files (mlkem-native, s2n-bignum) are the best prose "what is proved / what is assumed" docs.

### Cited Findings
- **libcrux** (https://github.com/cryspen/libcrux, Apache-2.0, last push 2026-10-22):
  - `libcrux-ml-kem/proofs/verification_status.md` is a per-module table (Fns / Panic-free / Correct / Properties). It is "generated by a simple script". Examples: generic `ind_cpa` 0/21, `sampling` 0/5, Neon arithmetic 0/13, AVX2 arithmetic 11/12 correct. It was last updated 2026-03-10.
  - Tools: hax→F* (`proofs/fstar/extraction*`, `.hints`; workflows `mlkem-hax.yml`, `mldsa-hax.yml`, `sha3-hax.yml`, `kmac-hax.yml`), Aeneas→Lean for the SHA-3 spec (`specs/sha3/proofs/aeneas-lean/`), and libjade Jasmin via `crates/sys/libjade/jazz` plus a Rust -sys crate. There are also HACL* and Vale components and a constant-time test workflow (`libcrux-ct-test.yml`).
  - Source: [verification_status.md](https://github.com/cryspen/libcrux/blob/main/libcrux-ml-kem/proofs/verification_status.md); repo tree
- The libcrux Jasmin seam is undocumented. `formal_verification/libjade/README.md` claims each libjade implementation has memory safety, functional correctness (EasyCrypt), timing protection, Spectre v1/v4 protection and stack cleanup. But its "Wrapping the libjade APIs within Rust" and "Spec Equivalence" sections are literal "TODO: something like the following" text copied from the HACL* page (it even says "verified implementations from HACL*"). The References list is empty. — [formal_verification/libjade/README.md](https://github.com/cryspen/libcrux/blob/main/formal_verification/libjade/README.md)
- **SymCrypt** (https://github.com/microsoft/SymCrypt, MIT): the proofs are on branch `feature/verifiedcrypto` under `SymCRust/lean/`, published by the commit "Publish ML-KEM and SHA3 proofs" on 2026-07-12.
  - `SymCRust/lean/Intrinsics/INTRINSICS.md` sets the policy. Each hardware intrinsic gets either an Aeneas-extracted Rust model with a proved Lean theorem in `Intrinsics/Properties/**`, or an explicit Lean axiom in `Intrinsics/Axioms/**` ("a deliberate trust decision"). The axioms cover unsafe raw-pointer intrinsics and crypto accelerators (AES, SHA-2, PCLMULQDQ, Armv8 AES).
  - The Rust side marks these `#[verify::opaque]`, and the `verify` feature keeps production builds bit-identical.
  - Source: [INTRINSICS.md](https://github.com/microsoft/SymCrypt/blob/feature/verifiedcrypto/SymCRust/lean/Intrinsics/INTRINSICS.md)
- The SymCrypt paper "Scaling Verification of Cryptographic Software with Aeneas, Rust, and Lean" (arXiv 2609.15648, Sept 2026, draft) reports a 237 KLOC Lean development proving safety, panic-freedom and functional correctness of 16.7 KLOC of Rust for x86-64 and ARM (secondhand via search summary). — [arXiv 2609.15648](https://arxiv.org/pdf/2609.15648); [MSR blog](https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/)
- **dalek-lite** (https://github.com/Beneficial-AI-Foundation/dalek-lite, last push 2026-10-08):
  - A Verus-verified fork of curve25519-dalek (serial/u64 backend only).
  - `.verilib/tracked_functions.csv` has columns `function,module,link,has_spec,has_proof`.
  - `outputs/stats_history.jsonl` holds snapshots like `{"total":223,"specs":175,"specs_external":3,"proofs":103}` (2025-12-29 snapshot).
  - `spec-taxonomy.toml` configures `probe-verus extract`. Its comments say the "Specs JSON answers: is this claim proved or assumed? (kind, has_trusted_assumption)" and that `docs/axiom_references.md` justifies each assumption.
  - There are no .lean files, so this is a single tool (Verus).
  - Source: [dalek-lite spec-taxonomy.toml](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/spec-taxonomy.toml); [tracked_functions.csv](https://github.com/Beneficial-AI-Foundation/dalek-lite/blob/main/.verilib/tracked_functions.csv)
- **s2n-bignum**: `non_ct_functions.txt` (above). **mlkem-native**: `s2n_bignum_allowlist.txt` (above).

### Inferences
- None of these publish a *cross-tool* seam in a structured form. mlkem-native's sync comments plus `subroutine_signatures.ml` come closest, and the parsing could be automated.
- SymCrypt's axiom files plus Lean `#print axioms` would give a machine-derived assumption list for one tool. That is a natural "assumed base" input, but there is no second tool to compose with.
- dalek-lite's probe-verus JSON with `has_trusted_assumption` is the most explicitly ledger-shaped artifact found. It is a good model for the per-certificate format even though it is single-tool.

### Gaps
- I did not fetch dalek-lite's actual specs JSON or `docs/axiom_references.md`, so the field schema is known only from the taxonomy comments.
- I did not count `axiom` declarations in SymCrypt: my grep for `^axiom` in `Axioms/X86_64/Common.lean` returned 0, so the axioms may be written in another syntax, such as an attribute or indentation.
- I did not check whether libcrux's status-table script is in the repo.

## Q3. What's new Aug–Oct 2026, and status of the other candidates

### Takeaway
The pq-code-package and s2n-bignum estates are very active and are tightening the exact seams that matter here. libcrux and SymCrypt remain active, but their verification artifacts changed little in the window. Many other candidates were checked only for activity, or not deeply.

### Cited Findings
- **mlkem-native, Aug–Oct 2026 commits:**
  - 2026-10-05 "HOL-Light/x86_64: Drop alignment assumption on tobytes/frombytes byte buffers". This fixes the seam bug SOUNDNESS.md cites as an example.
  - 2026-10-11 "HOL-Light: Don't report incomplete proof runs as OK".
  - 2026-10-12 "README: Exclude unproven backends and debug code from the CBMC claim" and "SOUNDNESS: State the scope of the constant-time tests".
  - 2026-10-17 "check-contracts: Find contracts with parentheses in the parameter list".
  - 2026-09-27 "CBMC: Use only array_unchanged in native fallback postconditions".
  - 2026-09-10 "CBMC: Add selectable proof configurations".
  - 2026-10-03 "Bump libOQS, Pavona, and AWS-LC pins".
  - Source: [commit log](https://github.com/pq-code-package/mlkem-native/commits/main)
- **s2n-bignum, Aug–Oct 2026:**
  - 2026-09-17 "Add x86 HOL-Light proofs for seven ML-DSA polynomial routines (#426)".
  - 2026-09-19 "Add partial RISCV32-IM model (#455)".
  - 2026-09-17 "Generalize ISA proof infrastructure for 32-bit backends (#452)".
  - 2026-09-22 RV32IM cosimulation and "cross-ct" PR #459.
  - 2026-10-21 "RISCV: Add Sail-backed executor for RV32IM cosimulation (#467)".
  - 2026-10-22 "AES-GCM for Graviton2 (#470)".
  - Many new Arm instruction models (#431/#433/#434/#436).
  - Source: [commit log](https://github.com/awslabs/s2n-bignum/commits/main)
- **AWS-LC:** mlkem-native v2.0.0 imported 2026-08-17. — [META.yml](https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/ml_kem/META.yml)
- **verify-rust-std:** ESBMC contract checking (#710, 2026-10-04); RAPx tool and CI added (#491, #631, 2026-08-29); `unsafe-finder` tool (#369, 2026-09-12); NonZero challenge marked resolved (#663, 2026-09-01); weekly Kani metrics. — [commit log](https://github.com/model-checking/verify-rust-std/commits/main)
- **libcrux:** release version bumps 2026-10-06. The verification_status table is unchanged since 2026-03-10. hax is merging the Aeneas engine and the Lean backend now supports while loops (Jan–Mar 2026 hax blog, outside the window). — [hax blog](https://hax.cryspen.com/blog/); [2026-01-19 post](https://hax.cryspen.com/blog/2026/01/19/verifying-a-real-world-rust-crate/)
- **SymCrypt:** the `main` push was 2026-08-06; proofs were published on `feature/verifiedcrypto` 2026-07-12; the arXiv paper is Sept 2026. — gh api; [arXiv 2609.15648](https://arxiv.org/pdf/2609.15648)
- **zkVM / Ethereum Foundation:** Galois is verifying Jolt's frontend against Sail RISC-V in Lean 4 (EF-funded, no completion date). An EVM-in-RISC-V-assembly Lean project had 24 of 55 RISC-V opcodes verified as of the 2026-04-08 breakout. These are secondhand blog and meeting notes, with no Aug–Oct primary update found. — [Galois](https://www.galois.com/articles/towards-a-verified-jolt-zkvm); [Eth Magicians breakout #03](https://ethereum-magicians.org/t/l1-zkevm-breakout-03-april-8-2026/28148)
- **Activity only (gh api pushed_at):**

  | Repo | Last push | Licence |
  | --- | --- | --- |
  | hacl-star | 2026-06-07 | Apache-2.0 |
  | formosa-crypto/formosa-mlkem | 2026-07-24 | none reported |
  | libjade | 2026-10-01 | |
  | jasmin | 2026-10-22 | MIT |
  | asterinas | 2026-10-22 | MPL-2.0 |
  | asterinas/vostd (Verus) | 2026-10-22 | MPL-2.0 |
  | mars-research/atmosphere | 2026-02-02 | MIT; stale |
  | firecracker | 2026-10-22 | Apache-2.0 |
  | hyperlight | 2026-10-22 | Apache-2.0 |
  | seL4 | 2026-10-22 | |
  | tock | 2026-10-22 | |
  | curve25519-dalek | 2026-09-24 | |

  Firecracker has `docs/formal-verification.md` and Kani harnesses (e.g. `src/vmm/src/rate_limiter/mod.rs`, `src/vmm/src/dumbo/pdu/ethernet.rs`), but it is single-tool.

### Inferences
- The October 2026 mlkem-native changes (alignment assumption dropped, incomplete runs no longer reported OK, CBMC claim scope narrowed) are fresh, citable examples of seam-assumption maintenance. They are good test cases for "the composed TCB/claim changed when one side's assumption changed".
- s2n-bignum's ML-DSA x86 proofs plus the mldsa-native CBMC contracts make **mldsa-native a second instance of the same two-tool seam**.

### Gaps
- Not investigated in depth this pass:
  - seL4 + CAmkES (Isabelle; CAmkES has no proofs of glue code, as far as I know, unverified)
  - Tock (Flux/Verus efforts)
  - Hyperlight
  - Atmosphere (Verus)
  - Asterinas vostd
  - s2n-tls (SAW + CBMC)
  - HACL*/EverCrypt (F* + Vale, the closest "two tools in one estate" with the Vale↔Low* interop seam)
  - libjade standalone (Jasmin + EasyCrypt)

  HACL*/EverCrypt and s2n-tls are worth a follow-up as further two-tool seams.
- I found no primary Aug–Oct 2026 announcements for zkVM verification, Cryspen/libcrux, or AWS-LC FIPS certificate status.
- Housekeeping: three tree-listing files were written to the scratchpad (`mlkn_tree.txt`, `libcrux_tree.txt`, `awslc_tree.txt`) during research.
