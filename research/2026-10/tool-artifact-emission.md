# Tool artifact emission: which verifiers emit consumable "what was established + assumptions" artifacts (as of 2026-10-23)

NOTE: Plan mode blocked writing to the requested path
`/tmp/claude-1000/-home-paolo-certified-composition/cbe1e5c5-1c8d-4aa0-b648-aecd0fe50c94/scratchpad/research_notes/Certified composition field refresh/tool_artifact_emission.md`.
The notes are here instead. Copy them over verbatim once plan mode ends.

Legend: [V] = checked this session on a primary source. [T] = from training knowledge (cutoff June 2026), not re-checked this session. Treat [T] as secondhand.

## Q1: Which tools have an explicit audit / assumptions-report feature, and what does the output look like?

### Takeaway
Six tools have a real assumptions report: Dafny (`dafny audit`), SAW (`summarize_verification`, with JSON), Lean (`#print axioms`, and since 2026-10-12 `lake check` and `lake comparator`), Rocq (`Print Assumptions`, `coqchk -o`), F* (`--report_assumptions` [T]) and Isabelle (`thm_oracles` [T]). Verus has no listing of its own. It has only `--no-cheating`, which turns any assume, admit, `external_body` or `assume_specification` into a rejection. That is a gate with a yes/no answer, not a ledger. Of these, only Dafny's audit has a diff-in-CI mode (`--compare-report`), and only SAW's summary has documented JSON "for consumption by other tools".

### Cited Findings

**Dafny `dafny audit` [V]**
- The command is marked "_This command is under development._" It runs the resolve phase, so it needs no verification run. — [Dafny UserGuide.md](https://raw.githubusercontent.com/dafny-lang/dafny/master/docs/DafnyRef/UserGuide.md)
- Options:
  - `--report-file:<f>`. Without it, findings are "issued as standard warnings, written to standard-out".
  - `--report-format:<fmt>`, one of `txt`/`text` ("plain text in the format of warnings"), `html`, `md`/`markdown`/`md-table`/`markdown-table`, or `md-ietf`/`markdown-ietf` (an IETF-language document).
  - `--compare-report`, which compares against the existing `--report-file` and fails on a difference. This is the same accept.expected-style diff the project already uses for Jasmin.
  — [UserGuide.md](https://raw.githubusercontent.com/dafny-lang/dafny/master/docs/DafnyRef/UserGuide.md)
- Exit codes: 0 means normal operation, "including operation that identifies audit findings". 1 means a command-line error. 2 means a parse or type error, a failure in the auditor, or a failed report comparison. — [UserGuide.md](https://raw.githubusercontent.com/dafny-lang/dafny/master/docs/DafnyRef/UserGuide.md)
- What it flags:
  - declarations with `{:axiom}`
  - declarations with `{:verify false}`
  - `{:extern}` declarations with at least one requires or ensures clause
  - any definition with `assume` in its body
  - methods with `decreases *`
  - `forall` statements without a body
  - loops without a body
  - any declaration with no body and at least one `ensures`
  — [UserGuide.md](https://raw.githubusercontent.com/dafny-lang/dafny/master/docs/DafnyRef/UserGuide.md)
- The doc gives no column list and no example output. As I recall [T], the markdown table has the columns Name / Compiled / Explicit Assumption / Extern / Issue / Mitigation. Confirm this by running it.
- Related: with `--log-format text` and `--warn-redundant-assumptions`/`--warn-contradictory-assumptions`, the log lists "proof dependencies (including source location and description)". `--log-format csv` goes with `measure-complexity`. — [UserGuide.md](https://raw.githubusercontent.com/dafny-lang/dafny/master/docs/DafnyRef/UserGuide.md)
  - Also [T]: `--log-format json` exists in Dafny 4.x and gives per-implementation outcome and resource count. My fetch read only the first 100k of 143k characters, so I could not confirm it.

**SAW `summarize_verification` [V]**
- 0.6 added experimental "verification summaries".
- 0.7: `summarize_verification` "will print a list of all functions or methods verified or assumed", with status and provers. `-f json` gives output "for consumption by other tools".
- 0.8: the `admit` tactic takes a `String` reason and replaces `assume_unsat`/`assume_valid`.
- 0.9: the `-s` summary has more detail, and a `verif-viewer` tool converts the JSON to GraphViz.
- 1.4 (2025-11-18): `--detect-vacuity` correctly reports contradictory specs on LLVM, MIR and JVM.
- 1.6 (2026-09-17): `assume_unsat` is deprecated; "Use `admit` instead."
- Unreleased "next": the summary "reports which MIR functions were analyzed".
- Source for all of the above: [saw-script CHANGES.md](https://raw.githubusercontent.com/GaloisInc/saw-script/master/CHANGES.md)
- The admitted/assumed status of `llvm_unsafe_assume_spec` overrides is what makes this a ledger. Each entry is either verified or assumed, and admits carry their reason string.
- Gap: I did not fetch the JSON schema itself. Look in `saw-script` `src/SAWScript/` for a VerificationSummary module, and in the `verif-viewer/` directory.

**Lean 4 [V for 4.35, T for #print axioms]**
- `#print axioms foo` [T] prints `'foo' depends on axioms: [propext, Classical.choice, Quot.sound]` or `'foo' does not depend on any axioms`. A `sorry` shows up as `sorryAx`. This is a text message, not a file.
- **New in Lean 4.35.0 (2026-10-12):**
  - `lake check` (#14990) "builds the default targets of the current project, exports them, replays the export through the kernel" and "fails if anything uses an axiom other than the standard ones".
  - `lake comparator` (#14885, #15146; renamed from `lake challenge`) checks that each named theorem in the solution "proves the same statement as in the challenge", with permitted axioms and kernel acceptance. It reads `comparator.json` by default (#15147).
  - `--paranoid` (#15145) runs every bundled checker and accepts only if all of them accept: lean4lean (#15048), nanoda (#15099), con-leche (#15130), con-ron (#15153), and `leanchecker-paranoid` (#14884, a hardened allocator).
  - `--from-export`, `--solution-from-export` and `--challenge-from-export` (#15157) check pre-built NDJSON exports, "third-party exports" among them.
  - `leanchecker --from-export file.ndjson` (#15050).
  - The bubblewrap sandbox (#15005) is Linux-only.
  - #14953 removes the `Lean.reduceBool`, `Lean.reduceNat` and `Lean.trustCompiler` axioms, because they "made whole-environment axiom checks such as `lake check` less meaningful". `native_decide` therefore no longer leaves a trustCompiler entry. Check what replaced it.
  - The notes describe no JSON report or exit-code contract. The outcome is only "accept" or "fails".
  — [Lean 4.35.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
- The highlights and the #15145 entry disagree on whether con-ron is part of `--paranoid`. — [release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
- Blog: con-leche is written in Lean and proven consistent relative to Carneiro's set-theoretic model. con-ron is a Rust translation with an Aeneas refinement proof. lean4lean's verification is "expected to finish in the next few months". `--inadvisably-no-sandbox` disables the sandbox. — [de Moura blog, 2026-10-15](https://leodemoura.github.io/blog/2026-10-15-lean-now-ships-with-verified-kernels/)
- The standalone comparator repo is archived and "merged into Lean core as of v4.35.0". Its config takes `challenge_module`, `solution_module`, `theorem_names`, `permitted_axioms`, `definition_names` and `external_kernels`. — [leanprover/comparator](https://github.com/leanprover/comparator)
- Community gap: Lake v4.35.0 has no compare-only mode, so a passing comparison always goes on to the kernel replays. — [lean-pkg issue #280](https://github.com/lean-pkg/lean-pkg/issues/280) (secondhand, third-party)
- lean4export: NDJSON, **format version 3.1.0**.
  - The `meta` header carries `exporter{name,version}`, `lean{githash,version}` and `format{version}`.
  - It contains Name/Level/Expr records with integer indices, then decls of kind axiom, def, thm, opaque, quot and inductive.
  - Options: `--export-unsafe`, `--export-mdata`.
  - No explicit stability guarantee.
  — [format_ndjson.md](https://raw.githubusercontent.com/leanprover/lean4export/master/format_ndjson.md), [lean4export](https://github.com/leanprover/lean4export)

**Rocq/Coq [T]**
- `Print Assumptions foo.` prints `Closed under the global context`, or sections such as `Axioms:` (`name : type` lines), `Section Variables:`, and notes on constants that rely on type-in-type, unsafe fixpoints or positivity bypass.
- `Print Assumptions` covers transparent and opaque dependencies. There is also `Print Opaque Dependencies`.
- `coqchk -o` prints a "CONTEXT SUMMARY" of axioms and of constants that rely on unsafe flags.
- All of this is text with no JSON. `admit`/`Admitted` show up as axioms.
- `.vo` files are binary and version-locked, so they are not a third-party format.

**F* [T]**
- `--report_assumptions` reports uses of escape hatches: `assume`, `admit`, `assume val` and `--admit_smt_queries`.
- `.checked` files are binary caches tied to the F* build, so they are not consumable.
- `.hints` files are JSON with Z3 unsat-core hints. They help replay but do not state what was assumed.

**Isabelle [T]**
- The `thm_oracles` command lists the oracles a theorem depends on. `sorry` appears as the `skip_proof` oracle.
- `isabelle build -o export_theory` and `isabelle export` give the theory content.
- The output is text, or theory exports through the build database.

**Verus [V]**
- No listing command. `--no-cheating`: "Do not allow assume, admit, verifier::external_body, and assume_specification". It gives a yes/no answer for the whole crate. — [rust_verify/src/config.rs](https://github.com/verus-lang/verus/blob/main/source/rust_verify/src/config.rs)
- `-V axiom-usage-info`: "Print usage info for broadcasted axioms, lemmas, and groups". It covers broadcast axioms only, not external_body. — [config.rs](https://github.com/verus-lang/verus/blob/main/source/rust_verify/src/config.rs)
- There is no `--emit` option in config.rs. — [config.rs](https://github.com/verus-lang/verus/blob/main/source/rust_verify/src/config.rs)

### Inferences
- These are the best candidates for a receiving parser. Each one carries an assumption list or a diffable verdict.
  1. **Dafny audit, `md-table` output plus `--compare-report`.** It is closest to the existing Jasmin accept.expected flow, because the tool itself diffs the report.
  2. **SAW `-s file -f json`.** Per-method entries say verified or assumed, with provers and admit reasons.
  3. **Lean `lake check` exit status plus `#print axioms`.** The cleanest "kernel-rechecked, only standard axioms" claim. The project is itself Lean, so it could also import the NDJSON export (v3.1.0) and compute axiom closure itself instead of trusting text.
- For Verus, the only cheap signal is "`--no-cheating` passed". A real ledger needs scanning for `#[verifier::external_body]`, `assume(`, `admit(` and `assume_specification` in source, or in a `--log vir` dump.
- Rocq, Isabelle and F* reports are text-only. They would need a scraper, like the Jasmin case.

### Gaps
- Example output from `dafny audit` in md-table form was not in the docs. Run it once and capture.
- The SAW JSON schema was not fetched.
- Lean `lake check` has no documented machine-readable report format.
- I did not re-verify the F* `--report_assumptions` flag name or Isabelle `thm_oracles` this session.

## Q2: What is new from Aug to Oct 2026 on this front?

### Takeaway
The big change is Lean 4.35.0 (2026-10-12). Comparator moved into Lake as `lake check` and `lake comparator`, five independent kernels ship with it, and it can check third-party NDJSON exports. SAW 1.6 (2026-09-17) pushes everyone onto `admit` with reasons. Jasmin 2026.09.0 and CN's recent commits add no certificate output.

### Cited Findings
- Lean 4.35.0: see Q1. Released 2026-10-12. — [release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
- SAW 1.6 (2026-09-17): `assume_unsat` is deprecated in favour of `admit`. Unreleased: the summary lists the MIR functions analyzed. — [CHANGES.md](https://raw.githubusercontent.com/GaloisInc/saw-script/master/CHANGES.md)
- Jasmin releases:
  - 2026.03.0 (Mar 9) makes square brackets mandatory around annotations.
  - 2026.03.2 (Jul 16) adds `overlay`, `callee_saved` and `required_alignment` annotations.
  - 2026.09.0 (Sep 30) adds "preliminary support for safety assertions".
  - No release mentions SCT output format, signatures, certificates or JSON.
  — [Jasmin releases](https://github.com/jasmin-lang/jasmin/releases)
- CN: no GitHub releases at all ("There aren't any releases here"). — [CN releases](https://github.com/rems-project/cn/releases)
  - Commits from Sep 16 to Oct 22, 2026 show work on Fulminate (runtime checking) and flexible array members.
  - On 2026-09-16 Lean CN_Lib source files were added to the repo, along with "Update Lean lemma tests" and ownership predicates for integer types ("Lean only"). This means CN now exports lemma obligations to Lean as well as Rocq.
  - No commit mentions JSON reports or trusted-function listings.
  — [CN commits](https://github.com/rems-project/cn/commits/main)

### Inferences
- The CN Lean lemma export is still the obligation direction. CN emits goals to discharge, not a verdict. The earlier conclusion ("CN does not emit a certificate") stands.
- Starting in October 2026, a Jasmin "safety assertion" may become a new trusted item. Watch the next release for checker output.
- Lean's `--from-export` accepting third-party NDJSON is directly relevant. Any tool that produces a Lean export, such as Aeneas or hax output once built, can now be rechecked by five kernels without trusting the producer's build.

### Gaps
- I did not check Aug–Oct 2026 changelogs for Verus, Kani, Dafny, Creusot, hax, Charon/Aeneas, F*, CBMC, Frama-C, Rocq or Isabelle. The tool-call budget ran out, so treat these as unknown, not as "nothing new".
- The CN commit page showed only Sep 16 onward, so August 2026 is uncovered.

## Q3: Which outputs are stable and versioned enough for a third-party program to consume? (per-tool format entries)

### Takeaway
Explicitly versioned and machine-readable:
- Kani `kani-list.json` (`file-version: "0.1"`)
- lean4export NDJSON (format 3.1.0, version in the header)
- Dafny audit, which is self-diffing through `--compare-report` but marked "under development"

Documented as for other tools but unversioned: SAW JSON summaries.

Not stable:
- Verus `--output-json`, whose JSON is results and timing
- Charon LLBC, "beta" with breaking changes planned
- binary caches: Rocq `.vo`, F* `.checked`, Lean `.olean`

### Cited Findings
- **Kani [V]**
  - `cargo kani list` / `kani list <FILE>` takes `--format [pretty|markdown|json]` and `--std`. By default it lists manual harnesses only. The experimental autoharness `--list` adds generated harnesses. — [Kani book, list](https://model-checking.github.io/kani/reference/list.html)
  - The JSON goes to `kani-list.json` and has this shape: `{"kani-version", "file-version": "0.1", "standard-harnesses", "contract-harnesses", "contracts": [{function, harnesses, ...}], "totals": {"standard-harnesses", "contract-harnesses", "functions-under-contract"}}`. — [kani-driver/src/list/output.rs](https://raw.githubusercontent.com/model-checking/kani/main/kani-driver/src/list/output.rs)
  - What it asserts: an inventory of which harnesses and contracts exist. It does not record verification results, stubs or unwind bounds.
  - [T]: the verification results come only as `--output-format regular|terse|old` text, with `VERIFICATION:- SUCCESSFUL` per harness. Stubs (`#[kani::stub]`, `stub_verified`) and `#[kani::unwind(N)]` are visible only in source or in the harness attributes.
- **Verus [V]**
  - `--output-json`: "Emit verification results and timing as json". `--version --output-json` gives the version as JSON. — [config.rs](https://github.com/verus-lang/verus/blob/main/source/rust_verify/src/config.rs)
  - The Verifier tracks `encountered_error`, `encountered_vir_error`, `count_verified`, `count_errors`, `func_fails`, `func_times` and `func_details`. `FuncDetails` serializes `obligation_proof_notes` and `failed_proof_notes`. When `output_json` is false, the text form is `verification results:: N verified, M errors`. — [verifier.rs](https://raw.githubusercontent.com/verus-lang/verus/main/source/rust_verify/src/verifier.rs)
  - What it asserts: counts and failures. No assumption list, no schema version.
  - I could not locate the exact JSON keys. [T] They are roughly `{"verification-results": {"encountered-vir-error", "success", "verified", "errors", "is-verifying-entire-crate"}, "times-ms": {...}}`.
- **Charon/Aeneas [V for Charon]**
  - Charon writes `crate_name.llbc` JSON with `crate_name`, `type_decls`, `fun_decls`, `global_decls`, `trait_decls` and `trait_impls`. Rust reads it through `charon_lib::export::CrateData`, and OCaml through `charon-ml`.
  - The project calls itself "beta software" with "a number of breaking changes in its API ... planned". Its limitations are in `docs/limitations.md`.
  — [Charon README](https://github.com/AeneasVerif/charon)
  - Aeneas [T]: the generated Lean puts opaque or external functions in `FunsExternal_Template.lean` as `axiom`s. Once built, `#print axioms` or `lake check` exposes them, which makes this the natural route to an assumption ledger.
- **hax [T]**
  - It emits F*, Rocq, SSProve or Lean files. Assumptions show up as `assume`/`admit`, `--admit` or `#[hax_lib::opaque]` / `hax_lib::assume!` in the backend files. There is no dedicated JSON verdict that I know of.
  - libcrux checks the F* output in CI with `--admit_smt_queries` off per module, using an admit list in the Makefile. Unverified.
- **Creusot [T]**
  - Proofs are stored as why3find `proof.json` files, which replaced `why3session.xml`, next to each module. These are proof-replay caches, not verdicts. Trusted items are `#[trusted]` and `extern_spec!`.
- **CBMC [T]**
  - `--json-ui` gives a JSON array of messages, including `{"result": [{"property", "status": "SUCCESS"|"FAILURE", "description", "sourceLocation"}]}`. `--xml-ui` is the alternative.
  - Assumptions are `__CPROVER_assume` calls and unwind settings (`--unwind`, `--unwinding-assertions`). Those settings are command-line context and are not echoed as a ledger.
- **Frama-C WP [T]**
  - `-wp-report-json <file>` writes per-goal status JSON. The Report plugin offers `-report-csv` and `-report-json`, giving the consolidated property status, including properties that are "considered valid" or have no proof. The [WP plugin page](https://www.frama-c.com/fc-plugins/wp.html) did not document these options. The WP manual is the source. Unverified.
- **Rocq, F*, Lean caches [T]**
  - `.vo`, `.checked` and `.olean` files are binary and tied to compiler versions. None is a third-party interchange format.
  - Lean's sanctioned interchange format is the lean4export NDJSON (v3.1.0), see Q1.

### Inferences
- Ranked by consumability for an assumption ledger:
  1. Lean NDJSON export: versioned, and the axiom closure can be computed independently.
  2. Dafny audit: assumption-specific and self-diffing.
  3. SAW JSON summary: verified or assumed per method.
  4. Kani list JSON: versioned, but an inventory only.
  5. Verus JSON: results only, so it must be paired with a source scan or `--no-cheating`.
  6. CBMC and Frama-C JSON: per-property status, with no trusted base listed.
  7. Text-only reports from Rocq, Isabelle and F*: need scrapers.
- For Kani, the trusted base (stubs, unwind bounds, `stub_verified` contracts) is not in any emitted artifact. Something like the project's existing `cross-check/leak-kani` capture would have to derive it from harness attributes.

### Gaps
- I did not fetch the exact Verus JSON keys, the SAW JSON schema, the CBMC/Frama-C JSON schemas, the Creusot proof.json format, or any hax CI artifacts. These need follow-up, either by cloning the sources or running the tools locally.
- Stability or versioning promises for the SAW JSON and Verus JSON were not found.
