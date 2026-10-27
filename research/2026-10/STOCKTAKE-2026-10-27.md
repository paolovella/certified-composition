# Stocktake, 2026-10-27: where L stands, where it is aimed, and the case against

*Measured on `g0/checker-lock` (= master after the 2026-10-27 merge). The plan of record is
`PLAN-2026-10.md`. `PLAN-2026-08.md` and `PLAN-MULTITOOL.md` are history, read here as the strongest
arguments against it. Every number below is from a file in the repo or a receipt.*

## 1. The aim, in one paragraph

**L** is a standalone, AI-native secure language whose compiler carries every certificate down to
RV64IM bytes. Programs are proof-carrying: they are validated, never inferred. Certificates come in
three shapes (`trace`, `rel`, `bound`) over one observation `Beh`. Passes are `PassCert`s whose
leakage and cost transformers compose, so proof cost is O(N·(C+P)), not O(N·C·P). Agents extend it
on green. A Ring 0 core (≤ ~2.5k LOC) and the gates change only with the user's key, under a
standing challenge engine. The exit that matters is Phase 5: the first `Artifact_<hash>` whose
`binary_carries` theorem is kernel-checked and whose binary, run under QEMU/Spike, matches the
predicted events, cost and return values. The plan estimates **45–65 sessions** to get there.

## 2. Where we are

### Phase 0 (bulletproof build): done except four items

| Item | Status | Evidence |
|---|---|---|
| 0.1 axiom manifest | done | `tools/axioms.expected`, 3444 lines; 185 claims held, 3 corrected |
| 0.2 Lean 4.35 + `lake check` | done (closes on this merge) | 1 of 96 modules broke; all four toolchains on v4.35.0 |
| 0.3 frozen statements | done | 25 statements, comparator, `ring0.lock` (390 definitions of meaning) |
| 0.4 witness registry | done | 37 checkers found, each with an accepted and a refused witness |
| 0.5 rule mutants | done | 318/318 killed |
| 0.6 hard-failing CI | **open** | base gate built and witnessed (15 cases). Branch protection, the heavy runner, the live weakening-PR test and the key mechanism are pending |
| 0.7 claim records | **not started** | |
| 0.8 open cells | done | Kani: no accepted 5-node program leaks (MAXITER 2), non-vacuous; aborting runs ledgered |
| P0-11 checker limit | done | checker edits pass without the key, ≤ 3 per change |
| P0-12 boundary warden | **open** | built and live-witnessed (cleared an equivalent rewrite, escalated a collapse); waits for its first run on GitHub |

Spikes: S-435 (bump in place), S-KERNEL (kernel evaluation feasible for passes to ~2k nodes, not
for a text parser), S-SAIL (proof route, with conditions: ADDI and BEQ proved, LD stated) are done.
S-OBS, S-PRIM and S-COST are not started.

### The language, the compiler, the core: not started

- `l-core/` does not exist. Ring 0 v1 (`Obs`, `Lang`, `Cert`, `PassCert`, `Core`, `Wire`, `RV`,
  `Contract`) is 0 lines.
- Certificates still live over **13 separate languages** (96 modules, 1328 theorems in
  conf-typing and transport-calculus).
- **The abort-in-a-loop defect is still in the semantics** (`uexec_dead_loop_diverges`).
  Completed-run certificates are vacuous on those runs until Phase 3's halting abort.
- No code generator exists. The P1 sketch (`CMP-P1`) is not on its branch yet.
- `AUTONOMY` = `off`. The §7 mechanics that `cells-only` needs are partly missing: the tier
  classifier and type manifest, auto-revert, kill-switch auto-downgrade, and claim records.

### What Phase 0 cost

The plan budgeted 6–9 sessions for Phase 0. It took five calendar days (2026-10-23 to -27), and
added work the plan did not list: P0-09 to P0-12, a history rewrite, and several corrections of
record. The process now has teeth it did not have:
- **A PR cannot rewrite its gate.** Witnessed.
- **The axiom claims are checked.** 185 held and 3 were corrected; before P0-01 none were checked.
- **The loop search finished.** It had died silently in August; I-0001 is resolved.
- **A weakened statement is refused,** whether by its text (comparator) or by its definitions
  (lock).

## 3. The distance, phase by phase

| Phase | Exit | Plan's sessions | Blocking unknowns |
|---|---|---|---|
| 1 Spine | `ucmd_p1_carries` with zero certificate-specific pass proofs | 6–9 | S-OBS: JSecTy with addresses moved into the leakage (`uLowEqA` equates `freed`/`hlab`/`fresh`) |
| 2 Engine | `cells-only` on | 5–7 | flake rate; claim records (P0-07) |
| 3 L core v1 | Ring 0 v1 frozen with the key; 13 languages → 1 | 10–14 | S-PRIM: table-dispatched semantics; kernel speed of `Wire` decoding |
| 4 Back end P2–P7 | `core_to_asm_carries` on the corpus | 12–18 | speculation (`specT` at P3/P6 is research-level) |
| 5 Bytes | first certified binary that runs and matches | 6–10 | S-SAIL's loads and stores; RvfiDii takes 1794 s to build; kernel compile time at program scale |
| 6 Scale | multi-function program linked with a foreign certificate | 6–10 | contracts, `link_correct` |

That totals about 45–65 sessions, as the plan says. In Phase 0, unlisted work (four of twelve
P0 items) was a third of the items, so expect the later phases to grow too.

## 4. The case against, from the repo's own plans

Each argument below was made seriously in an earlier plan. Each is followed by PLAN-2026-10's
answer, then by what still stands.

**4.1 "This is the Jif path" (PLAN-2026-08 §2.4, §4 Option 1, rejected).** New IFC languages died
of annotation burden and false positives. The 2026-08 plan rejected "keep building the language" as
"the Jif path with a decade less funding".
- *2026-10's answer:* the authors are AI agents, so annotation burden is free. Programs carry
  witnesses and are never inferred.
- *What still stands:* that answers the burden, not the **false-rejection rate**. The only
  measurement is 30 tasks (stage 2k): 17% inexpressible, and 8% of the expressible ones falsely
  refused. Nothing since has re-measured it. An agent that cannot get a true program accepted is
  as stuck as a human. The plan's own metric for this, the witness-expressiveness gap on external
  tasks with a sealed holdout (§8), does not exist yet. **Until it does, the central bet of L is
  unmeasured.**

**4.2 "There is no property on which we lead; the asset is the algebra" (PLAN-2026-08 §3).** The
two things judged novel were the checked composition algebra (`Bridge.pair_comp_cert`, componentwise
with no interaction term) and the trusted base computed from the artifact (`needs`, `Ledger`).
- *2026-10's answer:* both survive inside L. `PassCert` transformers compose, and at link time
  the ledger is the union (`link_correct` via `Bridge.comp`), so certified composition becomes the
  linker's semantics.
- *What still stands:* that arrives in **Phase 6**, the last phase. Phases 1–5 compete property by
  property with Jasmin (CT, SCT preservation), CN/VST (memory) and CompCert, where 2026-08 judged
  the repo "far behind". The differentiator is scheduled after the parts where the repo is weakest.

**4.3 "A proof is only as good as its model" (PLAN-MULTITOOL §1).** `leakSafe_sound` is about
`uexec`; if `uexec` is wrong, the theorem is beside the point.
- *2026-10's answer:* Ring 0 includes an RV model linked to Sail, plus a model-gap hunter and
  QEMU/Spike differential runs.
- *What still stands:*
  - The Sail link is ADDI and BEQ only. Its 75 externs are `opaque`, which is trust, not proof.
  - The hardware contract (Zkt, no secret `div`) is an assumption.
  - The Kani result says something about 5 nodes and two loop iterations, and nothing more.
  - None of the hunters run yet. Today the model is checked by one independent
    implementation (the Rust port) at one bound.

**4.4 "Gates are not the product" (implicit in 2026-08's stage list, which measures first).** The
last five sessions built gates, locks, mutants, a warden and a history rewrite, and 0 lines of L.
- *2026-10's answer:* gates come first and are non-negotiable, because autonomy without them
  would merge agents' mistakes faster.
- *What still stands:* the plan's own **stagnation alarms** (§8) would fire now:
  - mutant kill rate is 100% (the alarm is "100% for 4 cycles ⇒ operators too weak");
  - the corpus (`conf-typing/corpus/`) has not changed since 2026-08-14;
  - no external task has come in for over 14 days.

  The oldest-open-cell alarm (21 days) does not fire yet: CMP-P1 was filed on 2026-10-23,
  although the sketch it adopts has existed since August.

  The alarms exist to stop exactly this drift toward the comfortable work.

**4.5 Goodhart on the evolution process (PLAN-2026-10 §9 against itself).** Ratchets count
selftest cases (76), mutants (318) and witnesses (37 checkers). Every count went up this week, and
none of them measures whether L can express a real handler. 2026-08 §1.1 said the tests were
"rigged": every program was written after the rule that certifies it. That is still true of every
program in the repo.

**4.6 The threat model just changed.** The repo became public on 2026-10-27. The 2026-10 plan
assumed a private repo ("exposure is not a concern"). Now:
- fork PRs reach the gate;
- the warden can be made to spend tokens (forks are refused, but same-repo spam is not capped);
- the self-hosted heavy runner must never take a fork's job (`gate.yml` already refuses that);
- everything in history is public, which is why the trailers were rewritten first.

**4.7 The fallback rules have not been tested against their triggers.** Each phase has a kill rule.
Only Phase 0's fired-or-not check has been run (S-435: 1 of 96 modules broke, against a 10%
threshold). The riskiest, S-OBS for Phase 1, is unstarted. If it fails, the fallback is a
public-only allocator, a language restriction the user has not been asked about.

## 5. What would answer the case against, cheapest first

1. **Measure the bet (answers 4.1 and 4.5).** Re-run the corpus measurement on the current
   checkers. Then seed a sealed holdout of external tasks (CWE-derived, written blind). This needs
   no Ring 0 work and gives the first real number for L's premise. It is a few sessions.
2. **Start Phase 1 with S-OBS (answers 4.7).** It is the riskiest spike and decides the
   allocator. Then do CMP-P1 (the oldest open cell) and `Obs`/`Lang`/`Cert`/`PassCert` in
   `l-core/`.
3. **Close Phase 0's tail in parallel:**
   - P0-06: branch protection, the live weakening PR, the heavy runner, and the key mechanism.
   - P0-12: the first GitHub warden run.
   - P0-07: claim records.
4. **Turn on the stagnation alarms (answers 4.4)** before turning on any autonomy, so drift toward
   process work is a mechanical signal and not something a stocktake has to catch.
5. **Bring the composition asset forward (answers 4.2).** State `link_correct` and the ledger
   union in Phase 1's `PassCert` terms now, even if it is proved later, so the differentiator is
   in Ring 0 from v1.

## 6. Decisions only the user can make

- Whether L's premise (4.1) gets measured before more is built on it.
- Whether to accept a public-only allocator if S-OBS fails.
- Raising `AUTONOMY` above `off`. The plan allows `cells-only` once §7's mechanics exist; most
  of them do not exist yet.
- The key mechanism for G-0 (proposed: signed commits checked against `allowed_signers` on
  master).
- Registering the heavy runner, and filing the upstream Lake/nanoda issue.
