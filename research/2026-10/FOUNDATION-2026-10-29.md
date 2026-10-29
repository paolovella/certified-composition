# Foundation first (2026-10-29)

## 0. The goal this serves

The goal: a coding framework that is bulletproof by construction, where "it can't break
security" holds relative to a stated model, spec and trusted base. L is the vehicle. It is a
language that countless agents use and extend, on a small frozen foundation that no party can
exploit (PLAN-2026-10, Context).

So the foundation is solid exactly when **no party can get an insecure program certified**. The
parties are:
- a careless or adversarial program author;
- an agent extending L with a new pass, checker or primitive;
- an agent touching the gates;
- the model itself, when it claims more than it covers.

Everything below is measured against those four. Elegance of the kernel is not a criterion.

The user's verdict on Phase 1 was: slow, disconnected, incomplete, above all shallow. Section
1 checks it against the repo. PLAN-2026-10 stays the plan of record. Where this plan departs
from it, it says so and answers the counter-argument (section 4).

## 1. How each party could exploit the foundation today

**A1. A program author gets a vacuous certificate.**
- A `Lang` has no laws. `run : Nat → Prog → In → Beh` can be any function. Nothing says more
  fuel extends a run, or that a finished run stays finished.
- `Cert.lean`'s docstring claims "a fuelled run that stops early is a prefix". That is checked
  nowhere, and it is false for UCmd: `ucmdLang` reports an out-of-fuel run as an empty record.
- So a program that never finishes satisfies every `trace` certificate (`mediated π []`) and
  every `bound` (cost 0 ≤ k), whatever it does.
- This is the same hole PLAN-2026-10 names as its first design defect: an abort inside a loop
  diverges (`uexec_dead_loop_diverges`), and "completed-run certificates are vacuous on such
  runs". The kernel was meant to close it and does not: Phase 1 rebuilt the hole one level up.
- UCmd's counted loops happen to terminate, but no theorem says so (`uexec` has no fuel
  monotonicity lemma; only `wexec_mono` exists).

**A2. A pass author ships a compiler that drops the guarantee.**
- `rel_transfer` concludes `T.run m p' (enc i) = T.run m p' (enc i')`: a fact about the images
  of source inputs only. The target's `lowIn` is never used.
- Target inputs outside `enc`'s image are unconstrained. So the deployed binary, run on an
  input no source input encodes to, carries no certificate at all. That is precisely the input
  an attacker chooses.
- `trace_transfer` and `bound_transfer` have the same limit. Pipelines compose only through
  `seq`, never as certified programs in their own language.
- The one pass built, P1, is a renaming: `texec` mirrors `uexec` step for step. It never
  tested the case real lowering produces, where one source step becomes many target steps.
  `Pass.lean` defers that ("the laws will be added when a pass needs them").

**A3. An agent weakens what everyone trusts.**
- `tools/ring0.lock` holds 0 `LCore` names, and none of the 24 frozen statements
  (`workspace/Statements.lean`) mentions `LCore`. They freeze toy checkers' soundness, not L's
  meaning.
- The kernel is protected only by a path rule. Today's `seq` rewrite passed
  `ring0-lock --check` unchanged.
- Nothing ties a certificate claim to the kernel. A Ring 1 file can define its own weaker
  `rel` or `trace` and state "certified" theorems with it, without touching
  `LCore/Kernel/`. Neither the lock nor any frozen statement would notice.
- The key mechanism (P0-06) is undefined, and the warden (P0-12) has never run on GitHub.

**A4. The model claims more than it covers.**
- `VULN-COVERAGE.md` maps 14 vulnerability classes to theorems, but over 15 separate toy
  semantics (`aexec` … `wexec`). Only UCmd is an L `Lang`. For L, today, the map's
  "proved" means "proved in a different language".
- `Ev.release`, `Ev.ext`, `Lk.vtime` and `Lk.ext` are produced by no language. So
  declassification and variable-time leakage have kernel syntax and no tested meaning.
- `transport-*`, the Verus, Kani and Alloy cross-checks, the Rust port and `certcompose`
  have no stated relation to any L claim. A reader can believe their results apply to L, and
  nothing stops it.
- Out of scope for this plan, and named so it isn't forgotten: pointers are `Int`s and integers
  are unbounded. That is a model gap closed by PLAN-2026-10's L core (`W64`, PH3), after this
  foundation.

**And slow:**
- The only loop is the full CI: 954–1037 s, with no per-step timing.
- Kernel PRs went to the key before the kernel's design was settled, so each redesign costs
  another round trip, as `seq` just did.

## 2. "Solid", as checks

Each criterion is checked by a guard, manifest or witness, not stated. Each one closes the
attack with the same number.

- **S1 (A1). Certificates cannot be vacuous.**
  - `Lang` carries fuel laws: prefix-monotone events and leakage, monotone cost, finished
    runs stable.
  - `trace` and `bound` speak about every prefix, so a never-finishing run that reads a
    forbidden resource *violates* `trace (mediated π)`.
  - Vacuity witness, which fails today and must hold after: a diverging program that reads
    a forbidden resource is not `trace`-certified.
  - An unlawful language cannot be presented as a `Lang`.
- **S2 (A2). Certificates land on what runs.**
  - Transfers conclude `Cert.trace T Φ p'`, `Cert.rel T p'` and `Cert.bound T k' p'` over
    *all* target inputs, in the target's own `lowIn`.
  - Refusal witness: a pass whose `enc` misses a target input on which the program leaks is
    refused.
- **S3 (A2). The hard pass.**
  - One pass where one source step becomes several target steps (UCmd expressions to stack
    code) is a `PassCert` with zero certificate-specific proofs.
  - If that is impossible, the central claim (PLAN-2026-10 §6) is false. Better to learn it
    now than after 8 passes.
- **S4 (A3). The meaning is locked.**
  - The kernel's laws, certificate definitions, transfer and composition statements are
    `Frozen.` statements, and `ring0.lock` covers their closure.
  - A weakened kernel statement is refused by witness, as the comparator witness refuses a
    weakened `Frozen.` theorem today.
  - The kernel merges once, with the key, after S1–S3 hold.
- **S5 (A4). The vulnerability map is about L.**
  - Each `VULN-COVERAGE` row marked IN either names a `Cert` instance on a lawful L `Lang`
    (with the adequacy theorem tying the old checker to it), or is downgraded to "proved for
    toy language X", in a correction of record.
  - Every `Ev`/`Lk` constructor is produced by a language with a tested certificate, or is
    removed.
  - Each island has a row: an L claim it checks plus the CI step that checks it, or the label
    "history / Ring 3". A guard keeps the map and the island table current.
- **S6. A fast loop.**
  - A quick tier under 2 minutes for every iteration.
  - Per-step timing in every full run, with a ratchet (P0-14).

## 3. Work, in order

Each item becomes a backlog entry with plan, acceptance and kill rule before any code.

| # | Item | Closes | Ring | Acceptance | Kill rule |
|---|---|---|---|---|---|
| F0 | **Stop and correct.** Freeze PH2 and PH3. Hold #14 (kernel) and #15 open, unmerged. Corrections of record: `Cert.lean`'s unchecked prefix sentence; "Phase 1's exit is met" in CHANGELOG and PH1 (met in letter; the certificates it carries are vacuous on non-finishing runs and do not reach target inputs outside `enc`). | — | 0 (docs) | corrections struck through, with reasons; guard on the "prefix" claim | — |
| F1 | **Fast loop** (P0-14 steps 1–3 and `ci.sh --quick`). | S6 | 0 | quick < 120 s; per-step table; ratchet witness fires | timing spread > 30%: timings stay informational |
| F2 | **Lawful `Lang`, non-vacuous shapes.** `Lang.Lawful`; prefix semantics for `trace`/`bound`. `ucmdLang` reports the real prefix of an out-of-fuel run, via a prefix-reporting `uexec` variant proved equal to `uexec` on finished runs (`uexec` is locked meaning, so it is not edited). `ucmdLang` proved lawful. | S1 | 0 + 1 | vacuity witness flips; unlawful toy refused; `bcheck_lcore` re-proved | the variant cannot match `uexec` on finished runs: G-0 item on the locked meaning, stop |
| F3 | **Certificates land on the target.** Try (a) a decoding `dec : T.In → Option S.In` with laws, low-equality preserved both ways, and a certified behaviour for undecodable inputs (refuse or abort); or (b) admissible inputs carried by `Lang`. Choose on P1 *and* F4. | S2 | 0 | transfers conclude `Cert.X T …`; certificate-level composition theorem; refusal witness | neither design fits both passes: write up the obstruction, which amends PLAN-2026-10 §2 |
| F4 | **The hard pass.** UCmd expressions to stack code, on the F2/F3 kernel, with the fuel laws it forces. | S3 | 1 | `bcheck`'s three certificates arrive by transfer alone (guard (m) extended); budget transformed non-trivially | certificate-specific proofs needed: §6 fails, stop and report |
| F5 | **The map onto L.** For each `VULN-COVERAGE` IN row, in order of severity: a lawful `Lang` for its semantics and an adequacy theorem, or a downgrade by correction of record. Produce or remove the unused `Ev`/`Lk` constructors. The island table. Ring 1, parallel across agents once F2–F3 are stable. | S5 | 1 (+ docs) | every IN row names an L `Cert` or is downgraded; guards on map and table | ≥ 3 rows misfit the same way: the three shapes need a fourth (declassification, or hyperproperties beyond `rel`), redesign before F6 |
| F6 | **Lock the meaning; merge the kernel once.** `Frozen.` kernel statements; `ring0.lock` covers `LCore`; decide whether the 24 toy statements stay frozen or are restated as F5 `Cert` instances. | S4 | 0 | weakened kernel statement refused; one key merge | — |
| F7 | **The gates F relies on.** P0-06's key mechanism, then the heavy runner; P0-12's first live warden run. | S4 | 0 | as in P0-06, P0-12 | — |

Order: F0 → F1 → F2 → F3 → F4 → F5 → F6. F7 runs alongside, whenever the user can act.

## 4. Counter-arguments, and the answers

- **"PLAN-2026-10 puts the engine (Phase 2) next."**
  - The engine automates merging changes onto a foundation that A1–A4 can exploit. That
    multiplies the hole: many agents, auto-merge on green, green that means less than it says.
  - Of PH2, only the fast loop and the timing ratchet are needed now. They are F1.
- **"Add the laws when a pass needs them" (`Pass.lean`'s docstring today).** Right for getting
  the spine to build, wrong for a Ring 0 kernel. Once locked, each law is a key round trip and
  a re-proof of every pass. F4 makes the first pass that needs them come before the lock.
- **"PH3 retires the toy languages anyway; adapting them is busywork."** They hold the only
  evidence for the claim the whole goal rests on: that three shapes and one observation
  express "no vulnerability of class X". PH3 would fold 14 languages into one core whose
  observation is exactly the untested part. F5 is that test, and its kill rule is what makes it
  worth running.
- **"The kernel is 216 lines; laws will triple it."** Ring 0 is budgeted at about 2.5k lines
  (PLAN-2026-10 §1). Size is not the risk. Vacuity is.
- **"More frozen statements make the user a bottleneck"** (the ring0.lock concern of
  2026-10-27). P0-11 already keeps checker edits key-free. F6 locks what L actually trusts, and
  once S1–S3 hold it should change rarely.
- **"This delays reaching RISC-V bytes."** A certificate that is vacuous at the source, or
  missing at the target, is just as vacuous in bytes. The compiler is only worth carrying
  certificates down once they mean something.

## 5. Work in flight

- `ph1/spine` (#14) and `ph1/ucmd-lang` (#15), green on both branches, are F2–F3's starting
  point. The `seq` fix (c6c3db2, merged into #15 as 12fbe9c) stays.
- The CI item drafted today (P0-14) becomes F1.
- PH1 stays in progress, its exit restated as S1–S3.
