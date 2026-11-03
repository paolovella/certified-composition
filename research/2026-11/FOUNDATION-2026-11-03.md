# The foundation is not solid enough to deliver: vertical slice first (2026-11-03)

The user's verdict of 2026-11-03: "our foundation is not solid enough to keep up and deliver with
promises". The user's decision: hold the lock, and build one vertical slice first.

`PLAN-2026-10.md` stays the plan of record for where L is going. This note changes the order of work,
as [`FOUNDATION-2026-10-29`](../2026-10/FOUNDATION-2026-10-29.md) did. Item: [`VS-1`](../../backlog/VS-1.md).

## 1. Measured against the repo's own test

The test, from 2026-10-29: the foundation is solid exactly when no party can get an insecure program
certified.

| Party | The promise | Today, 2026-11-03 |
|---|---|---|
| Program author | a certificate holds for what runs | Nothing runs. No RISC-V model is in the kernel, and there is no compiled output. Integers are unbounded and pointers are `Int`s, so certificates describe a machine that does not exist |
| Agent extending L | cannot redefine what "certified" means | The lock names `ucmdLangS` and `ucmdLangT`. `ucmdLangI`, `ucmdLangW`, `ucmdLangH` and `splitPass` are outside it. The "on L" guard, check-claims (q), checks that a named theorem exists, not that its language is faithful to L |
| Agent touching the gates | only the user's key changes Ring 0 | Master has branch protection and the base gate runs. The key mechanism is undefined and there is no heavy runner (F7, P0-06) |
| The model | claims no more than it covers | `VULN-COVERAGE.md` §3.0 is now honest. The README's security section presented toy-language results as the claim, until the note added with this one |

**Specific gaps.**
- **No pipeline.** `p1Pass` goes from `ucmdLang` to `slotLang`, and `splitPass` from `ucmdLangS` to itself,
  so they do not chain. Of PLAN-2026-10's P1 to P8, only P1 exists.
- **No pass has changed the input.** F3's log leaves its kill rule open: whether a lowering whose target
  input really differs can meet `cover` and `low_cover`. `splitPass` keeps the input, and P1 hides its
  table in the target program. `PassCert.enc` also does not take the program.
- **The observation has no result.** PLAN-2026-10 §2 gave `Beh` a `ret`. It has `ev`, `lk`, `cost` and `out`.
  So `rel` says nothing about what a program computes, which is what `bare_rel_breaks` shows.
- **Ring 0 is 4 of about 10 planned artifacts.** `Obs`, `Lang`, `Cert` and `Pass` exist. `Word`, `Core`,
  `Ext`, `Wire`, `RV` and `Contract` do not.
- **Little is on master.** #18 (the kernel since F4) is open, and `f5/map` holds its work on top of that.
- **F5's acceptance is not met.** It requires an island table, and none exists.

**What holds, and carries forward.** Certificates cannot be vacuous (F2). Transfers conclude certificates
on the target over its inputs (F3's theorems). Passes compose (`seq`). A one-to-many pass carries certificates
by transfer alone (F4). The lock and comparator refuse weakened statements, and mutants and witnesses are
enforced. This session's rows found real things, and they stay as evidence.

## 2. Why this order

Work so far has widened the top of the stack, and nothing tests the bottom. Each open kernel question is
about the bottom: machine words, a result, an input that changes shape, leakage as a program counter.
Locking first would freeze those answers untested, and each one found later would cost a key round trip
and a re-proof of every pass.

2026-10-29 answered "this delays reaching RISC-V bytes" by saying a vacuous certificate is just as vacuous
in bytes. That was right then. F2 and F3 have since dealt with it, so the argument no longer applies.

## 3. What changes

| Item | Now |
|---|---|
| **VS-1**, the vertical slice | next, and the only build work |
| F6, the lock and key merge | **held** until VS-1 says what the kernel needs |
| L-UNIFY, and the directive design | held. VS-1 tests the bottom first; speculation is not in the slice |
| REL-01 | held |
| F5 | paused. Open: step 4's constructors and the island table |
| PH2, PH3 | stay blocked. PH3's `W64` and PH5's bytes get a first small version in VS-1 |
| PLAN-2026-10's order | Phase 4 and 5's thin path comes before Phase 3's consolidation. A G-0 note for the user's key, since the plan is cited by `CLAUDE.md` |

## 4. Not promised

VS-1 proves little about real programs: no loops, heap, strings, functions, mediation or speculation. It does
not reach "bulletproof", and no one should read it that way. Its worth is what it finds wrong with the kernel
while that is still cheap to fix. It may also fail, and its kill rules say what that would mean.

There is no estimate of its length here. PLAN-2026-10's "45 to 65 sessions to the first certified binary" was
never measured, and VS-1's first steps are the first real data on it.
