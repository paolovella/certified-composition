# S-EXPR results: blind tasks, blind programs

Method (`backlog/S-EXPR.md`), each step committed before the next:
1. **The task list** (`TASKS.md`, 9d48c6b) was written by an isolated agent that never saw the
   language. Its whole input was `BRIEF.md`.
2. **The split** (`SPLIT.md`) has a recorded seed: 20 open, 20 holdout.
3. **The programs** (`p/`, `MANIFEST.tsv`, bc5638f) were written by a second isolated agent.
   Its only inputs were `REFERENCE.md`, `AUTHOR-BRIEF.md` and `TASKS.md`. It ran as
   `claude -p --restricted` with Read, Write and Glob confined to that directory, so it could
   not read the checkers' source or run `certcheck`.
4. The checker was run on the open half only: `certcheck p/NN.uc [--secret <MANIFEST secrets>]`,
   output in `out/`.

## Open half (20 tasks: 16 SAFE, 4 UNSAFE), 2026-10-28

| | count | |
|---|---|---|
| SAFE tasks | 16 | |
| inexpressible | 1 | 02: no comparison operator, so no password check |
| expressible | 15 | |
| accepted | 11 | **73%** of expressible safe programs |
| **falsely refused** | **4** | **27%**, against the August corpus's 4% |
| UNSAFE tasks | 4 | |
| correctly refused | 4 | 33 injection, 36 double free, 37 secret into a public cell, 40 missing check |
| wrongly accepted | 0 | |

### The four false refusals

| # | task | why it was refused | kind |
|---|---|---|---|
| 18 | allocate under a public flag, free under the same flag | the pointer tracked after an `if` is the intersection of both branches, so the second `if` frees an untracked pointer. Safe on every path | **checker limit**, listed in PLAN-2026-08 §1.2 (`interStr` at `ite`) |
| 20 | nested counted loops over a grid | the counted-loop rule checks its body with a checker that has no loop rule | **checker limit**: the same as August's program 24 |
| 09 | hold an API token in a secret cell, call upstream, emit constants | `secret x` is accepted only if the pointer variable `x` is itself marked secret (`FullCert.lean:154`) | **reference defect**: `REFERENCE.md` never said so |
| 22 | hash a password, store only the hash in a secret cell | same as 09 | **reference defect** |

09 and 22 are accepted when the cell pointers are added to `--secret` (checked 2026-10-28). They
still count as refusals here, because the reference was fixed before the run and correcting it
now would be tuning. The rule is not stated in the README either. A blind author had no way to
know it, which is itself a usability finding.

### Do the accepted programs carry the task's property?

An accepted program is certified for the checker's properties: budget, mediation, flow, memory
safety, and `'`-delimiter injection. Those are not always the property the task asked for. The
coverage column below is the measurer's own judgment, not a checked claim.

| # | task property | certified? | note |
|---|---|---|---|
| 01 | every access authorized | yes | |
| 03 | free on every path, no leak | partly | memory safety yes; leak-freedom is not certified |
| 05 | no SQL injection | partly | `san` inside a quoted literal stands in for parameter binding |
| 07 | no control characters into the log | partly | `san` handles the `'` delimiter only |
| 08 | HTML escaping | partly | the same |
| 15 | no use-after-free | yes | |
| 16 | no double free | yes | |
| 19 | authorized read-back | yes | the two requests are one program |
| 23 | no shell injection | yes | only fixed literals reach `sh` |
| 28 | no open redirect | partly | the allowlist test is a public flag; the test itself cannot be written |
| 29 | no out-of-bounds read | no | there are no lengths or bounds; a counted loop stands in |

**6 of 11** carry the task's property in full. The rest are certified for something narrower,
because the language has no comparisons, lengths, arrays or string operations. The author's
`MANIFEST.tsv` notes an approximation for 31 of the 37 programs.

## What the open half says, before the holdout

- **The checkers refuse no unsafe program here** (4/4), and every refusal is for the stated
  reason.
- **The false-refusal rate on blind programs is 27%**, against 4% on the rules author's own
  corpus. Two refusals are known checker limits that a blind author hit unprompted. The other
  two are an undocumented rule.
- **Inexpressibility is low, 1 of 16, but only because approximation hides it.** About 84% of
  programs needed an approximation, and 5 of the 11 accepted ones are certified for something
  narrower than the task. The comparison operator alone, which `02` and `27` lack, would change
  what can be stated.
- **S-EXPR's kill rule** (more than 30% falsely refused or inexpressible) **does not fire** on
  the open half (27% and 6%). It is close.

The holdout is reported below, unsealed after this section was committed, with no rule and no
reference changed.

## Holdout (20 tasks: 16 SAFE, 4 UNSAFE), unsealed 2026-10-28 after a960c05

No rule and no reference changed between the two halves.

| | count | |
|---|---|---|
| SAFE tasks | 16 | |
| inexpressible | 2 | 24: no lengths or substrings, so no truncating copy; 27: no comparison |
| expressible | 14 | |
| accepted | 12 | **86%** |
| **falsely refused** | **2** | **14%** |
| UNSAFE correctly refused | 4/4 | 34 path traversal by concatenation, 35 use-after-free, 38 secret decides a branch, 39 unbounded loop |

| # | task | why refused | kind |
|---|---|---|---|
| 11 | retry five times with a fixed delay | a delay loop nested inside the retry loop | **checker limit** (nested counted loops, as 20) |
| 10 | branch on a public role flag, key kept in a secret cell | the secret-cell pointer was not marked secret | **reference defect** (as 09, 22); accepted when it is |

Coverage of the 12 accepted programs (the measurer's judgment): **7 yes** (13, 14, 25, 26, 30,
31, 32), **4 partly** (04, 12, 17, 21: bounded and memory-safe, but the out-of-bounds property
has no meaning in a language without indices), and **1 no**:

- **06 is accepted, and the task's property does not hold.** The program builds
  `"/srv/uploads/" ++ san ( input )`. `san` neutralizes the `'` delimiter only, so `../` passes
  through. The certificate is true (there is no quote injection), but a blind author read
  `san` as a general sanitizer and wrote a path-traversal hole the checker cannot see. The
  repo's path-traversal certificate (`PathCert`) is not part of `certcheck`.

The halves differ by 13 points in false refusals (27% and 14%), under the 15-point threshold, so
the open half was not unrepresentative.

## Combined (40 tasks)

| | open | holdout | all |
|---|---|---|---|
| SAFE inexpressible | 1/16 | 2/16 | **3/32 (9%)** |
| SAFE accepted / expressible | 11/15 | 12/14 | **23/29 (79%)** |
| **SAFE falsely refused** | 4/15 | 2/14 | **6/29 (21%)** |
| UNSAFE refused | 4/4 | 4/4 | **8/8** |
| accepted carrying the task's property in full | 6/11 | 7/12 | **13/23** |

The six false refusals have three causes:
- **nested counted loops: 2** (20, 11);
- **the `if` join intersecting tracked pointers: 1** (18);
- **the undocumented secret-pointer rule: 3** (09, 22, 10).

Fixing the reference would leave 3/29 (10%), all checker limits that the repo has recorded
since August.

**Verdict against the kill rule** (over 30% falsely refused or inexpressible): **it does not
fire** (21% and 9%). The bet survives its first blind measurement, with four qualifications:

1. **The number that moved is the false-refusal rate:** 4% on the author's corpus, 21% blind.
   Half of it is documentation, not the checker.
2. **Inexpressibility looks low only because the author approximated** (31 of 37 programs).
   Taken as written, the tasks need comparisons, lengths, arrays, functions and early return,
   which is exactly the PLAN-2026-10 §3 surface the L core is meant to add.
3. **Acceptance is not the task's property.** 2 of 23 accepted programs (06, 29) are certified
   for something that does not include what the task asked for, and 06 is a real hole. `san`'s
   name promises more than it does. L's typed sinks (`SinkKind` with per-sink classifiers,
   PLAN-2026-10 §3) are the fix the plan already names.
4. **One author, one run, 40 tasks.** A second blind author on the same tasks would show how
   much of this is the author.
