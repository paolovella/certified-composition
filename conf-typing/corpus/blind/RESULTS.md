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
