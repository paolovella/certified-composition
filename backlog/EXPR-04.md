---
id: EXPR-04
title: "san is quote-only but reads as a general sanitizer: typed sinks, or certcheck runs PathCert"
ring: 1
tier: G-X
deps: [S-EXPR, INJ-01]
closes: ['S-EXPR follow-up']
acceptance: a fs emit built from `san ( input )` that allows `../` is refused, or san's name and documentation say what it neutralizes; the blind program 06 is refused
kill: -
status: blocked
---

## Plan

S-EXPR's 06 is accepted, and the task's property (no path traversal) does not hold. `san`
neutralizes the `'` delimiter only. A blind author read it as a general sanitizer and joined
`san ( input )` to a directory. The certificate is true, but it is not the property the
author thought they had.

Two routes, to decide before code:
1. **Short (Ring 3 and docs):** document `san` as quote-only, and have `certcheck` warn on any
   `emit fs` whose argument is not a literal, since its path-traversal certificate is not run.
2. **Real (Ring 1):** run the repo's path certificate (`PathCert`, `pathCheck_sound` is frozen)
   on `fs` sinks in `certcheck`, so 06 is refused. This is the first step toward PLAN-2026-10
   §3's typed sinks (`SinkKind` with one delimiter classifier per sink).

Recommended: route 1 now, route 2 as part of PH3's sinks.

## Log

- 2026-10-28, branch `expr-04/san-scope`. Route 1 done; route 2 (PathCert in `certcheck`, then
  PH3's typed sinks) stays open.
  - The README states that `san` is quote-only.
  - `certcheck` adds a note to an accepted program for each `fs` emit with a non-literal path.
    The note is Ring 3 text, and the verdict is unchanged. Checked: blind 06 gets the note, and
    `examples/handler.uc` does not.
- 2026-11-10, **where route 2 closes** ([`PLAN-2026-11`](../PLAN-2026-11.md) §3): in `INJ-01`, milestone M4, 2027-02-12. Sinks are typed there, and a string cleaned for `sql` is refused at `fs`. Until then this item stays open with route 1 done. Whether it can close at M0 on route 1 alone is judged against its acceptance on branch `expr-04/san-scope`.
- 2026-11-10, **judged against the acceptance, clause by clause ([`M0-01`](M0-01.md)): not done. `blocked` on `INJ-01`.**
  - *"a fs emit built from `san ( input )` that allows `../` is refused, or san's name and documentation say what it neutralizes"*: met by its second half. README: "`san` neutralizes the `'` delimiter and nothing else." `certcheck` prints a note on each `fs` emit with a non-literal path.
  - *"the blind program 06 is refused"*: **not met.** Run today at `e6e50d3`: `corpus/blind/p/06.uc` is accepted, exit 0, with the note "Not certified: path traversal. `san` neutralizes the ' delimiter only, not `../`." Route 1 was never going to refuse it.
  - So it cannot close on route 1 alone, which answers the question the entry above left open.
  - **What `INJ-01` will and will not do for this clause.** It refuses a string cleaned for `sql` and sent to `fs`, on the compiled language. That refuses 06 as `BLIND-01` ports it, not `06.uc` under `certcheck`, which will accept it for as long as it is built. When `INJ-01` lands, this item closes with that difference recorded, or is killed. It is not to be marked done on the port alone without saying so.
  - *Correction of record.* The entry above says the judging is ~~on branch `expr-04/san-scope`~~. It was done on `m0/close-old`. That older branch holds route 1 only, which is on the plan branch as `1419f13`.
