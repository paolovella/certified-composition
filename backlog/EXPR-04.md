---
id: EXPR-04
title: "san is quote-only but reads as a general sanitizer: typed sinks, or certcheck runs PathCert"
ring: 1
tier: G-X
deps: [S-EXPR]
closes: ['S-EXPR follow-up']
acceptance: a fs emit built from `san ( input )` that allows `../` is refused, or san's name and documentation say what it neutralizes; the blind program 06 is refused
kill: -
status: planned
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
