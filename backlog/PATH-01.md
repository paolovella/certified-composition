---
id: PATH-01
title: "Row 14 on bytes: a path built from untrusted input stays under its root, on the literal image"
ring: 1
tier: G-X
milestone: M4 (2027-02-12)
deps: [STR-01, INJ-01]
closes: ['VULN-COVERAGE §3.0 row 14: loop-free and per sink, on ucmdLangI, carried by no pass']
acceptance: Cert.trace on the literal image by transfer alone, saying that the path reaching the fs sink never climbs above its root for any untrusted input; accepted: a leaf name with separators and dots refused at run time, and a path whose depth is bounded below by the analysis; refused: a concatenation of an unchecked name, whose image opens a path outside the root under QEMU
kill: -
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track A, to 2027-02-12. The rules to start from are `ConfTyping.pcheck_traceI` (`PathL.lean`) and the depth analysis of `PathCert.lean`.

1. The per-sink rule, on the slice language: an untrusted string reaches `fs` only as a checked leaf.
2. The depth analysis: a lower bound on the depth a path expression leaves, so that a `..` taken from a literal is accepted where the bound allows it.
3. The image, by transfer. Witnesses, QEMU, mutants.

**Third in the cut order** (`PLAN-2026-11` §5): if M4 is late, step 2 is dropped and the row keeps the per-sink rule, with a record.

**Not claimed:** anything about symbolic links, or about how the operating system resolves a path. The alphabet is segments, separators and `..`.

## Log
