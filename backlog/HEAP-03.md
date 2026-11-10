---
id: HEAP-03
title: "Row 6 on bytes, leaks: a run that finishes has freed what it allocated"
ring: 1
tier: G-X
milestone: M5 (2027-02-26)
deps: [HEAP-02]
closes: ['VULN-COVERAGE §3.0 row 6: leak-freedom holds on ucmdLangH for finished runs']
acceptance: on the literal image and by transfer alone, every finished run ends with the pool as it began; accepted: allocate and free in a loop; refused: an allocation in a loop with no free, whose image exhausts the pool under QEMU
kill: -
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2027-02-22 to 2027-02-26. The rule to start from is `ConfTyping.leakSafe_traceH` (`LeakL.lean`), whose refused witness is `loopAlloc`.

**Second in the cut order** (`PLAN-2026-11` §5): if M5 is late, this item is dropped with a record and row 6 on bytes is memory safety only.

1. The rule: `memCheck`'s final state has no owned pointer.
2. The statement is about finished runs only, as on L today. A run that does not finish may hold memory, and the map says so.
3. The image, witnesses, mutants.

## Log
