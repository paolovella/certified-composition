---
id: HEAP-02
title: "Row 6 on bytes, memory safety: no use after free, no double free, no wild access, on the literal image"
ring: 1
tier: G-X
milestone: M5 (2027-02-26)
deps: [HEAP-01]
closes: ['VULN-COVERAGE §3.0 row 6: memory safety holds on ucmdLangS']
acceptance: a checker on the slice language whose acceptance gives, on the literal image and by transfer alone, that no run faults and every access is to a live cell or a declared array; accepted: a handler that allocates, uses and frees in a loop; refused: a use after free, a double free, and a free on one branch only, each with an image that reads or corrupts another object under QEMU
kill: if aliasing makes the checker refuse more than 30% of the safe heap tasks in conf-typing/corpus/blind, report before going on; that is the threshold S-EXPR used
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2027-02-08 to 2027-02-19. The rule to start from is `bcheck`'s ownership state (`ConfTyping.bcheck_memsafeS`, `UStep.lean`; `MemCert.lean`).

1. `memCheck` on `Slice2.Prog`: each pointer variable is unowned, owned or freed. `ite` joins, and a loop's body must return the state it was given.
2. The statement. Safety is a property of runs, so it is `Cert.trace` over a fault event, or the absence of a stuck state. Which one the kernel states is settled first, in the item's note, from how `sliceLang` treats an out-of-range store today.
3. The image, by transfer.
4. Witnesses, QEMU runs of the refused images, mutants: the join that takes the better arm, the loop rule that forgets a free.

**Not claimed:** safety of code outside L that the program is linked with.

## Log
