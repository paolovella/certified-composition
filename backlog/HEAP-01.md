---
id: HEAP-01
title: "A fixed-cell pool allocator in machine code and an opaque pointer in the language, carried by the passes"
ring: 1
tier: G-X
milestone: M5 (2027-02-26)
deps: [S-HEAP]
closes: ['VULN-COVERAGE §3.0 row 6: the heap is a map in UCmd''s state, and nothing compiles it']
acceptance: alloc and free in the slice language, lowered to the allocator's instructions, with both passes' certificates; every existing certificate shape still transfers for programs that use them; the allocator's steps are constant, so a program that allocates under a secret-independent pattern keeps Cert.rel and Cert.bound; QEMU agrees with the model on alloc, free, reuse and exhaustion, each with a broken model; every existing literal image is unchanged
kill: as S-HEAP's verdict states; if that verdict was the fallback, this item is static arenas with public indices, and its acceptance is restated with a record before work starts
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2027-01-13 to 2027-02-05. The design is `S-HEAP`'s verdict, and this plan is rewritten from it on 2027-01-12. What is fixed now:

1. The pattern is `CAP-01` part 4's: the machine first, each new behaviour compared with QEMU, then the language, then mutants.
2. Exhaustion is an event, not undefined behaviour. The note says which: a fault, or a null the program must test.
3. A C reading of `malloc` and `free` for one stated size class, in a READING note, tested against clang with a fixed-pool `malloc`.

## Log
