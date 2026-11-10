---
id: S-HEAP
title: "Spike: does a pool allocator written in machine code simulate an abstract heap, on one alloc and one free?"
ring: 3
tier: G-P
milestone: D2 (2027-01-12)
deps: [RC-03]
closes: ['PLAN-2026-11 §5 cut 6: the heap design or its fallback is decided on 2027-01-12', 'EXPR-03, whose kill rule fired on 2026-10-28: the question it left is inherited here']
acceptance: research/2027-01/S-HEAP.md with a verdict, from Lean that builds: a source language with alloc and free over an abstract heap of fixed-size cells; a lowering to the slice's memory with a free list; the pass certificate for a program that allocates once, writes, reads and frees, or the goal that cannot be closed; the measured kernel cost; a statement of what an opaque pointer may and may not do
kill: if the simulation needs a relation the kernel's PassCert cannot state, or one alloc costs more than 60 s of kernel time, the verdict is the fallback: static arenas with public indices (PLAN-2026-10 §3's first package)
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2026-12-21 to 2027-01-12, beside `S-SPEC`. A spike, with nothing entering the build.

Row 6 holds today on `ucmdLangS` and `ucmdLangH` (`bcheck_memsafeS`, `leakSafe_traceH`), where the heap is a map in the state and a pointer is a name. On the machine a pointer is a number, and the allocator is code.

1. **Read `EXPR-03` in full**: what its kill rule measured and why it fired.
2. **The design to test.** One pool of `n` cells of one size, in a region stated at link time. A free list threaded through the cells. `alloc` pops and `free` pushes, in a constant number of steps, so that rows 2 and 10 survive.
3. **The source's pointer** is opaque: no arithmetic, no comparison but equality, no cast. The report states what that excludes of real C.
4. **The simulation.** The relation between the abstract heap and the machine's memory, and whether `PassCert`'s `enc` and `cover` state it. Address events (`Lk.addr`) are the hard part: the machine's addresses depend on the allocation history, so the source must emit them or the certificate must be at a view that hides them. The report says which.
5. **The verdict**: the design, a narrower one, or the fallback.

**Vacuity:** a use after free in the source has a machine run that reads another object's bytes, shown under QEMU.

## Log
