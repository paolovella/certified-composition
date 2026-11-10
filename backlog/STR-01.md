---
id: STR-01
title: "Byte strings of run-time length: a buffer with a stated capacity and a public length, filled by loops and emitted to a named sink"
ring: 1
tier: G-X
milestone: M4 (2027-02-12)
deps: [L-IO]
closes: ['rows 3 and 14 need a query or a path built from an input of run-time length; arrays today have a stated length']
acceptance: a program that copies an input string of public length up to a stated capacity between two literals and emits the filled part to a named sink reaches its literal image with Cert.rel and Cert.boundR by transfer; QEMU agrees on lengths 0, 1, the capacity, and a length past it, which is refused or clamped as the note states; a write past the capacity is refused; every existing literal image is unchanged
kill: if an emit of run-time length breaks the passes' cover or low_cover, or needs a kernel change, stop and report
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track A, 2027-01-11 to 2027-01-22.

1. A note on what a string is: a buffer, a capacity that is a literal, and a length that is a public word. Secret lengths are out of scope, and the checker refuses them.
2. `emitB` gains a length that is an expression, bounded by the capacity. The machine already writes a run-time length: `sysWriteStep` reads it from a register.
3. The budget: `boundR` in the length, as `BOUND-01`'s counted loops.
4. The C reading of `char *` with a length argument, in a READING note, against clang.
5. Witnesses, QEMU cases and mutants as the acceptance says.

## Log
