---
id: CPP-01
title: "The C front end reads macros, inline helpers with pointer arguments, do-while(0), and a public branch on a stated pointer"
ring: 1
tier: G-X
deps: [W32-01]
closes: ['S-USABLE §4: crypto_core_hchacha20 as written uses QUARTERROUND, ROTL32, LOAD32_LE and STORE32_LE']
acceptance: the front end reads core_hchacha20.c lines 16-69 with private/common.h's helpers, all pinned by sha256, into one L program by decide; refused witnesses for a recursive macro, an unbounded expansion, a helper whose pointer argument is not a fixed offset into a stated array, and a pointer branch with no stated value
kill: if macro expansion cannot be bounded so the kernel evaluates it, stop and report
status: planned
---

## Plan

From [`USABLE-L`](../research/2026-11/USABLE-L.md) §5, item 4. Function-like macros are expanded by a bounded pass before parsing. `static inline` helpers with pointer arguments (`k + 16`) are inlined, with each pointer read as a fixed window of a stated array. `if (c == NULL)` is read with `c` stated non-null, and the other branch is refused, not read. The `NATIVE_LITTLE_ENDIAN` question (`memcpy` against the portable branch) is settled in a READING note first.
