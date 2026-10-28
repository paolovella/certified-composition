---
id: CMP-P1
title: Compiler pass P1 (names to slots): adopt the sketch on branch compiler/p1 with frame theorem and teeth
ring: 1
tier: G-X
deps: [WI-001]
closes: ['sketch only in scratchpad']
acceptance: branch builds; square + frame + colliding_slots_leak proved
kill: -
status: planned
---

## Plan

See PLAN-2026-10.md. Write the concrete steps here before starting work.

## Log

- 2026-10-28: the sketch is lost (I-0003). Only `compile` and `TCmd` survive, in `bench/kernel/gen.py`. P1 is rebuilt as PH1 step 5; this item closes with PH1.
