---
id: PH6
title: Phase 6 scale: functions, contracts, separate compilation, link_correct, mlkem-native seam
ring: 1
tier: G-X
deps: [PH5]
closes: ['whole-program only']
acceptance: multi-function program linked with a foreign certificate
kill: -
status: blocked
---

## Plan

See PLAN-2026-10.md. Write the concrete steps here before starting work.

## Log
- 2026-11-10, **parked past L 1.0** ([`PLAN-2026-11`](../PLAN-2026-11.md) §6): real calls with stack frames, separate compilation and linking. Status `planned` to `blocked`. 1.0's programs are one function after `CPP-01`'s inlining, and `SEAM-01` composes components that are compiled together.
