---
id: LSYN-01
title: "L's own surface syntax, for agents: a second front end onto the same core, with storage and secrecy annotations"
ring: 1
tier: G-X
deps: [RC-04]
closes: ['the user, 2026-11-08: both surfaces, C first, then L syntax for agents']
acceptance: decided when it is planned; at minimum, HChaCha20 and fe25519_mul written in L's syntax compile to the same literal images as their C readings
kill: -
status: blocked
---

## Plan

From [`USABLE-L`](../research/2026-11/USABLE-L.md) §5, item 9. After the core has met real C, so the syntax describes a language that exists. S2 measured the C front end linear in the kernel (about 0.35 ms per character), so a text syntax can be parsed in the kernel too.

## Log
- 2026-11-10, **parked past L 1.0**, by the user's decision of that day ([`PLAN-2026-11`](../PLAN-2026-11.md) §0 and §6): 1.0's source is C read by the front end. Status `planned` to `blocked`. It returns after the tag `l-1.0`. Its dependency `RC-04` is parked too.
