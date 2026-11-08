---
id: ROUTE2-01
title: "Route 2's cost per certified program: raise the budget, cache a per-program export by content hash, or split what the external kernels re-check"
ring: 0
tier: G-0
deps: [RC-03]
closes: ['S-USABLE §2: lean4lean re-checks each program at about 20 times Lean kernel cost (an estimate from one pair), so route 2 holds a handful of real functions']
acceptance: the user's choice among USABLE-L §2's (a), (b), (c), with route 2's time measured before and after on M1
kill: -
status: planned
---

## Plan

For the user's key. [`USABLE-L`](../research/2026-11/USABLE-L.md) §2 recommends (b): a per-program export, checked once per content hash by all six kernels and cached, so every check is kept and each is paid once. Measured first on `RC-03`, and the ratio is re-estimated from more than one pair.
