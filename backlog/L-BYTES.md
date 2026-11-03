---
id: L-BYTES
title: "Connect L's checkers to machine code: compile UCmd, or a language that replaces it, so the map's rows reach bytes"
ring: 0
tier: G-0
deps: [VS-2]
closes: ['VS-1: the path to bytes is for a separate language; bcheck and the map stop before machine code']
acceptance: decided after VS-2; at minimum, one vulnerability-map row holds on literal bytes, by transfer from the checker that row names
kill: -
status: planned
---

## Plan

Recorded on the user's word of 2026-11-03. Not started, and blocked on VS-2's result.

**The gap.** `LCore.Slice` compiles to RV64 bytes. `UCmd`, which `bcheck` and every row of `VULN-COVERAGE.md` §3.0 are about, does not, and no theorem
links the two languages. So no checker or row in the map reaches machine code.

**The two routes** (`research/2026-11/VS-1-ACCOUNT.md` §6), for the user to choose after VS-2:
- **Grow `sliceLang`** into L's core, adding heap, strings and mediation one at a time, each through to the bytes. Every row is re-proved, and is real when it lands.
- **Lower `UCmd`** by bridging it to `W64`. It keeps F5's work, and has to settle what an unbounded integer means on a machine.

`L-UNIFY`, the directive design and `REL-01` are about a language that may not be the one that compiles, so they wait on this choice.

## Log
