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
- 2026-11-06: VS-2 is done, so this item is no longer blocked: the route is the user's to choose. [`VS-2-ACCOUNT`](../research/2026-11/VS-2-ACCOUNT.md) §6 recommends growing `sliceLang`, since loops, an array and negative immediates each reached bytes in one step, and `UCmd`'s unbounded integers still cannot.
- 2026-11-06, **correction of record** to the entry above. It said `UCmd`'s unbounded integers ~~still cannot~~ reach bytes. That is false: CakeML compiles unbounded integers to RISC-V through a verified bignum runtime ([`VS-2-RESEARCH`](../research/2026-11/VS-2-RESEARCH.md) §1). The reason that holds is narrower: for secret data a bignum's size shows in its time and addresses, which `rel` observes. So lowering `UCmd` needs a constant-time bignum runtime or bounded integers. The recommendation to grow `sliceLang` stands, for that reason.
- 2026-11-06, **the route is chosen, by the user: grow `sliceLang`** into L's core, one construct at a time, each through to the bytes. The first is a counted `for` loop with a budget (`BOUND-01`, also the user's decision). `UCmd`'s rows are re-proved on the grown language, one at a time.
