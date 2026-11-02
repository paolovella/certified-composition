---
id: REL-01
title: "Computed release on L: a declassify command in UCmd that produces Ev.release, with a ledger"
ring: 0
tier: G-0
deps: [F5]
closes: ['F5 row 4 limit']
acceptance: a program that releases only a computed value (the guard bit of P_leak) has a certificate that says no more than that value, and Ev.release is produced by a run
kill: -
status: planned
---

## Plan

Recorded by the user's decision of 2026-11-02, when F5 row 4 took whole-variable release. Not started.

**The gap.** `ConfTyping.Release.bcheck_release` can release only a whole input variable.
`revealR_coarser` shows a program that reveals whether a variable is zero, whose certificate must
still release all of it. `SecTyD` states computed releases, but on the toy `Cmd`.

**What it needs.** A `declassify` command in `UCmd`, which produces `Ev.release`, a ledger of what
was released as `SecTyD`'s `relOf` does, and a case in every proof over UCmd's commands.

**Timing, for F6 to decide.** This changes L's meaning, and F6 locks that meaning. It is cheaper
before the lock than after, so F6 must either do this first or record why the lock goes ahead
without it.

## Log
