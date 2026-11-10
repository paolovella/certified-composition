---
id: REL-01
title: "Row 4 on bytes: a release command on the slice language that produces Ev.release, and a certificate that says no more than the released value"
ring: 1
tier: G-X
milestone: M3 (2027-01-08)
deps: [L-IO]
closes: ['F5 row 4 limit', 'VULN-COVERAGE §3.0 row 4: release holds on ucmdLangS for a whole input variable, and no pass carries it']
acceptance: a program that releases only a computed value (the guard bit of P_leak) has a certificate that says no more than that value, and Ev.release is produced by a run; both on the literal image, by transfer alone; a refused program that releases one value and emits another, whose image shows the difference under QEMU
kill: if the relation "low inputs agree and the released values agree" is not preserved by the passes' enc, stop and report
status: planned
---

## Plan

**Re-aimed on 2026-11-10** by [`PLAN-2026-11`](../PLAN-2026-11.md) §3: Track A, 2027-01-04 to 2027-01-08. The earlier plan is kept below, and the log records what changed.

1. `release tag e` in `Slice2.Cmd`, from `L-IO`: it produces `Ev.release tag` with the value of `e`.
2. `relCheck`: `ctCheck` at the partition where each released expression counts as public from its release on. The ledger is the list of released expressions, in order.
3. The certificate is `Cert.relView` with a general relation: two inputs are related when their low parts agree and every released expression has the same value on both. That is `SecTyD`'s `relOf`, stated on inputs.
4. The image, by the `relView` transfer `RC-02` used.
5. Witnesses: `P_leak`'s guard bit released and accepted; the whole variable emitted after releasing one bit, refused. Mutants: the rule that counts a variable as released when only an expression of it was.

**Not claimed:** that releasing the value is wise. The ledger says what was released, and the policy on it is the user's.

### The plan before 2026-11-10, on UCmd

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
- 2026-11-03, held by the user's decision: the vertical slice comes first (VS-1).
- 2026-11-10, **re-aimed from UCmd to the slice language**, by the user's decisions of that day (`PLAN-2026-11` §0).
  - The header before: title "Computed release on L: a declassify command in UCmd that produces Ev.release, with a ledger"; ring 0, tier G-0; deps [F5]; kill "-". The acceptance's first sentence is unchanged, and "on the literal image" and the refused witness are added.
  - Why the ring fell: the command is added to `Slice2.Cmd`, which is Ring 1. `Ev.release` is already in the kernel's `Ev`, so the kernel does not change. If it turns out that it must, `L-IO`'s kill rule fires first.
  - F6 locked the kernel on its own terms, and the timing question above is closed by that.
