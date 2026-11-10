---
id: ENG-03
title: "Auto-revert, incidents and the kill switch: a merged commit that fails the audit is reverted, recorded, and can turn autonomy down"
ring: 0
tier: G-0
milestone: M2 (2026-12-18)
deps: [ENG-02]
closes: ['PLAN-2026-10 §7: AUTONOMY is a file nothing reads; a bad merge is found by the next session']
acceptance: a post-merge audit on master runs the full CI and the heavy tier; on failure it opens a revert PR, which merges on green, and writes incidents/I-####.md with an item for the guard that would have caught it; the merge bot and the SessionStart hook read AUTONOMY and obey it; two reverts in 7 days, or any G-0 audit failure, set AUTONOMY to off and open an issue for the user; planted - one bad cell is reverted, a second one within the week turns autonomy off, and a planted audit failure on a G-0 path does so at once
kill: gate flake above 5% over the planted runs - fix the flake first (PH2's kill rule)
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2026-12-07 to 2026-12-11.

1. **The audit** is a workflow on `push` to master. It is the same `tools/ci.sh` and the heavy steps, so it cannot disagree with the gate except by what the gate could not see: the merge result, the heavy runner, time.
2. **The revert** is a PR like any other, classified by the gate. A revert of a Ring 1 change is G-X.
3. **Turning down is automatic, turning up is the user's.** `AUTONOMY` is Ring 0, and the bot's write to it is the one exception, lowering only. The witness shows a bot commit that raises it is refused.
4. **Receipts:** each merge, revert and downgrade writes one under `tools/receipts/`.
5. The planted failures run on a fork or a scratch repository, and the item records where.

## Log
