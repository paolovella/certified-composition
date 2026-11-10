---
id: ENG-02
title: "Ratchets in the gate: the counts that may only rise are compared with BASE's, and auto-merge on green for the tiers below G-0"
ring: 0
tier: G-0
milestone: M2 (2026-12-18)
deps: [ENG-01, CI-03]
closes: ['PLAN-2026-10 §7: ratchets are checked by the PR''s own copy of the counts']
acceptance: the gate compares, against BASE - guard-selftest cases, mutants killed, witness pairs, frozen statements, the corpus-accepted set; a PR that lowers any of them is G-0 whatever its paths, shown by a witness for each; a G-P, G-C or G-X PR that is green merges with --merge and no person; a G-0 PR never does, shown by a witness
kill: -
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2026-11-30 to 2026-12-04.

1. **The counts** come from the data files the gate already treats as data: `tools/mutants.expected`, `witnesses.expected`, `axioms.expected`, and `guard-selftest`'s case count. A line removed from one of them is a lowering.
2. **Corpus impact:** a program accepted at BASE and refused at the PR raises the tier to G-0, outside a recorded edition break.
3. **The merge bot** is a workflow on `workflow_run` of the gate, from BASE. It reads `AUTONOMY` first. It merges with `--merge`: the documents cite branch hashes.
4. **Per-tier caps** on merges per day, in the same table as the paths.

## Log
