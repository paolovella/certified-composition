---
id: CAP-01
title: "Lift the slice's caps that are not the machine's: distinct variables in fits, the real code-segment bound, large literals, long branches"
ring: 1
tier: G-X
deps: [RC-02]
closes: ['S-USABLE §1: the pipeline refuses 100 straight-line statements, by caps that are proof constants or bookkeeping']
acceptance: line:300 and loop:150 from research/2026-11/usable/s1_gen.py compile and carry relView to their literal images; 0x61707865 and 0x7ffffffffffff are accepted literals; a branch arm of 2,000 instructions is accepted; every existing literal image (VS-1, VS-2, BOUND-01, RC-01) is byte-for-byte unchanged
kill: if the 3,000-byte bound cannot be raised without a kernel change, stop and report
status: planned
---

## Plan

From [`USABLE-L`](../research/2026-11/USABLE-L.md) §1. Four caps, each with an accepted and a refused witness at its new edge:
1. `Slots.fits` counts distinct names, not occurrences. `slotOf` is unchanged.
2. The hypothesis `C.length ≤ 3000` in `walk_exec`, `behind`, `ahead`, `det_run`, `init_inv` and `okP` becomes the code segment's real room, below `dataBase`.
3. Literals outside −2048…2047 lower to `lui` + `addi`. Each is compared with QEMU in `rv_diff.py`, and `good_lui` covers the encoder.
4. A branch arm past 1023 instructions: an inverted `beq` over a `jal`. `jal` enters `rvLang` with its encoding and a broken model.

Riskiest first: 2, since it touches the pass proofs' hypotheses.
