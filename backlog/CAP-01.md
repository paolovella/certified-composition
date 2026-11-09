---
id: CAP-01
title: "Lift the slice's caps that are not the machine's: distinct variables in fits, the real code-segment bound, large literals, long branches"
ring: 1
tier: G-X
deps: [RC-02]
closes: ['S-USABLE §1: the pipeline refuses 100 straight-line statements, by caps that are proof constants or bookkeeping']
acceptance: line:300 and loop:150 from research/2026-11/usable/s1_gen.py compile and carry relView to their literal images; 0x61707865 and 0x7ffffffffffff are accepted literals; a branch arm of 2,000 instructions is accepted; every existing literal image (VS-1, VS-2, BOUND-01, RC-01) is byte-for-byte unchanged
kill: if the 3,000-byte bound cannot be raised without a kernel change, stop and report
status: in-progress
---

## Plan

From [`USABLE-L`](../research/2026-11/USABLE-L.md) §1. Four caps, each with an accepted and a refused witness at its new edge:
1. `Slots.fits` counts distinct names, not occurrences. `slotOf` is unchanged.
2. The hypothesis `C.length ≤ 3000` in `walk_exec`, `behind`, `ahead`, `det_run`, `init_inv` and `okP` becomes the code segment's real room, below `dataBase`.
3. Literals outside −2048…2047 lower to `lui` + `addi`. Each is compared with QEMU in `rv_diff.py`, and `good_lui` covers the encoder.
4. A branch arm past 1023 instructions: an inverted `beq` over a `jal`. `jal` enters `rvLang` with its encoding and a broken model.

Riskiest first: 2, since it touches the pass proofs' hypotheses.

## Log
- 2026-11-09, **started**, on the user's "keep working", on branch `cap/caps` from `rc/out-arrays`, which is not yet merged. This item was filed on `spike/usable`, also unmerged, and is copied here with its plan unchanged.
- 2026-11-09, **a change of plan, before code: existing images may change.** The plan required every existing literal image to be byte-for-byte unchanged. Part 1 cannot keep that.
  - A local's slot was 128 plus its first position in `allVars`, a list of every occurrence. Part 1 numbers locals among distinct names, so programs whose names repeat before a new one appears get new slot numbers.
  - The acceptance becomes: each changed literal is regenerated from the compiler, checked by its `decide` equation, and its QEMU comparison rerun with a receipt.
- 2026-11-09, **part 1 done: locals numbered among distinct names** (`Slots.uniq`, `slotOf`, `fits`).
  - `fits` counted occurrences against 512, and no proof used that bound. The binding limit was the lowering's `okC`: a slot under `wordsMax = 256`. `fits` now counts distinct names against it.
  - **Images regenerated** (`decide` equations hold): `scan` 9 bytes changed, `arrayInLoop` 3, `countUp` 6, `capped` 4, `verify16` 13, `sodium_add` 10. `spin` and five refused programs' images are unchanged. `scanInsns` is updated by hand to the new slots, 1040 and 1048.
  - Every theorem about those images still holds: the budgets 905 and 1825, the transfers, the leak witnesses.
  - **QEMU reruns** (receipt `cap01-qemu`): `image2_diff`, `bound_diff`, `refused2_diff`, `verify16_diff` (with clang), `add_diff` (with clang) and `out_diff` all report 0 failed.
  - **Witnesses** (`Slice2/Caps.lean`): `manyOcc_fits`, 402 occurrences of two names, accepted now and refused by the old rule; `names_edge`, 128 locals accepted and 129 refused.
  - **Cost, measured** (receipt `cap01-s1`): S-USABLE S1's `line100` now passes the whole pipeline. Its literal equation takes 289 ms against 415 ms before, and `line300`'s 850 ms against 1200 ms.
  - `names_edge` costs 2.3 s of kernel time, from 129 distinct strings compared pairwise; at S-USABLE's estimate of about 20 times, roughly 45 s of route 2.
- 2026-11-09, **part 2 done: the image may be 65360 bytes** (`dataBase - codeBase`; it was 3000).
  - **The real cap was the ELF writer, not the proofs.** It put the data segment at file offset 0x1000, so code over 3920 bytes would have overlapped it. The 3000 in the pass proofs sat below that.
  - `Rv.elf`, and the tests' independent Python writers, now put the data segment at the first page boundary after the code. Every ELF of code under 3920 bytes is unchanged.
  - The pass proofs hold at 65360 with no change but the constant: they used it only to keep code below `dataBase`.
  - **Witnesses:** `image_edge`, 16340 instructions accepted and 16342 refused, proved from `genP_length` with no image built.
  - **`test/big_diff.py`** (receipt `cap01-bigdiff`): a 7220-byte image is accepted. Lean's ELF and the Python writer's agree byte for byte, and QEMU gives the model's exit status (203) and instruction count (1805). Vacuity: the old layout's ELF does not.
  - **QEMU reruns after the writer change** (receipt `cap01-qemu2`): `rv_diff`, which uses Lean's writer, and the seven image tests, all 0 failed.
  - **Mutants:** three new ones in `slice2_low_mut.py`, all killed (receipt `cap01-lowmut-new`). The script built only as far as `LCore.Slice2.Bytes`, so the first run left "fits allows one more local" alive. `Caps.lean`'s witnesses were outside its build. It now builds `LCore.Slice2.Caps` too.
- 2026-11-09, **an audit of what cites the old images**, on a side agent's note: every write-up and test that cites them must be updated before the merge.
  - **Image bytes** appear only in Lean literals, each held to its program by a `decide` equation, all regenerated. They also appear in four `slice2_low_mut.py` anchors, each checked for a unique match.
    - The regeneration had reformatted four literals, a break after `[`, so one anchor stopped matching. The script's assert refused to run, and the literals are restored to their old layout.
  - **No write-up cites image bytes, slot offsets or image hashes.**
    - The sizes the accounts state (`verify16`'s 180 bytes, `sodium_add`'s 204) are unchanged, as are the budgets (905, 1825) and the instruction counts measured under QEMU (452, 1200).
    - `VS-2-FUEL`'s "locals from slot 128" still holds.
    - `cfront_gen.py`'s and `ring0-lock.sh`'s hashes are of source files and kernel declarations, not images.
  - **The tests read the literals from the Lean files** (`image2_diff.literal`) or have Lean print them (`Verify16Pred`, `AddPred`), so they test the new bytes. All were rerun (receipts `cap01-qemu`, `cap01-qemu2`).
  - **What changes at the merge:** `verify16Image`, certified in RC-01 and on `master`, becomes a different 180-byte image with the same certificate, the same budget and the same QEMU and clang results. The certificate is a theorem about whatever the pipeline produces, re-proved here. It is not a claim about those particular bytes.
- 2026-11-09, **parts 1 and 2's full mutant run** (`slice2_low_mut.py`, receipt `cap01-lowmut`): 73, all killed, with `LCore.Slice2.Caps` in the build.
- 2026-11-09, **parts 1 and 2's CI: green on all 28 steps** (receipt `cap01-ci`). Route 2 took 240 s against 319, up from 197, about as estimated for `names_edge`.
