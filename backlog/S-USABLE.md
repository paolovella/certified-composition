---
id: S-USABLE
title: "Spike: from the slice language to a usable L, by measurement: kernel cost at scale, the caps, the cost of a construct, and the first real milestone"
ring: 3
tier: G-P
deps: [RC-01]
closes: ['the user, 2026-11-08: "research how to pass from toy language to actual usable language"']
acceptance: research/2026-11/USABLE-L.md, every number from a receipt or a bench/usable tsv row; the kernel cost of checking and compiling at about 1x, 10x and 100x verify16's size; the front end's cost against text length; lines touched per construct over RC-01, VS-2 and BOUND-01; a construct inventory of at least five candidate real functions; a recommended milestone and an ordered route of planned items
kill: -
status: in-progress
---

## Plan

The user's words of 2026-11-08: "research how to pass from toy language to actual usable language". The user's answers to three questions:
- **Surface:** both, C first. The C front end grows so real C certifies, and L's own syntax for agents comes later, lowering to the same core.
- **Milestone:** the research decides, with evidence.
- **Depth:** a survey plus measured spikes on this repo.

**No library change.** Spike Lean lives in `research/2026-11/usable/`, imported by nothing, run with `lake env lean -D autoImplicit=false` from `l-core/`, as `BoundRSketch.lean` is. Generators are Python in the same folder. Results go to `bench/usable/*.tsv`, and long runs go through `tools/run-job.sh`, capped in memory and time.

**Why it is still a toy, from the code:**
- 64 input words and one 64-word scratch array (`Slice2/Slots.lean` `fits`), and 256 word slots (`Slice/Lower.lean` `wordsMax`).
- Branch arms under 1024 instructions (`Slice2/Lower.lean` `okC`).
- Byte arrays of 1, 2, 4 or 8 words.
- One function, one 64-bit result.
- No `mul`, no 32-bit arithmetic, no left shift.
- C is read by the kernel from character codes.
- Every real program's kernel-evaluated proofs are re-checked by route 2's six kernels.

**Spikes.**
- **S1, kernel cost against program size.** Synthetic Slice2 programs at about 1x, 10x and 100x `verify16`, in three shapes: (a) straight-line chains, (b) a counted loop with a k-statement body, (c) `verifyN` up to the 64-byte cap.
  - Timed in Lean's kernel for each: `ctCheck` by `decide`, the literal-image equation by `decide`, `pipeline_comp` with `relView_transfer`, and the source budget.
  - A cap that refuses a size is recorded as data.
  - lean4lean's cost is estimated from `CTBytes`' ratio, and marked as an estimate. One size is checked directly if that is feasible.
  - **Vacuity:** the 1x point is `verify16`, which must reproduce `CTBytes`' times within noise.
- **S2, the front end's cost against text length.** `CFront` on generated C texts of about 600, 2,400 and 9,600 characters, by `decide +kernel`. One generated text must be refused.
  - **Rule:** superlinear past a few kilobytes means the parser leaves the kernel. An untrusted parser emits the `Prog`, and the kernel checks a printer round-trip.
- **S3, the marginal cost of a construct.** Lines and files touched per construct, from `git log --numstat` over RC-01, VS-2 and BOUND-01, against PLAN-2026-10 §6's O(N·(C+P)).
- **S4, a construct inventory of candidate milestones**, from pinned upstream sources fetched as untrusted data: libsodium's `utils.c`, `sodium_bin2hex`, ChaCha20, Poly1305, SHA-256's compression function, and X25519 field arithmetic. For each: what it needs that L lacks, and where it is used.

**Survey**, of what bears on "usable", with sources: Jasmin (inlining, `export`, arrays, a RISC-V back end?), FaCT, CakeML and CompCert (evaluation against an extracted compiler), Low\*/HACL\*, and translation validation.

**Deliverable:** `research/2026-11/USABLE-L.md`. It covers the caps and what lifts each one, the trust story at scale, the cost of a construct, the milestone, the route as planned items, and what is not claimed. Ring 0 items in the route are G-0. `PLAN-2026-10.md` is not edited.

## Log
- 2026-11-08, **filed and planned**, on branch `spike/usable` from `master` at `870c4e4`. RC-02 is paused after its step 1.
