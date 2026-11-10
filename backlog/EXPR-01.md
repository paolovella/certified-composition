---
id: EXPR-01
title: "Document the secret-pointer rule, and make certcheck say when it fires"
ring: 3
tier: G-D
deps: [S-EXPR]
closes: ['S-EXPR follow-up']
acceptance: a blind reader of the reference can write an accepted secret cell; certcheck names the unmarked pointer when it refuses for this reason
kill: -
status: blocked
---

## Plan

S-EXPR's false refusals 09, 10 and 22 have one cause. `secret x` is accepted only when the
pointer variable `x` is itself in the `--secret` partition (`FullCert.lean`, the `allocS`
case). No document says so: not the README, not `conf-typing/README.md`, and not the
reference the blind author was given.

1. State the rule where the surface syntax is documented (the README's "Running it" section
   and `conf-typing/README.md`). Write a v2 of the author reference
   (`corpus/blind/REFERENCE-v2.md`). The v1 reference is the frozen measurement input and stays
   unchanged.
2. `certcheck`: when the program has a `secret x` whose `x` is not marked secret, print that as
   a hint on refusal (Ring 3: the hint is untrusted text; the verdict is unchanged).
3. Witnesses: `09.uc` without the flag is refused and the hint names `tokcell`; with the flag it
   is accepted. `tools/ci.sh` checks both, as it does the documented examples.

## Log

- 2026-10-28: steps 1 and 2 done. The rule is stated in the README ("Running it") and in `corpus/blind/REFERENCE-v2.md` (v1 unchanged). `certcheck` prints a hint naming each unmarked `secret` pointer on refusal; checked by hand: 09 refused with `hint: secret tokcell ...`, accepted with `--secret token,tokcell`, `use-after-free.uc` refused with no hint. Step 3's CI witness edits `tools/ci.sh` (Ring 0), so it goes in a separate PR for the user's key.
- 2026-11-10, **judged against the acceptance, clause by clause ([`M0-01`](M0-01.md)): not done. `blocked`, on two things that are the user's to start.**
  - *"a blind reader of the reference can write an accepted secret cell"*: **not tested.**
    - The rule is in `corpus/blind/REFERENCE-v2.md` (the `secret p` row of its table, and its paragraph on secrets) and in the README's "Running it".
    - No reader has been given the v2 reference. `EXPR-05`'s second author wrote from v1, as its acceptance asked. So whether a blind reader now gets it right is not known.
    - The test is one isolated author, the v2 reference, and the three tasks that failed for this reason (09, 10, 22). This session starts no agent without the user's word.
  - *"certcheck names the unmarked pointer when it refuses for this reason"*: met, checked by hand today at `e6e50d3`, and held by no CI step.
    - `corpus/blind/p/09.uc --secret token`: refused, exit 3, with "hint: `secret tokcell` is refused unless `tokcell` is itself marked secret (--secret ...,tokcell)".
    - The same file with `--secret token,tokcell`: accepted, exit 0.
    - `examples/rejected/use-after-free.uc`: refused, exit 3, with no hint. So the hint is not printed on every refusal.
    - Plan step 3, the CI witness for these three runs, is not done. It edits `tools/ci.sh`, which is Ring 0, and no proposal for it has been opened.
  - **What unblocks it:** the user's word for the blind reader, and a Ring 0 proposal for step 3. Or the user's word to kill it: `certcheck` and its reference move to the museum at RC with the rest of `conf-typing`, and `BLIND-01` measures the same 40 tasks on L with a reference of its own.
