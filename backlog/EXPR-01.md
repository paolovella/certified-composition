---
id: EXPR-01
title: "Document the secret-pointer rule, and make certcheck say when it fires"
ring: 3
tier: G-D
deps: [S-EXPR]
closes: ['S-EXPR follow-up']
acceptance: a blind reader of the reference can write an accepted secret cell; certcheck names the unmarked pointer when it refuses for this reason
kill: -
status: planned
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
