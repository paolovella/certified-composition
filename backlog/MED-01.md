---
id: MED-01
title: "Row 7 on bytes, mediation: every read of a resource is preceded by its check, on the literal image"
ring: 1
tier: G-X
milestone: M3 (2027-01-08)
deps: [L-IO]
closes: ['VULN-COVERAGE §3.0 row 7: mediation holds on ucmdLangS, which does not compile']
acceptance: a checker on the slice language whose acceptance gives Cert.trace on the literal image by transfer alone, for the property that each Ev.read r follows an Ev.check r; an accepted handler, with a loop; a refused one that reads first, whose image shows the read before the check under QEMU
kill: if the order of events is not kept by a pass as it stands, so that the transfer needs a lemma about this certificate, stop and report
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track A, to 2026-12-23. The rule to start from is `bcheck`'s threaded rights (`ConfTyping.bcheck_mediatedS`, `Mediation.lean`).

1. `medCheck` on `Slice2.Prog`: the set of checked resources is threaded through the commands, joined at `ite`, and a loop's body must keep it.
2. Soundness at the source: `Cert.trace (sliceLang …) mediated p`.
3. The image: by `slice_carries` and `pipeline_comp`, with no pass lines.
4. Witnesses: accepted and refused, as the acceptance says. A second refused case: the check on one branch only.
5. Mutants: the rule that forgets a branch, and the rule that lets a loop drop a right.

**Not claimed:** that the policy is right. The monitor's answer is an oracle, as the map's row 7 says of policy correctness.

## Log
