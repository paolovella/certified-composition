---
id: ISO-01
title: "Row 7 on bytes, isolation: tenant B's sink shows nothing of tenant A's data, on the literal image"
ring: 1
tier: G-X
milestone: M3 (2027-01-08)
deps: [L-IO]
closes: ['VULN-COVERAGE §3.0 row 7: isolation holds on ucmdLangI, and no pass carries it']
acceptance: Cert.relView on the literal image by transfer alone, at an observer that reads tenant B's sink and a relation that fixes B's data and the public input; the item names its attacker; a refused program that copies A's data to B's sink, whose image shows the difference under QEMU
kill: if the tenant's observer is not preserved by the passes' view conditions, stop and report
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track A, to 2026-12-23. The rule to start from is `ConfTyping.Tenant.tenantCheck_relView`. It is fifth in the cut order (§5).

1. **The attacker, stated first:** tenant B, who chooses its own input, reads its own sink, and sees no leakage. A stronger attacker who also sees time is `ctCheck`'s, at the partition where A's data is secret, and the item says which one each witness is about.
2. `tenantCheck` on `Slice2.Prog`, with two partitions.
3. `Cert.relView` at the source, and on the image by the existing `relView` transfer (`RC-02` carried one with `noOut`).
4. Witnesses and mutants, as for `MED-01`.

## Log
