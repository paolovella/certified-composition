---
id: SPEC-01
title: "A speculating RV64 model, driven by the attacker's directives, with the ordinary model as its special case"
ring: 1
tier: G-X
milestone: M6 (2027-03-19)
deps: [S-SPEC]
closes: ['VULN-COVERAGE §3.0 row 9: speculation is modelled on ucmdLangW, with a window, and no machine']
acceptance: rvSpecLang, a lawful Lang whose input carries directives; with no misprediction directive its runs are rvLang's, proved; a Spectre v1 gadget's image leaks in it, by decide; both passes carry certificates to it for the slice language's speculating semantics; the hardware contract it assumes is written down, with what no test here can check
kill: if S-SPEC's verdict needs a kernel change and the user declines it, this item and SPEC-02 leave 1.0 with a record (cut 4)
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track A, 2027-02-15 to 2027-03-05. The design is `S-SPEC`'s verdict, and this plan is rewritten from it. What is fixed now:

1. **Scope: conditional branch misprediction only.** No store-to-load forwarding, no return or indirect-jump prediction. The slice has no indirect jump, and `jal` is direct.
2. **No comparison with QEMU.** QEMU does not speculate. The comparison is with `rvLang` on directive streams that never mispredict, and the contract is the trust assumption. The release says this.
3. If the model lives in the hardware contract (Ring 0, `PLAN-2026-10` §2), the item is a proposal for the user's key. `S-SPEC` settles where it lives.

## Log
