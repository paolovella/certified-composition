---
id: MUL-01
title: "Multiplication and 128-bit sums: mul and mulhu in rvLang, and uint128_t read as two words with explicit carries"
ring: 1
tier: G-X
deps: [CAP-01, W32-01]
closes: ['S-USABLE §4: fe25519_mul and Poly1305 need 64x64 to 128-bit products']
acceptance: mul, mulhu and sltu in rvLang, compared with QEMU, each with a broken model; the language's products and two-word sums through both passes; the reading of uint128_t stated and tested against clang on products at the extremes
kill: if a product's leakage differs between the model and the hardware contract the project states, stop and report (multiplication's timing is data-independent on the targets the contract names, or it is ledgered)
status: blocked
---

## Plan

From [`USABLE-L`](../research/2026-11/USABLE-L.md) §5, item 7. RV64M's `mul` and `mulhu`; carries by `sltu`, since RISC-V has no flags.

## Log
- 2026-11-10, **parked past L 1.0**, by the user's decision of that day ([`PLAN-2026-11`](../PLAN-2026-11.md) §0 and §6): the crypto route stops at M1 (HChaCha20), and the rows of the vulnerability map come next. Status `planned` to `blocked`. Nothing found against the plan above.
