---
id: INJ-01
title: "Rows 3 on bytes: untrusted input cannot change the structure of what reaches a typed sink, with sanitizers that are loops"
ring: 1
tier: G-X
milestone: M4 (2027-02-12)
deps: [STR-01]
closes: ['VULN-COVERAGE §3.0 row 3: loop-free, on ucmdLangI, carried by no pass', 'EXPR-04: san is quote-only but reads as a general sanitizer']
acceptance: Cert.trace on the literal image by transfer alone, saying that what reaches the sql sink has the program's literal skeleton for every untrusted input; the sanitizer is a loop written in L and accepted by a checked rule; refused: a concatenation with no sanitizer, a sanitizer that passes one delimiter, and a string sanitized for one sink sent to another; each refused image shows the changed structure under QEMU
kill: if a sanitizer's loop cannot be accepted by a kernel-evaluated checker, stop and report; the fallback is a stated set of primitive sanitizers, recorded as a limit
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track A, 2027-01-25 to 2027-02-12. The rule to start from is `ConfTyping.tcheck_traceI` (`InjectionL.lean`), which counts delimiters and has no loop rule on L.

1. **Sinks are typed.** Each sink has its delimiters: `sql`, `html`, `log`, `shell`, `fs`. A string's taint says for which sinks it is clean.
2. **The sanitizer rule.** A loop that writes an input byte only on the branch where it was compared with each of the sink's delimiters, and writes an escape on the other. The rule is syntactic and checked by evaluation.
3. **The property** at the sink: the delimiter positions of the emitted bytes do not depend on the untrusted input. As a `Cert.trace` it is stated per program, from the program's literals.
4. The image, by transfer.
5. **`EXPR-04` is settled here**: a string cleaned for `sql` is refused at `fs`, which is what blind program 06 does.
6. Witnesses, QEMU runs of each refused image with an attack string, mutants.

**Not claimed:** that the database parses as the delimiter table says. That table is the trust assumption, stated in the item's note.

## Log
