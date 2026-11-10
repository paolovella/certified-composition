---
id: S-SPEC
title: "Spike: does a speculating RV64 model, driven by directives, fit the kernel as it stands?"
ring: 3
tier: G-P
milestone: D2 (2027-01-12)
deps: [RC-03]
closes: ['L-UNIFY, held since 2026-11-03: the directive question was never decided', 'PLAN-2026-11 §4: whether row 9 needs a kernel change is the user''s decision on 2027-01-12']
acceptance: research/2027-01/S-SPEC.md with a verdict, from Lean that builds: a speculating step for the slice's branch, in the source and in the machine, with the attacker's directives as part of the input; either one pass certificate carrying Cert.rel for one program with a branch, or the exact place where PassCert's enc does not fit, as a goal that cannot be closed; the cost in lines against VS-1's
kill: if two weeks do not give a verdict either way, report what was tried, and cut 4 applies
status: planned
---

## Plan

From [`PLAN-2026-11`](../PLAN-2026-11.md) §3, Track B, 2026-12-21 to 2027-01-12, around the break. A spike: its output is a verdict, and nothing it writes enters the build.

The question comes from [`SPECULATION-PASSES.md`](../research/2026-11/SPECULATION-PASSES.md). The field's method lets the attacker choose each branch by a stream of directives, and has no window in the source. A pass then needs two maps, one on leakage and one on directives. The kernel's `PassCert` has `enc` on inputs and `cover` on runs. Whether the directive map is an `enc` is what `VS-1` left open.

1. **Read the paper first.** The research note read the slides, not Arranz Olmos et al.'s text. If the fetch is refused again, the report says so.
2. **The model**, in a scratch file: the input is the program's input and a directive list. A mispredicted branch runs the other arm with a flag set, and the run ends at the next directive that says so. No rollback, as their no-backtrack theorem allows.
3. **One pass**, the slice's `slots` or `lower`, on one program with one branch: does `PassCert` hold with the directives carried by `enc`?
4. **The verdict**, one of:
   - it fits, and `SPEC-01` goes ahead as planned;
   - it fits only for an attacker who mispredicts and sees `Lk` events, with `rel` alone (cut 4's narrow form);
   - it needs a kernel change, stated as a diff of `Kernel/Cert.lean`, for the user to accept or decline.

**Vacuity:** the model must show a leak. A Spectre v1 gadget's two runs differ under some directive stream, by `decide`.

## Log
