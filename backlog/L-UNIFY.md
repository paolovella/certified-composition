---
id: L-UNIFY
title: "One language for L's certificates: combine ucmdLangI, ucmdLangW and ucmdLangH, and carry them through passes at every window"
ring: 0
tier: G-0
deps: [F5]
closes: ['F5: certificates on separate languages, not carried through a pass']
acceptance: one lawful language, indexed by window, of which ucmdLangS, ucmdLangI and ucmdLangH are proved special cases; one theorem giving a single program its properties together; splitPass carries them at every window; no frozen statement changes
kill: if det for the pointwise family cannot be proved on the revised window, or the design needs a kernel change, stop and bring the evidence to the user. Fallback, already designed - typing preservation (step 5), which carries only bcheck's rel
status: planned
---

## Plan

The user's decisions of 2026-11-03: design a window-aware pass relation, and F6's lock waits for this
item. Designed, not built. Probes ran on the current machine; no Lean is changed yet.

**The gap.** F5 stated each property on its own language. Rows 3, 14 and 7b are on `ucmdLangI`, row 9 on
`ucmdLangW`, row 6's leaks on `ucmdLangH`. No theorem gives one program several of them at once, and
`splitPass` is over `ucmdLangS`, so none reaches compiled code. `tools/ring0.lock` names `ucmdLangS` and
`ucmdLangT`, and not the three variants or `splitPass`.

**The language.** `ucmdLangC P π w`: strings as an input, window `w`, and the exit report.
`ucmdLangS`, `ucmdLangI` and `ucmdLangH` are proved special cases: window 0, plus empty strings or no
report. Frozen statements stay as they are, because those languages are not redefined.

**The window-aware relation: a family of passes, one per window.**
`splitPassC : ∀ w, PassCert (ucmdLangC P π w) (ucmdLangC P π w)`. `PassCert` already takes any two
languages, so this needs no kernel change, and each transfer applies pointwise: a source certificate at
window `w` gives the target's at the same `w`. Two passes compose by `PassCert.seq` at each `w`.

**Why the same window works.** Each source command becomes one or more target commands, so a target
window covers no more of the program than the source's. The target's transient addresses are a prefix
of the source's, of a length fixed by the syntax. Probe on `if 0 { x := a+b+c; deref s }`, source and
target addresses by window:

| w | source | target |
|---|---|---|
| 0, 1 | none | none |
| 2 | the secret | none |
| 3, 4 | the secret | the secret |

**What breaks: `det` on the current machine.** `transRun` runs a nested `ite` or `loop` as one command
under `uexec 30`. Splitting deepens the command, so past the cap a target window stops where the
source's does not. Probe at window 2 on `if 0 { if s { x := 1+1+...+1 } ; deref p }`, with `n` additions:

| n | source, s=1 | source, s=0 | target, s=1 | target, s=0 |
|---|---|---|---|---|
| 5 to 29 | p | p | p | p |
| 30 to 40 | p | p | none | p |

From `n = 30` the source's views agree and the target's differ, so `det` is false for that program at
that window, and the compiled program leaks `s` where the source does not. `bcheck` refuses the program,
but `det` covers every program. Counting a nested command's own steps against the window would remove
the cap and, by the same reasoning, keep the failure: a secret branch with a long split arm would use up
the window. That last point is argued, not probed.

**The fix: a transient window ends at a nested `ite` or `loop`.** Every transient command is then
atomic, `uexec 30` goes away, and which commands the window reaches depends only on the syntax. A
transient fault only stops later addresses, so the source's list still fixes the target's prefix.
- **Cost:** a weaker attacker for programs with a memory access after a nested branch in an untaken
  branch. Row 9 is recorded as a correction, and `SpecFused` keeps the stronger model on `uexecS`.
- **Rejected:** `comp` refusing programs with nested commands in a branch, which refuses counted loops
  there. Weakening `det` to related inputs, which is a Ring 0 change to what every pass proves.

**Steps.**
1. Revise the window in `ucmdLangW`, and keep both probes as tracked witnesses. Re-prove
   `transW_agree`. The second probe becomes the theorem that the old model breaks `det`.
2. The prefix lemma: `transW w (flatten (split b))` is a syntax-fixed prefix of `transW w (flatten b)`.
   Riskiest step, and the kill rule's measure, with `det`.
3. `ucmdLangC`, its lawfulness and its special cases. `split_reflect` also exposes the final `live`.
4. `splitPassC`, by `behind` and `ahead`, which already take any state. New cases: at an `ite`, `det`
   peels the transient addresses, which works because the next entry is a step marker, and `cost_sim`
   needs `m' ≤ Lc * m`.
5. **Independent of the above, and the fallback:** `JSecTy P V c V'` gives `JSecTy P V (split c) V'`.
   With `runW_same`, this is `bcheck`'s `rel` on compiled code, at every window, on the stronger model.
   It carries nothing else, and later passes (stack code, RISC-V) will not keep the typing, so it does
   not replace the family.
6. The carried theorems, and one theorem giving a single program its properties at one partition. Row 4
   picks that partition. Then rows 3, 14, 7b, 9 and 6's leaks change in §3.0's pass column.

**Open questions.**
- `bound` on `ucmdLangC` must grow with the window. `k * (1 + w)` is `spec_cost_bound`'s form on `uexecS`,
  and has to be re-proved here. Mediation and faults are unaffected.
- A window chosen at the source says nothing about a processor until PH5's hardware contract states one.
  Every certificate here holds for all `w`, so PH5 needs only the existence of a window.
- Attackers stay per certificate: `rel`, `relView` and `trace` each name theirs, as F5 decided.

## Log
- 2026-11-03, *correction of a claim made in conversation, not in a document.* The review of this plan
  said the compiled program's leakage at a window cannot be worked out from the source's, and that a
  window-aware relation would probably need a kernel change. The first is true only past the fuel cap,
  and the second is false on this design. The first table above is the evidence.
- 2026-11-03, **this design is held.** Research in
  [`research/2026-11/SPECULATION-PASSES.md`](../research/2026-11/SPECULATION-PASSES.md) recommends
  replacing the window with attacker-chosen directives, and finds that this plan's fix, ending a window at
  a nested branch, loses a known leak. The user decides. Until then, do not start the steps above.
- 2026-11-03, **held by the user's decision: the vertical slice comes first** (VS-1). The directive question is not
  decided. It returns with what VS-1 finds about `enc`.
