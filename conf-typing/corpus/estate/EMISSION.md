# Stage E — the emission census, run rather than read

`PLAN-MULTITOOL.md` stage E: for each tool in the estate, **what does it actually emit**,
is it consumable, and what shape is the guarantee? Stage D established the method and why
it matters — CN's JSON turned out to be a timing log — so nothing here is taken from
documentation. Every row was produced by **running the tool on the estate's own artifacts**
on 2026-08-14, and the bytes are in `captures/`.

Estate: `/home/paolo/.vella-workspace/sentinel/formal` — 59 Verus kernels, 124 Kani
harnesses, 48 TLA+ specs, 8 Coq files, 6 Lean files, 2 Alloy models, 17 allowlisted
escape hatches.

## The table

| tool | emits a certificate? | carries its **bound**? | carries its **trusted base**? |
|---|---|---|---|
| **Coq** | **yes** — `Print Assumptions` | n/a (unbounded) | **yes, exactly** |
| **Lean** | **yes** — `#print axioms` | n/a (unbounded) | **yes, exactly** |
| **Kani** | **yes** — per-check `RESULTS` block | **yes**, via `.unwind.N` status | no |
| **Alloy** | **yes**, but **split across two files** | **yes**, in `receipt.json` | partly (`solver`) |
| **TLC** | **yes** — completion + a numeric caveat | instance is in the `.cfg`, not the output | **a probability**, emitted |
| **Verus** | not assessed — not on `PATH` here | — | — |
| refinement | no — one markdown file | — | — |
| tools | n/a — 11 shell scripts, the glue | — | — |

**Six of eight emit something consumable.** Stage E's kill criterion was fewer than three.
It did not fire.

## Coq and Lean emit the ledger itself

```
Axioms:
trusted_fs : forall n : nat, n + 0 = n
```
```
't1' depends on axioms: [trusted_fs]
't2' does not depend on any axioms
```

This is the closest fit to this repo's machinery of anything found so far — closer than CN
or Jasmin. `Ledger` *is* a list of assumptions, `needs` computes one from an artifact, and
`Print Assumptions` / `#print axioms` **are that computation, already implemented, already
per-theorem**. A discharged obligation literally prints as "does not depend on any axioms",
which is `condBoundary_nil`.

## Kani: the unwind annotation is not the bound

The finding that would have been got wrong by reading rather than running.

`#[kani::unwind(4)]` looks like a caveat on the guarantee. **It is not.** It is a search
parameter, and the epistemic status is reported separately, as a check:

```
Check 32: proofs::k_bounded_loop.unwind.0
	 - Status: SUCCESS
	 - Description: "unwinding assertion loop 0"
```

With unwinding assertions on — Kani's **default** — an insufficient bound makes verification
**FAIL**, not silently return a bounded result:

```
Check 32: truncated::k_truncated.unwind.0
	 - Status: FAILURE
SUMMARY: ** 1 of 32 failed (31 undetermined)
VERIFICATION:- FAILED
```

So: **all unwinding assertions SUCCEED ⟹ the loops were fully unrolled ⟹ the result is
unbounded.** Both cases were run (`captures/kani-unbounded.out`).

**Consequence for the estate, checked:** it sets `--no-unwinding-checks` and
`--unwinding-assertions` **nowhere**. So every one of its 124 harnesses that passes is
carrying an *unbounded* guarantee, and its 23 `#[kani::unwind(N)]` annotations are search
parameters, not caveats. The naive reading — "Kani is a bounded model checker, so its
results are bounded" — is **wrong here**, and stage F's bound gap does not apply to this
estate's Kani results.

## Alloy: the certificate is split across two files, and neither half is one

Console:

```
00. check S7_ForbidDominance       0       UNSAT
```

`receipt.json`, which the run also writes:

```json
"S7_ForbidDominance": {
  "bitwidth": 6,
  "scopes": ["4 AbacPolicy", "3 Attribute", "2 Principal", "3 EvalContext"],
  "source": "check S7_ForbidDominance for 4 AbacPolicy, ... 6 Int",
  "type": "check"
}
```
with `"solver": "sat4j"`, `"symmetry": 20`, `"coreMinimization": 2` at top level.

**The verdict is on stdout and the bound is in the receipt, and a consumer needs both.**
`UNSAT` alone is not a certificate — it is "no counterexample" with the scope silently
elided, which is precisely the reading `min_unsound` punishes. The receipt alone does not
say whether the check passed. This is the one tool in the estate whose guarantee is
genuinely bounded and whose emission requires assembling two artifacts to state it.

*(Correction of record: the first pass of this census reported that Alloy does not emit its
scope at all. That was read off stdout before the receipt was found. The receipt is written
into a directory beside the model, and it has the scopes.)*

**And the estate's wrapper discards both.** `tools/run-alloy-model.sh` reduces the run to
`Alloy checks passed: AbacForbidOverride.als` and greps the log for `Counterexample`. The
scope never reaches a consumer. That is not a criticism of the script — it was written to
gate CI, not to feed a composition layer — but it is exactly the seam stage H would have to
change.

## TLC: exhaustive over a finite instance, with a probability attached

```
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  calculated (optimistic):  val = 6.9E-7
  based on the actual fingerprints:  val = 2.6E-9
19193917 states generated, 685497 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 9.
```

Two things worth separating. `0 states left on queue` and *"the complete state graph"* mean
the search was **exhaustive over the model instance** — not truncated. The instance itself
is the bound, and it lives in the `.cfg` (`CONSTANT SinkClasses <- const_SinkClasses`, …),
not in the output.

And TLC **emits a numeric soundness caveat**: the probability that two distinct states
collided in the fingerprint and a reachable state was therefore skipped. That is a
*probabilistic* ledger entry, a kind neither CN, Jasmin, Coq nor Lean produces, and the
existing `Ledger = List Prop` has no place to put a number. Stated here as a gap in the
receiving machinery rather than in TLC.

## What this changes

1. **Stage E's kill criterion did not fire** — six of eight emit.
2. **Coq and Lean are the best reception targets in the estate**, not the exotic ones: they
   emit exactly the object `Ledger`/`needs` is about.
3. **Stage F's bound gap is narrower than feared but real.** Kani's results here are
   unbounded; TLC's are exhaustive-over-instance; **Alloy's are the genuinely bounded ones**,
   and Alloy is the tool whose bound is easiest to drop on the floor — it is in a second
   file, and the estate's own wrapper discards it.
4. **A new gap, found by running:** `Ledger` cannot express TLC's probabilistic caveat.

## Reproduction

- Alloy: `java -jar alloy/alloy.jar exec --command "S*" alloy/AbacForbidOverride.als`
  (writes `receipt.json` into a directory beside the model).
- TLC: `bash tools/run-tla-spec.sh IntentScopeContainment` (21 s).
- Kani: `cargo kani` on the probe crate in this file's history; the two harnesses differ
  only in whether the unwind bound suffices.
- Coq: `coqc` on a file with one `Axiom` and one `reflexivity` proof, then
  `Print Assumptions`.
- Lean: `#print axioms` on the same shape.

Nothing in the sentinel estate was modified; the Alloy output directory the run creates was
removed afterwards.
