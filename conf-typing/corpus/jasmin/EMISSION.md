# Does anyone actually emit a certificate? — the stage D kill criterion, checked

Stage D's kill criterion: *if no external tool emits a machine-readable certificate we can
consume (rather than prose in a paper), this reduces to a manual encoding exercise and
should be scoped as such rather than sold as a pipeline.*

That is an empirical question about two real tools, and it was answered by looking rather
than by assuming. **The verdict is split**, which is why this file exists instead of a
sentence in a commit message.

## Jasmin — yes

The SCT checker prints an inferred signature per function (`pp_funty`, driven by
`compiler/tests/sct-checker/accept.ml`), and the project checks the output into the repo as
`accept.expected` and diffs against it in CI. A tool that regression-tests its own output
text is a tool whose output text is stable enough to parse.

One entry, verbatim:

```
modmsf f : #transient ->
#secret
output corruption: #public
 constraints:
```

Four accumulating facts per function: the **MSF-clobber flag** (`modmsf`/`nomodmsf`), the
input type, the **output SCT level**, and the **output corruption** level, plus a
constraint set for the polymorphic cases.

This is a *statement of what was established*, which is the thing a composition layer needs.
`accept.expected` is copied verbatim into this directory and is what `certcompose` reads.

**Measured on it: 57 certificates, 20 with a level this model receives.** The other 37 are
polymorphic (`#poly = { n = k, s = k}`) or compound (`#[ptr = …, val = …]`) and have no
image in `SLvl`. They are recorded as unreceived rather than flattened into a ground level,
for the same reason the CWE corpus recorded inexpressible tasks instead of adapting them.
**35% is the honest coverage figure**, and the gap is a real limitation of the receiving
model, not of Jasmin.

## CN — no

Three things CN emits, none of them a certificate:

1. **JSON.** There is a `--json` path and a reader, `tools/scan_cn_json.py`. It is a
   **timing log**. The reader's own first line is `# for reading the JSON (ish) timing
   output`, and its parser is introduced with `# FIXME: this next bit is a total hack`
   because it recovers objects by scanning for `'"name": "function"'` and walking
   backwards to a brace. Timings, not guarantees.
2. **Coq export** (`-pf`, `tests/cn/coq.json`). This emits proof **obligations** plus a
   supporting library (`coq/CN_Lemmas/`, `coq/Cerberus/`) — work to be discharged, which is
   the opposite direction from a guarantee to be received. Consuming it would mean
   re-proving in Coq, not accumulating what CN established.
3. **Exit status and console prose.** `CN verify: SUCCESS`.

So for CN there is nothing to consume, and **the kill criterion fires**: the CN half of
this repo's composition story is a manual encoding exercise and is scoped as one in
`CNReceive.lean`.

## What this means for the plan

The criterion said *no external tool*. One does, so the direction is not killed — but the
"pipeline over two real tools" framing was too strong and has been corrected to:

- **Jasmin: a pipeline.** `certcompose` reads emitted bytes, parses them (machine-checked
  on real samples in `ConfTyping/JasminCert.lean`), accumulates by the stage-C law, and
  prints the composite with its trusted base.
- **CN: a hand encoding**, as `CNReceive.lean` has said since stage B.

The composite of *two different tools* therefore still cannot be built from consumed
artifacts alone. That remains open, and it is a fact about what the ecosystem emits rather
than about the algebra.

## Sources

- Jasmin SCT checker and its expected output: `compiler/src/sct_checker_forward.ml`,
  `compiler/tests/sct-checker/{accept.ml,accept.expected}`, jasmin-lang/jasmin.
- Typing High-Speed Cryptography against Spectre v1, IEEE S&P 2023.
  <https://eprint.iacr.org/2022/1270>
- Preservation of Speculative Constant-Time by Compilation, POPL 2025.
  <https://eprint.iacr.org/2024/1203.pdf>
- CN JSON reader: `tools/scan_cn_json.py`; Coq export config: `tests/cn/coq.json`;
  Coq support library: `coq/CN_Lemmas/`, rems-project/cn.
