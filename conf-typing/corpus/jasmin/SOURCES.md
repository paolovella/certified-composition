# Jasmin SCT — the second producer, transcribed

Not written by me, and not written for this repo. Stage C's first pass used an
SCT-*shaped* certificate that I invented (`sctGA`, a public set accumulating by
intersection). This is the second pass: the real thing, read rather than recalled.

## The tool

**Jasmin**'s speculative-constant-time type system — a value-dependent information-flow
type system that enforces SCT, i.e. protection against Spectre v1.

> Typing High-Speed Cryptography against Spectre v1. IEEE S&P 2023.
> <https://eprint.iacr.org/2022/1270>

Checker source: `compiler/src/sct_checker_forward.ml`, jasmin-lang/jasmin.
Test corpus: `compiler/tests/sct-checker/{success,fail}/`.

## The structure that matters: a level is a PAIR

This is the fact that makes the transcription worth doing, and I did not have it right
from memory. A Jasmin SCT level is **two** levels, one for normal execution and one for
misspeculating execution:

| Jasmin name | pair | meaning |
|---|---|---|
| `public` | ⟨L, L⟩ | public normally **and** under misspeculation |
| `transient` | ⟨L, H⟩ | public normally, **secret under misspeculation** |
| `secret` | ⟨H, H⟩ | secret either way |

The explicit pair syntax appears in the source itself — `fig5a` below is annotated
`{ normal: d, speculative: secret }`. `transient` is the abbreviation for the mixed case.

**`transient` is the exact shape of the stage-C finding.** A CN certificate is a fact
about the architectural machine only; carried into a speculative world it is public
normally and unconstrained under misspeculation. Jasmin already has a name for that, and
it is not `public`. The first pass found the gap; the second pass discovers the gap was
already named by the other tool.

## The mechanism: MSF and `#protect`

Misspeculation is tracked in a register — the **misspeculation flag**. `#init_msf()`
initialises it (it is a fence), `#update_msf(b, ms)` refreshes it after a branch on `b`,
and `#protect(x, ms)` masks `x` when execution is misspeculating. `#protect` is what
turns a `transient` value into a `public` one.

## `fig3a` — the S&P 2023 paper's Figure 3a, verbatim

Source: `compiler/tests/sct-checker/success/paper.jazz`, jasmin-lang/jasmin.

```jasmin
param int N = 20;

#[sct =
  "{ ptr: transient, val: transient } * { ptr: transient, val: secret } * transient -> { ptr: public, val: secret }"
]
// ct = "public * secret * public -> secret"
fn fig3a(
  reg const ptr u64[N] p,
  reg mut ptr u64[N] w,
  reg u64 i)
  ->  reg mut ptr u64[N] {
  reg u64 ms x;
  reg bool b;
  ms = #init_msf();
  x = 0;
  b = i < N;
  if b {
    ms = #update_msf(b, ms);
    x = p[i];
    x = #protect(x, ms);
  } else {
    ms = #update_msf(! b, ms);
  }
  w[x] = 0;
  return w;
}
```

**This is the same gadget stage C's first pass built abstractly**, which is the reason to
anchor here rather than anywhere else: a guarded load `x = p[i]` whose *value* becomes the
*address* of a second access `w[x] = 0`. Architecturally the guard `i < N` makes it safe.
Under a mispredicted branch the body runs with `i` out of bounds, and without
`#protect` the second access leaks the out-of-bounds value as an address.

`x = #protect(x, ms)` is the fix, and note where it sits: **inside** the branch, after the
load, before the value is used as an address.

## `fig5a` — the explicit pair syntax

```jasmin
#[sct = "
  { ptr: public, val: { normal: d, speculative: secret } } -> { normal: d, speculative: d }
"]
fn fig5a(reg const ptr u64[N] p) -> reg u64 { ... }
```

## What was modelled, and what was dropped

| Jasmin has | stage C second pass | why |
|---|---|---|
| the level **pair** ⟨normal, speculative⟩ | **received**, as `SLvl` | it is the structure the finding is about |
| `public` / `transient` / `secret` | **received**, as the three inhabitants | `transient` is the finding |
| level **join** along composition | **received**, as `sctLvlGA`'s `mul` | a genuinely different monoid from CN's union |
| `#protect` / MSF | **modelled by its effect only** | the transient access contributes nothing outside the footprint |
| value-dependence, arrays, `ptr`/`val` split, `#update_msf` placement | **not modelled** | none of it bears on the composition law |

## The reception gap, stated plainly

As with CN: nothing here proves that Jasmin's `#[sct = ...]` annotation *implies* the
predicates used in `JasminSCT.lean`. That is Jasmin's soundness theorem over its own
semantics. The encoding is by hand and unchecked against the Jasmin checker; no `.jazz`
file is parsed and no Jasmin output is consumed.

The speculative machine here remains one schedule parameter and an address trace. Jasmin's
is a real machine with directives, and its SCT statement quantifies over adversarial
speculation far beyond a single misprediction window.
