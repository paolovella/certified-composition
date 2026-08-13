# External corpus results — 2026-08-13

12 programs transcribed from CWE demonstrative examples (`SOURCES.md`), all written before
the checker was run once. Command: `certcheck ext/bNN.uc`.

## Detection: 6 of 7 real vulnerabilities caught

| id | CWE | what it is | verdict | |
|---|---|---|---|---|
| b01 | 416 | write through a freed pointer after two intervening allocations | REJECT | ✅ caught |
| b02 | 416 | conditional free, then use under a second condition | REJECT | ✅ caught |
| b04 | 862 | protected read with no authorization check | REJECT | ✅ caught |
| b07 | 89 | query built by concatenating untrusted input | REJECT | ✅ caught |
| b09 | 835 | retry loop with no exit bound | REJECT | ✅ caught |
| b11 | 835 | loop whose counter never decreases when the input is zero | REJECT | ✅ caught |
| b06 | 401 | allocation not freed on the error path | **ACCEPT** | ❌ **missed** |

**The miss is a scope hole, not a soundness bug.** The memory certificate covers
use-after-free, double-free and wild dereference. **It says nothing about leaks**, and
`VULN-COVERAGE.md` never claimed CWE-401. The corpus makes the gap concrete: *no
certificate in this repo detects a leak*, and the checker will happily accept a program
that allocates on a path and never frees. Anyone reading "memory safety, certified" would
reasonably assume otherwise, so it is written down here.

Corpus A's program 21 (`for i = 5 { alloc t } ; free t`) was recorded as a correct refusal
"because it leaks". **That reason was wrong** and is corrected here: it is refused because
the loop rule requires the tracked set to be a fixpoint, which is a different fact that
happens to coincide. Leak detection is not among the guarantees.

## Precision: 4 of 5 safe programs accepted

| id | CWE | the good version | verdict | |
|---|---|---|---|---|
| b03 | 416 | use before free | ACCEPT | ✅ |
| b05 | 862 | authorize, then read | ACCEPT | ✅ |
| b08 | 89 | validate the input, then build the query | ACCEPT | ✅ |
| b10 | 835 | bounded retry with a counter | ACCEPT | ✅ |
| b12 | 835 | **validate the rate up front, then loop** | **REJECT** | ❌ **false rejection** |

**b12 is the finding.** It is not a program I invented to stress a rule — it is *the fix
CWE-835 tells developers to write*. The good version of Example 2 is still an unbounded
`while`; what makes it terminate is an up-front validation (`if (rateSold < 1) return;`).
Our counted-loop rule accepts a loop only when the bound is a **syntactic constant**, so
the checker rejects the recommended fix.

Rate on this corpus: **1 false rejection in 5 safe programs (20%)**, and 6/7 detection.

## What this changes

1. **The next rule is now defined by evidence, not by taste.** The counted loop must accept
   a bound that is a *variable validated by a guard* — `if n ≤ K then for i = n { … }`,
   with the budget taken from `K`. That means the checker has to carry what the guard
   established into the branch: **the first value-dependent rule in this repo**. It is also
   the shape Jasmin's information-flow type system already uses (value-dependent levels),
   which is a good sign about the direction and a reminder about who got there first.
2. **Leaks need saying out loud** in `VULN-COVERAGE.md` rather than being absent by
   omission.
3. **20% on five programs is not a precision figure**, it is a pointer. The number that
   would mean something needs hundreds of cases; what this corpus bought is the *identity*
   of the failing rule, which twenty-five author-written programs could not find.
