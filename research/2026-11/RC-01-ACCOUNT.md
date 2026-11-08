# RC-01: the account (2026-11-08)

The question came from the review of 2026-11-06: **the security work never meets real code.** The user chose "Real C, at the source": a
front end that reads a subset of real C into L, and certifies it there, through to RV64 bytes. The first real code is libsodium 1.0.20's
`crypto_verify_16`. **It is certified constant-time on its literal image, by the kernel's transfers alone, and the kernel did not change.**

**The claim, exactly.** This C function, read into L and compiled by L's certified pipeline, is constant-time on the machine model. It is
**not** a claim that libsodium is constant-time: the libsodium people ship is compiled by Clang or GCC, which nothing here checks.
"Constant-time" is L's observation on `rvLang`: PCs, addresses, instruction count and termination. Not cycles, caches or speculation.

## 1. What now exists

| Step | What | File |
|---|---|---|
| 1 | The subset and its reading, on paper, against the pinned source and header | `research/2026-11/RC-01-READING.md` |
| 2a | `sub`, `xor`, `or`, `and`, `srli` in `rvLang`, each compared with QEMU, each with a broken model | `Slice/Rv.lean`, `test/rv_diff.py` |
| 2b | `^ \| & -` and `>> k` in the language, through both passes | `Slice2/Ops.lean` and the passes |
| 3 | `lbu`, and `loadB`: byte arrays as inputs, read at a public index, through both passes | `Slice2/Bytes.lean` and the passes |
| 4 | `ctCheck` and `ctCheck_relView`; one widening round in the loop rule | `Slice2/CT.lean`, `Slice2/Source.lean` |
| 5 | A front end for the subset, in Lean and kernel-evaluated; the vendored source hashed at every build | `Slice2/CFront.lean`, `CSrc.lean`, `Sha256.lean` |
| 6 | The certificate and a constant budget on the 180-byte image; QEMU and clang | `Slice2/CTBytes.lean`, `test/verify16_diff.py` |

**The headline theorem, `verify16C_ct_bytes`:** the program the front end reads from lines 60 to 75 and 79 to 83 of the pinned `verify.c`,
`volatile` and casts included, compiles to exactly the 180-byte image `verify16Image`, and that image has
`Cert.relView (rvLang secX) lowIn noRet`. On every two inputs, in every environment and at every fuel, its PCs, addresses, instruction
count and outcome are equal, whatever the two arrays hold. `verify16_bound_bytes` adds a constant budget: at most 905 instructions.

**What the test adds, and does not.** `verify16_diff.py` ran the image under QEMU on 92 pairs of arrays: every run equals the model, with
one trace and one cost, 452 instructions. Clang's compilation of the unmodified `verify.c`, run natively at `-O0` and `-O2`, gives the same
answer as L's image on all 92. That is how the reading of C is believed: by testing, not by proof. The kill criterion did not fire.

About 1,500 lines of Lean in seven new modules of the slice, and changes to the passes. No change to the kernel.

## 2. What the kernel needed

**Nothing.** `relView` and `relView_transfer` came with F6, and `bound_transfer` with PH1. Every pass proof is about the
machine's instructions, never about a certificate. That is the second time the design held on contact with something new: BOUND-01 needed
one additive shape, this needed none.

**What the slice needed** was ordinary growth: five instructions and `lbu` in `rvLang`, four operators, a shift and a byte load in the
language, and one change of rule (§3, item 1).

## 3. What went wrong, and what it teaches

Each item is in `backlog/RC-01.md`'s log, with its correction where one applies.

1. **The plan said no checker rule would change, and one had to.** `ctCheck secX verify16` came back false. `highC` took no fixpoint at a
   loop, and `d` is public at the head and secret after the body. A loop-carried secret accumulator is what constant-time code is made of,
   so `sliceCheck` could never have accepted it. One widening round fixed it, with every program accepted before accepted with the same
   state. **Lesson: the first real program found a gap in a rule that the existing witnesses had never exercised.**
2. **A witness claimed the wrong value**, and `decide` refused it: `crypto_verify_16`'s return expression is an equality test only for
   `d` at most 255, which C guarantees. At `2^64 - 1` it gives 0.
3. **A mutant harness retargeted itself silently** (step 3a). Inserting `lbu` beside `ld` moved one anchor onto the new instruction, and
   `ld`'s faulting leak went untested by any broken model. Found by reading the mutant table, and restored.
4. **Two footprint changes went to the user's key.** `Nat.bitwise` in Lean core brings `propext` into `eval` once the language can say `^`,
   and `Repr` for lists brings it into two derived instances. Both are the permitted axiom, and both are recorded for the merge.
5. **A gap a side agent found**: CI did not check the vendored source against the release's hash, so an agent could have edited the copy and
   the excerpt together. The build now hashes all four vendored files in Lean. Putting the pins themselves in Ring 0 is `TP-01`, the user's.
6. **Time budgets, again.** Route 2 grew from 151 to 196 s over RC-01, because every kernel re-checks every kernel-evaluated proof, and its
   budget was raised to 240 s on the user's word, as was lake check's, to 160 s. A concrete-run witness in step 6 cost 15 s per kernel check
   and was removed before any commit, since its content is covered by other theorems and the QEMU runs. With step 6, route 2 is at its
   budget again: `CTBytes` adds about 20 s to lean4lean, the slowest of the six, though under a second to Lean's own kernel (receipt
   `rc01-step6-kerneltime`). Both budgets are held for the user's key. **The kernel-evaluated witnesses are now the main cost of CI, and
   they grow with every real program.** The machine's steps are what cost: a literal image is no faster than a compiled one.
7. **A CI run was lost** when the machine's VM went down mid-run (`incidents/I-0004.md`). Nothing was lost but the run.

## 4. The trust base of `verify16C_ct_bytes`, for a real run

VS-2's, unchanged: the Lean kernels and the six that re-check them; `rvLang`, compared with QEMU and not linked to Sail; the ELF wrapper and
the loader; QEMU as the only machine; the kernel's definitions. **Added by RC-01:**
- **The reading of C** (`RC-01-READING` §3): LP64 and glibc's 64-bit `uint_fast16_t`, the result read as the low 32 bits of the word, and
  `volatile` read as nothing. Believed by testing against clang on 92 pairs, not proved.
- **The vendored text**, pinned by sha256 in an ordinary file until `TP-01`.

## 5. What of C is still out of reach

The front end reads one shape of function, and refuses the rest. Refused today, each with a witness in `CFront.lean`:
- **Control:** `if`, `!=` and early `return` (so the leaky early exit is refused by the parser, not the certificate); `while`, uncounted
  loops and loops not starting at 0; `goto`.
- **Data:** pointer arithmetic other than indexing; writes through a parameter; arrays of a length other than 1, 2, 4 or 8 words; one array
  read twice in a statement.
- **Arithmetic:** division; signed `>>`; `int` values not bounded by the check; shifts of 64 or more.
- **Program structure:** calls other than `static inline` with literal arguments; anything the preprocessor would decide. One function per
  image: no calls in the compiled code, no stack, no separate compilation (PH6).

Of these, **writes to an output array and `if` on public values** are what the next real functions need: the field arithmetic
of `crypto_scalarmult`, for one, stores its results, and most real code branches on public lengths.

## 6. Recommendations

**On the merge.** RC-01 meets its acceptance, with CI green on substance. Branch `rc/real-c` carries two footprint changes, and route 2's
and lake check's time budgets (245 s against 240, 166 s against 160 on the quietest run), for the user's key, each in the log. `TP-01` should be taken with the merge, since the claim "read from libsodium's text" rests on the pins.

**On what comes next.** In order of what I would do:
1. **Output arrays**: a write-only byte array, stored with `sb`, through both passes. It opens every function that returns data, not a flag.
2. **`if` on a public condition** in the front end. The language and the checker already have `ite`; only the reading is missing.
3. **Make the kernel-evaluated witnesses cheaper**, or move the heavy ones out of route 2's closure. At the current rate, each real
   function adds 20 to 40 s to CI.
4. The QEMU tests in CI, now six scripts (VS-1's proposal 3, still open).
