# From the slice language to a usable L (S-USABLE, 2026-11-08)

The user's question: how does L pass from a toy language to an actually usable one? The user's answers set the frame:
- **Surface:** both, C first. L's own syntax for agents comes later, lowering to the same core.
- **The milestone:** for the research to decide.
- **Depth:** a survey with measurements.

Everything below rests on `bench/usable/s{1,2,3,4}.tsv` and the receipts `usable-s1b`, `usable-s2`, `usable-s2b`. Estimates are marked as estimates.

**The answer in one paragraph.** What makes L a toy today is **its caps, not the cost of its proofs**.
- Kernel evaluation scales linearly to tens of kilobytes. The compiler, run in the kernel, produces a 72 KB image in 11 s, and the C front end reads 27 KB of text in 10 s.
- The pipeline refuses every program past about 100 straight-line statements, because of caps that are proof constants or bookkeeping, not limits of the machine.
- Each new construct has been additive. Eleven constructs changed no kernel line and removed at most 23 lines of existing proofs each.

So the route is:
1. Lift the caps, by re-proof.
2. Add the few constructs real crypto needs (left shift, 32-bit words, large literals, macros, inline helpers with pointer arguments).
3. Certify **libsodium's `crypto_core_hchacha20`** as the first non-toy milestone.
4. Then multiplication, and **`fe25519_mul`**.

The binding cost is not Lean's kernel but route 2's re-check by lean4lean, by an estimated factor of about 20. That needs a decision before the second milestone, not now.

## 1. The caps, measured, and what lifts each

S1 compiled synthetic programs in three shapes and recorded where each was refused (`bench/usable/s1.tsv`).

| Cap | Where | Refuses | Is it the machine's? | What lifts it |
|---|---|---|---|---|
| **The image is at most 3,000 bytes** (about 750 instructions) | `okP`, and as a hypothesis of `walk_exec`, `behind`, `ahead`, `det_run` and `init_inv` | straight-line code at 300 statements (7,284 bytes), a loop body at 150 (3,720 bytes) | **No.** The data segment starts 0x20000, 65,360 bytes past the code base | Re-prove with the real bound. The constant is a proof convenience |
| **At most 384 variable occurrences** | `Slots.fits`: `128 + (allVars p).length ≤ 512` | 100 straight-line statements with only 12 distinct variables (`line100`) | **No.** `allVars` lists every occurrence, while slots are assigned by first occurrence | Count distinct names. `slotOf` is unchanged |
| A branch arm of at most 1023 instructions | `okC` | a loop or `if` body over about 4 KB | Yes: `beq`'s 13-bit offset | Branch over a `jal` (21 bits, ±1 MB): `jal` in `rvLang` |
| Literals in −2048…2047 | `okE` | `0x61707865` (HChaCha20), `0x7ffffffffffffULL` (fe25519) | Yes: `addi`'s 12-bit immediate | `lui` + `addi`, or a constant pool in the data segment |
| 256 word slots | `wordsMax` | more than about 128 locals | Yes: 12-bit offsets from one base | A second base register, or `lui` per access |
| 64 input words, one 64-word scratch array, byte arrays of 8 to 64 bytes | `fits`, `arrBase`, `maskOK` | SHA-256's `W[64]` beside its state; Poly1305's message | Partly: the data segment is 4 KB | A static layout of several named arrays in a larger data segment |
| One function, one 64-bit result | the language | every C file with helpers | No | Inline first (§5), real calls later (PH6) |

**Below the caps, kernel cost is small** (Lean's kernel, `type checking` per theorem, milliseconds):

| Program | Image bytes | `ctCheck` | literal image (the compiler, in the kernel) | `okP` | transfers to bytes |
|---|---|---|---|---|---|
| `verify16` (the 1x point; `CTBytes` measured about 100 ms for the image) | 180 | 20 | 66 | 40 | 0 |
| loop, 50-statement body | 1,320 | 66 | 241 | 116 | 0 |
| straight line, 1,000 statements (past the caps) | 24,084 | 331 | 3,450 | refused | not reached |
| straight line, 3,000 statements (past the caps) | 72,084 | 977 | 11,000 | refused | not reached |

Both costs grow linearly: about 0.15 ms per byte for the image, and 0.3 ms per statement for `ctCheck`. The transfers `relView_transfer` and `bound_transfer` cost nothing measurable: all the cost is in `decide`. Peak memory reached 5.4 GB at 72 KB, which matters on a shared box.

**Decision, by S-KERNEL's rule** (60 s per 200-node pass): whole-program kernel evaluation stays. Per-function modules are not needed for size. They may be needed for route 2's time, §2.

## 2. The trust story at scale: Lean's kernel is cheap, route 2 is not

**The front end (S2, `bench/usable/s2.tsv`).** `read16`, by `decide +kernel`, on `verify.c`'s excerpt with its loop statement repeated:

| Characters | 595 (`verify16C` itself) | 985 | 2,233 | 7,225 | 27,193 |
|---|---|---|---|---|---|
| Kernel ms | 102 | 212 | 590 | 2,330 | 9,660 |

It is linear, about 0.35 ms per character, and the variant with an `if` is refused, in 74 ms.
- S-KERNEL's ~70 s at 133 nodes was the UCmd string parser, a different program, and its rule against parsing text in the kernel does not apply to CFront.
- **Decision: the C front end stays in the kernel.** No printer round-trip is needed at these sizes. A real function is 1 to 5 KB.

**Route 2 is the binding cost.**
- One measured pair: `earlyExit_bytes_leak` cost 0.89 s in Lean's kernel, and adding `CTBytes` added about 20 s to lean4lean (receipt `rc01-step6-kerneltime`, on a noisy box). That is a ratio of about 20. **It is an estimate from one point**, not a model.
- Extrapolated, a function with a 10 KB image adds about 2 s in Lean's kernel and **about 40 s to route 2**, and route 2's budget is now 319 s.
- So route 2 absorbs a handful of real functions, not dozens. **This is the next decision point, at the first milestone, and it is the user's** (Ring 0):
  - (a) raise the budget again;
  - (b) give each certified program its own export, checked once per content hash and cached;
  - (c) have the external kernels re-check the library and its theorems, with each program's `decide` facts checked by Lean's kernel only.

  (b) keeps every check and pays once. I would choose it.

**The precedents agree on where in-logic evaluation stops.**
- CakeML bootstraps its compiler by evaluation inside HOL4, and reports that evaluating the compiler in the logic is slow: simple Pancake programs take hours, and the instruction encoder was a named bottleneck.
- Jasmin and CompCert run an extracted compiler, which the user's trust story (PLAN-2026-10 §4, T2) rejects.
- L sits between them: the compiler is evaluated in the kernel, per program, and is linear.

## 3. What a construct costs (S3, `bench/usable/s3.tsv`)

Lines added and removed per layer, for each construct added so far:

| Construct | Machine | Source and checker | Slots pass | Lowering | Budget | Witnesses | Kernel | Removed |
|---|---|---|---|---|---|---|---|---|
| 5 ALU instructions (RC-01 2a) | +35 | | | +60 | | | 0 | 1 |
| `^ \| & -`, `>> k` (2b) | +19 | +12 | +18 | +107 | +10 | +74 | 0 | 13 |
| `lbu` (3a) | +12 | | | +17 | | | 0 | 1 |
| `loadB`, byte arrays (3) | | +60 | +37 | +195 | +22 | +117 | 0 | 23 |
| `ctCheck`, a new certificate (4) | | +51 | | **0** | | +177 | 0 | 18 |
| `andi` (VS-2 3) | +12 | | | | | | 0 | 1 |
| `while` and an array (VS-2 4 to 6) | | +607 | +511 | +1,547 | | +82 | 0 | 10 |
| counted loops and their budget (BOUND-01 2, 3) | | | | | +644 | | 0 | 0 |

**PLAN-2026-10 §6's claim holds where it was tested.**
- A new certificate cost no pass lines (`ctCheck`).
- A new construct cost local lemmas in each pass: mostly the lowering, about 100 to 200 lines for an expression or a command, and about 2,000 for loops.
- No construct changed the kernel. The largest edit to existing proofs removed 23 lines (`loadB`).

**What it did not test:** a construct that changes the machine state's shape, like a stack for calls, or a second memory region. Those are the expensive ones still ahead (§4, items 2 and 7).

## 4. The milestone, chosen by evidence (S4, `bench/usable/s4.tsv`)

Eleven candidate functions from libsodium 1.0.20, pinned by sha256, with what each needs that L lacks:

| Candidate | New constructs | What they are |
|---|---|---|
| `sodium_is_zero` | 0 | a stated length |
| `sodium_add`, `sodium_sub`, `sodium_increment` | 1 | an output array (RC-02) |
| `sodium_compare` | 2 | truncating `unsigned char`; a counted loop downwards |
| `sodium_bin2hex` | 7 | output, `<<`, 32-bit words, `~`, an aborting check, a parameter length, truncating stores |
| **`crypto_core_hchacha20`** | **9** | output, `<<`, 32-bit words, large literals, 32-bit little-endian loads and stores, macros, inline helpers with pointer arguments, a public branch on a pointer, size past the caps |
| **`fe25519_mul` (51-bit limbs)** | **7** | `mul` and `mulhu`, 128-bit sums with carries, `<<`, a large literal, word arrays in and out, inline, size |
| `SHA256_Transform` | 9 | as hchacha20, plus local arrays, a constant table, big-endian loads |
| `poly1305_blocks` (donna64) | 9 | as fe25519, plus a struct and a loop over a public length |
| ChaCha20's block and stream | 12 | as hchacha20, plus a struct, a public-length loop, a local array |

**The recommendation: `crypto_core_hchacha20` first, then `fe25519_mul`.**
- **HChaCha20 is the smallest step to a real primitive.** It has fixed sizes, one counted loop of 10, no multiplication, and output through `STORE32_LE`. Its new constructs are each small, and most are front-end work: macros, inline helpers, 32-bit masking. The XChaCha draft (draft-irtf-cfrg-xchacha) has an HChaCha20 test vector, to be confirmed in RC-03's first step, which gives a check beside clang's.
  - Size, estimated from the C: about 320 statements after expansion, roughly 10 KB of image. That is past today's caps and well inside S1's linear range.
- **`fe25519_mul` is the most valuable next one.** It is the field multiply under the ref10 X25519 and Ed25519 code, straight-line, with no loops or tables. What it needs is `mul`/`mulhu` in `rvLang` (RV64M), and a reading of `uint128_t` as two words with explicit carries. That is the step where the machine model grows most, so it comes second, on the caps that HChaCha20 has already lifted.
- **Not first:** SHA-256 and Poly1305 need local arrays, a constant table or a struct, which are the state-shape changes S3 did not test. ChaCha20's stream adds a public-length loop and partial blocks. The `utils.c` functions are worth doing on the way (RC-02 is one), but they are not "usable" milestones: each is 10 lines.

## 5. The route

In order. Each item gets an acceptance rule and a kill rule in `backlog/`, filed `planned`.

| # | Item | Ring | What | Why here |
|---|---|---|---|---|
| 1 | `RC-02` (in progress) | 1 | output arrays, observed as `Ev.emit`; `sodium_add` | every function that returns data needs it |
| 2 | `CAP-01` | 1 | count distinct variables in `fits`; raise the 3,000-byte bound to the code segment's room; `lui`+`addi` literals; long branches over `jal`. Every existing image is byte-for-byte unchanged | S1: the caps refuse real code before cost matters |
| 3 | `W32-01` | 1 | `<<` (`slli`/`sll`) in machine and language; 32-bit unsigned arithmetic read as word operations masked to 32 bits. The reading is stated, and `addw`/`sllw` are a later optimisation | HChaCha20, SHA-256, bin2hex |
| 4 | `CPP-01` | 1 | the front end: function-like macros, by bounded expansion; `static inline` helpers with pointer arguments at a fixed offset (`k + 16`); `do { } while (0)`; a public `if` on a stated pointer value | HChaCha20's text as written |
| 5 | `RC-03` **milestone M1** | 1 | `crypto_core_hchacha20`, read from its pinned text, constant-time with a constant budget on its literal image, by transfer; QEMU, clang and the draft's test vector agree | the first non-toy program |
| 6 | `ROUTE2-01` | **0, G-0** | route 2's cost per program: one of §2's (a), (b), (c) | it is due at M1, by the estimate |
| 7 | `MUL-01` | 1 | `mul`, `mulhu` in `rvLang`, compared with QEMU; 128-bit sums as two words with carries (`sltu`) in the language | fe25519 and Poly1305 |
| 8 | `RC-04` **milestone M2** | 1 | `fe25519_mul`, constant-time, a budget, and correct against a Lean specification of multiplication mod 2^255 − 19 | the X25519 core; the first functional-correctness certificate on real code |
| 9 | `LSYN-01` | 1 | L's own surface syntax, for agents: the same core, a second front end, Jasmin-like storage and secrecy annotations | after the core has met real C, so the syntax describes a language that exists |
| 10 | PH6, as planned | 0/1 | real subroutines, stack frames, contracts, `link_correct` | when a target needs a call that inlining cannot remove |

**Two corrections to this research's own plan**, recorded here:
- The plan said inline-only functions come first "as Jasmin does". **Jasmin does not inline by default.** Since release 2023.06.0 a bare `fn` is a subroutine, and only `inline fn` is inlined.
  - The order stands for a different reason: every helper in the chosen targets is a `static inline` function or a macro in libsodium's own source, so inlining is what the text asks for.
  - Real calls are PH6, when a target needs them.
- The plan expected kernel cost might force per-function granularity. It does not, for size. Route 2 may, for time.

## 6. Not claimed, and open

- **No timing is a model.** The S1 and S2 times come from one box under other projects' load, one run each. The 1x points reproduce earlier receipts within noise. The lean4lean ratio is one pair.
- **Sizes after expansion are estimates** from reading the C, not measured, since no program past the caps can be compiled yet.
- **Call sites** are surveyed only where the table says so.
- **Not surveyed:** speculation (SCT), for which `SPECULATION-PASSES.md` stands; memory safety beyond fixed arrays; strings and the sinks of PLAN-2026-10 §3, which none of these targets need.
- **Open:**
  - whether `uint32_t` should become a type in L, or stay a masked reading in the front end;
  - whether a constant table (`Krnd`) is a read-only input or data in the image;
  - how the reading states `NATIVE_LITTLE_ENDIAN`'s `memcpy` branch, which RISC-V compiles, against the portable one that L would read.

## Sources

- Jasmin: [functions, `inline`, `export`](https://jasmin-lang.readthedocs.io/en/stable/language/syntax/structure.html), [arrays](https://jasmin-lang.readthedocs.io/en/stable/language/semantics/arrays.html), [release notes: `fn` is a subroutine since 2023.06.0](https://github.com/jasmin-lang/jasmin/releases), [the RISC-V back end in jasmin-compiler 2026.03.0](https://ocaml.org/p/jasmin/latest/jasmin.jasmin/Jasmin/Riscv_arch_full/index.html), [verification and extraction](https://jasmin-lang.readthedocs.io/en/stable/about.html).
- FaCT: [Cauligi et al., PLDI 2019](https://cseweb.ucsd.edu/%7Edstefan/pubs/cauligi:2019:fact.pdf). Constant-time C avoids secret ifs, loops and calls; secrecy types; libsodium routines within −5% to +21% of C.
- CakeML: [bootstrapping inside the logic](https://www.cl.cam.ac.uk/~mom22/popl14.pdf); [slow in-logic evaluation, and the encoder as a bottleneck](https://comp.anu.edu.au/courses/comp3710-compilers/assets/lecture-pdfs/12-norrish.pdf); [Pancake programs taking hours](https://remyjck.github.io/research/bootstrapped-compiler).
- The libsodium texts, tag `1.0.20-RELEASE`, with the hashes in `bench/usable/s4.tsv`.
