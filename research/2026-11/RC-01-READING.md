# RC-01 step 1: the C subset, and how it is read into L (2026-11-06)

Written before any parser, against the pinned source. Every line of `crypto_verify_n` and `crypto_verify_16` is accounted for below, and each
reading says what it rests on.

**The source.** libsodium `1.0.20-RELEASE`:
- `src/libsodium/crypto_verify/verify.c`, sha256 `44642761ec112967330b0bbc67fee47edb9f35e1dd9b4c8a40fb05fc4d568ea9`
- `src/libsodium/include/sodium/crypto_verify_16.h`, sha256 `d3b4fbea4b6d2bf23a9a079939a181625be76a006af129732af86bf4b544456c`,
  which gives `#define crypto_verify_16_BYTES 16U`
- `src/libsodium/include/sodium/crypto_verify_32.h`, sha256 `6ea1ea855b691a2b08510afe74f893d4ff44e40b14501d774d1a73dd79ad4e73`, which gives
  `#define crypto_verify_32_BYTES 32U`, and `LICENSE` (ISC), sha256 `43964d976a6db3fb986af689d05f8ca0e9971878bccae709750dac8fdc4a99cf`.
  Added 2026-11-08 (step 5). All four are vendored in `third_party/libsodium-1.0.20/`, and the build hashes them (`CSrc`, `Sha256`).

```c
static inline int
crypto_verify_n(const unsigned char *x_, const unsigned char *y_, const int n)
{
    const volatile unsigned char *volatile x = (const volatile unsigned char *volatile) x_;
    const volatile unsigned char *volatile y = (const volatile unsigned char *volatile) y_;
    volatile uint_fast16_t d = 0U;
    int i;

    for (i = 0; i < n; i++) {
        d |= x[i] ^ y[i];
    }
    return (1 & ((d - 1) >> 8)) - 1;
}

int
crypto_verify_16(const unsigned char *x, const unsigned char *y)
{
    return crypto_verify_n(x, y, crypto_verify_16_BYTES);
}
```

## 1. Which branch is read

`verify.c` has two definitions of `crypto_verify_n`, chosen by `#if defined(HAVE_EMMINTRIN_H) && defined(__SSE2__)`. On RISC-V `__SSE2__`
is never defined, so the portable branch above is what runs there, and it is the only one read. **The preprocessor is not reimplemented.** The
front end reads the text of one function, and the step that picks the branch is stated here, not checked. The differential test (step 6)
compiles the file as it is, with `HAVE_EMMINTRIN_H` undefined, so it also takes this branch.

## 2. The platform: LP64 with glibc

| C type | Width read | Rests on |
|---|---|---|
| `unsigned char` | 8 bits | C11 5.2.4.2.1, `CHAR_BIT` is 8 on every target L has |
| `int` | 32 bits, signed | LP64. Measured 4 bytes on this machine's x86-64 glibc |
| `uint_fast16_t` | 64 bits, unsigned | glibc defines it as `unsigned long int` on 64-bit targets. Measured 8 bytes on x86-64. **Not measured on riscv64**: its glibc headers are not installed here. **On musl it is 32 bits**, and §4 shows the result does not change |

L's words are 64-bit unsigned, so `uint_fast16_t` is a word, and its arithmetic is word arithmetic, modulo `2^64`.

## 3. Each construct

**The parameters.** `x_` and `y_` are pointers to 16 bytes each, which the caller owns. **Read as two read-only input byte arrays of fixed length
16**, the secret inputs. They may alias: `crypto_verify_16(p, p)` is legal C. Nothing writes through either, so aliasing cannot change a value
read, and two arrays read the same as one. `n` is the literal `16U`, converted to `const int`: 16.

**The inlined call.** `crypto_verify_16` calls a `static inline` function once, with constant arguments. **Read by substitution**, `n := 16`.
The subset admits only this: a call to a `static inline` function in the same file, with literal or parameter arguments, and no recursion.

**The casts** to `const volatile unsigned char *volatile` change only qualifiers. They are **read as the identity**: same address, same bytes.

**`volatile`.** C11 6.7.3p7: every access to a volatile object is evaluated strictly as the abstract machine says. It exists to stop an
optimising compiler removing or merging accesses, here so that the loop's time does not depend on the data. **L's reading performs every
access the abstract machine performs, once each, in order**:
- each `x[i]` and `y[i]` is one byte load per iteration;
- `d` is read and written each iteration;
- L's pipeline keeps every variable in its own memory slot and does not optimise.

So `volatile` is not dropped silently: the property it asks for, no access removed, holds of L's compilation by construction. **What is not
claimed:** that clang's compilation of the original keeps it. That belongs to clang, and is outside this item.

**`volatile uint_fast16_t d = 0U;`** A word variable initialised to 0.

**`int i;` and `for (i = 0; i < n; i++)`** with `n = 16`: a counted loop over `i = 0 … 15`, and `i` is not assigned in the body. **Read as
BOUND-01's `forN` with a literal count of 16**, and `i = 16 - c` from its counter `c`. `i` is an `int`, and its values stay in `0 … 16`, so int and
word arithmetic agree on it.

**`d |= x[i] ^ y[i];`**, under C11 6.3.1.1 and 6.5.11:
1. `x[i]` and `y[i]` are `unsigned char`, zero-extended. Each is a byte load, read as a word in `0 … 255`.
2. Both are promoted to `int` before `^`. Their xor is an `int` in `0 … 255`, the same as the word xor.
3. `d |= v` converts `v` to `d`'s type, `unsigned long`. `v` is non-negative, so the value is unchanged, then it is or-ed into `d`. In words:
   `d := d | (x[i] ^ y[i])`.

The `int` intermediates stay in `0 … 255`, so no signed overflow and no implementation-defined conversion arises. The front end must check this
range, not assume it (§5).

**`return (1 & ((d - 1) >> 8)) - 1;`**, under C11 6.3.1.8, the usual arithmetic conversions. `d` is `unsigned long`, so every operand is
converted to it:
1. `d - 1` is word subtraction, modulo `2^64`. It wraps to `2^64 - 1` when `d = 0`.
2. `>> 8` is a logical shift, since the operand is unsigned. It gives `2^56 - 1` when `d = 0`. Otherwise `d ≤ 255`, so `d - 1 ≤ 254` and the
   shift gives 0.
3. `1 & …` gives 1 when `d = 0`, else 0.
4. `- 1` gives 0 when `d = 0`, else `2^64 - 1`, as an `unsigned long`.
5. **The conversion to the `int` return type** is out of range for `2^64 - 1`, which is implementation-defined (C11 6.3.1.3p3). GCC and clang
   define it as reduction modulo `2^32`, giving `-1`.

**Read:** L's result word is 0 or `2^64 - 1`, and the C `int` is its low 32 bits, sign-extended: 0 or -1. The differential test compares that
way. **The result is 0 exactly when the 16 bytes are equal, and -1 otherwise.**

## 4. What does not depend on the reading's choices

With a 32-bit `uint_fast16_t`, as on musl, step 1 wraps to `2^32 - 1`, step 2 gives `2^24 - 1`, and the result is the same 0 or -1. So the
result is the same on glibc and musl. **The leakage is not**: on a 32-bit `d` the compiled code differs. What L certifies is L's compilation, with
`d` a word.

## 5. The subset, as it stands after this function

| Construct | Reading |
|---|---|
| Parameters of type `const unsigned char *` with a fixed, known length | read-only byte arrays |
| `static inline` calls with literal arguments | substitution |
| Qualifier-only casts; `volatile` | identity; §3 |
| Locals of type `unsigned long`, `uint_fast16_t`, `uint64_t` | words |
| Locals of type `int` | words, **only where an interval check bounds every value in `0 … 2^31 - 1`** |
| `for (i = 0; i < N; i++)` with literal `N` and `i` unassigned in the body | `forN`, with `i = N - c` |
| `^ \| & + -` and `>> k` for a literal `k`; integer literals | word operations; `>>` logical on unsigned |
| Array reads `a[i]` with `i` the loop index | byte loads at a public index |
| `return e;` of type `int` | the result word, and its low 32 bits as the int |

**Refused**, so that the front end says no and does not guess: pointer arithmetic other than indexing; writes through a parameter; a
loop not of the counted form; `int` values the interval check cannot bound; signed `>>`; division; calls other than the above; `goto`;
anything the preprocessor would have to decide.

## 6. What each construct needs in L, and through to the bytes

| Needed | In L today? | `rvLang` |
|---|---|---|
| `^`, `\|`, `&`, `-`, `>> k` on words | `add` only | `xor`, `or`, `and`, `sub`, `srli`: new, each compared with QEMU |
| Two read-only byte arrays as inputs | one word array, not an input | `lbu`: new |
| `forN` with literal count, and an increasing index from it | `forN` (BOUND-01), the index needs `-` | none new |
| Constant-time certificate, blind to the result | `Cert.relView` in the kernel | through `relView_transfer` |

**No kernel change is expected.** The certificate is `relView` with an observer blind to the `ret` channel, and the kernel has it, locked
(F6).
