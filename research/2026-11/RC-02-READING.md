# RC-02 step 1: `sodium_add`, and how it is read into L (2026-11-08)

The second real function, and the first that writes its result. This note extends `RC-01-READING`: its platform (§2) and its rules for
`volatile`, casts and loops (§3) stand, and only what is new is written here.

## 0. The pinned text

From tag `1.0.20-RELEASE` of `jedisct1/libsodium`. Fetching `verify.c` the same way gives RC-01's pin, `44642761…568ea9`, so these are
the release's files.

| File | sha256 | What is read |
|---|---|---|
| `src/libsodium/sodium/utils.c` | `62ef6a5e2289a69a1e72d8d2d77d7080ee30be1c1e75f758bfdd816e91756d96` | lines 313 to 318 and 354 to 360: `sodium_add` without the `HAVE_AMD64_ASM` block |
| `src/libsodium/include/sodium/utils.h` | `89e4062d53fa0d43834c83fb2e488a71367a6344b39636d08cc601f942c6f0a5` | line 54, the declaration |
| `src/libsodium/crypto_core/ed25519/core_ed25519.c` | `799dfef3e6ba0a63f36438dedede34a162594aa6ddd616543698a6a3d2fcfed8` | line 164, the call site that fixes `len` |
| `src/libsodium/include/sodium/crypto_core_ed25519.h` | `d8e7c59a0225df93b2d61ea10bbe16550ef7f23d81af8d88e357a58e81af9f6a` | line 23, `crypto_core_ed25519_SCALARBYTES 32` |

Step 5 vendors them beside `verify.c`, and `CSrc`'s `#eval` hashes them at every build, as it does `verify.c`.

```c
void
sodium_add(unsigned char *a, const unsigned char *b, const size_t len)
{
    size_t        i;
    uint_fast16_t c = 0U;

    for (i = 0U; i < len; i++) {
        c += (uint_fast16_t) a[i] + (uint_fast16_t) b[i];
        a[i] = (unsigned char) c;
        c >>= 8;
    }
}
```

## 1. Which branch is read

`HAVE_AMD64_ASM` guards x86-64 assembly (`movq`, `adcq`), which cannot build for RISC-V. The reading takes it as undefined, so lines
319 to 354 are not compiled, and the portable loop is the whole function. That configure leaves it undefined on riscv64 is assumed
from the assembly's content, not checked against `configure.ac`. The note states this. The x86-64 assembly is not read, and nothing is
claimed of it.

## 2. The length

`len` is a parameter. L reads the function at a **stated length**, 32, from the call in `crypto_core_ed25519_scalar_add`:
`sodium_add(x_, y_, crypto_core_ed25519_SCALARBYTES)`, with the define `32` from the pinned header. The call's buffers are 64 bytes,
zeroed and then filled to 32, and the add touches the first 32. What is certified is `sodium_add` with `len = 32`, not for every `len`.

## 3. Each construct that RC-01 did not have

- **`unsigned char *a`, not `const`**: an array read and written. It is the output. Its 32 bytes are input words 0 to 3, and at the
  end the run emits them as `.emit "out"`, before the result. The function returns `void`, so its result is the constant 0, and the
  test does not compare it.
- **`const unsigned char *b`**: a read-only array, as in RC-01: input words 4 to 7.
- **`size_t i`**, from 0 to 31: a word. `i < len` with `len = 32` is RC-01's counted loop, `forN` with `i = 32 - c`.
- **`c += (uint_fast16_t) a[i] + (uint_fast16_t) b[i]`**. `a[i]` and `b[i]` are loaded zero-extended. Each cast is to a 64-bit word
  (`uint_fast16_t` on LP64 glibc, `RC-01-READING` §2), so it is the identity on a byte. The sum is word addition. Bound: `c` is at
  most 1 on entry to every iteration but the first, where it is 0, so `c` stays at most `255 + 255 + 1 = 511`, and no wrap occurs on
  any platform whose `uint_fast16_t` has at least 16 bits.
- **`a[i] = (unsigned char) c`**: conversion to `unsigned char` is reduction mod 256 (C11 6.3.1.3p2), so the byte stored is `c & 255`.
  L's byte store keeps the low byte, and the reading says so.
- **`c >>= 8`**: logical, since `c` is unsigned. `c` becomes the carry, 0 or 1.

## 4. Aliasing: what C allows and what the reading assumes

C allows `a == b`, and the function is still well defined then: `a[i]` and `b[i]` are both read before `a[i]` is written. L's
reading has two distinct arrays, from two distinct inputs, so a call with `a == b` is **not covered**. The call that fixes the length
passes the distinct buffers `x_` and `y_`. Partial overlap, `b == a + k`, is not covered either.

## 5. Its constant-time shape

Every index is the loop's, so it is public. No branch reads a secret. The carry `c` is secret and loop-carried, as `d` was in
`crypto_verify_16`, which is what RC-01's widened loop rule accepts. The output bytes depend on the secrets by design. The observer
`noOut` reads neither the result's payload nor the output's, and sees everything else: PCs, addresses, instruction count, outcome, and
that one output of 32 bytes is written.

## 6. The subset, after this function

RC-01's §5, plus:

| Construct | Reading |
|---|---|
| Parameters of type `unsigned char *` with a stated length | byte arrays read and written, emitted at the end |
| Parameters of type `const size_t` given a stated value | the value, substituted |
| `a[i] = e;` with `i` the loop index | a byte store at a public index, of `e & 255` |
| `x += e;` and `x >>= k;` | `x := x + e` and `x := x >> k` |
| Casts to `uint_fast16_t`, `size_t`; to `unsigned char` on a store | identity; the store keeps the low byte |
| A function returning `void` | the result 0 |

Still refused: `a` and `b` overlapping; writes through a `const` parameter; a store at an index other than the loop's; everything
RC-01's §5 refuses.
