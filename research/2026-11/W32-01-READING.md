# W32-01: how a `uint32_t` is read into L (2026-11-09)

L's words are 64-bit and unsigned. HChaCha20, SHA-256 and `sodium_bin2hex` compute on `uint32_t`. This note states how such a value is
read into L's words, and what tests that reading. It extends `RC-01-READING`, whose platform (§2, LP64: `int` is 32 bits) stands.

Like every reading in this repository, it is a **trust assumption**. C is not formalized here, so no theorem says this reading is C's
meaning. It is believed because it agrees with clang on the tests in §3, and it fails loudly if they disagree.

## 1. The reading

**A `uint32_t` value is a word whose top 32 bits are zero.** Each operation keeps that true:

| C, on `uint32_t` | L | Why |
|---|---|---|
| `a + b` | `(a + b) & 0xffffffff` | the sum of two values below `2^32` may reach `2^33 - 2` |
| `a - b` | `(a - b) & 0xffffffff` | below zero, the word wraps modulo `2^64`, and its low 32 bits are C's answer modulo `2^32` |
| `a << k`, `0 ≤ k < 32` | `(a << k) & 0xffffffff` | bits shifted past 32 stay in the word, and C drops them |
| `a >> k`, `0 ≤ k < 32` | `a >> k` | a value below `2^32` shifted right stays below it |
| `a ^ b`, `a \| b`, `a & b` | the same | each bit of the result is a function of the same bit of the operands, so bits 32 to 63 stay zero |

**Why C means this.** On LP64, `uint32_t` is `unsigned int`, whose rank is `int`'s. The integer promotions (C11 6.3.1.1p2) therefore
leave it unchanged, and the usual arithmetic conversions of two `unsigned int` operands give `unsigned int`.
- Unsigned arithmetic is modulo `2^32` (C11 6.2.5p9).
- `E1 << E2` on an unsigned `E1` is `E1 × 2^E2` reduced modulo `2^32` (C11 6.5.7p4).
- A shift by 32 or more is undefined (6.5.7p3), so the reading covers `k` below 32 only. libsodium's `rotl32(x, b)` computes `x >> (32 - b)`, so `b = 0` would be undefined too. HChaCha20 calls it with 16, 12, 8 and 7.

**Not covered:**
- types narrower than `int` (`uint8_t`, `uint16_t`), which promote to `int`;
- a `uint32_t` mixed with a wider type;
- comparisons and division;
- `*`, which is `MUL-01`.

A `uint32_t` store, as in `STORE32_LE`, is `CPP-01`'s.

## 2. In L

- The language needed one new construct, `e << k` (`Expr.shl`, W32-01 part 2). The masks are ordinary `&` with the literal
  `0xffffffff`, which CAP-01 made buildable, in three instructions.
- The reading is applied by hand in this item: in the test programs of `test/W32Pred.lean`.
- The front end does not read a `uint32_t` declaration yet. That, the macros and the inline helpers HChaCha20's text uses are `CPP-01`.
- **Cost:** each masked operation costs one `and` and, unless the mask sits in a register, the three instructions that build it. RV64's `addw` and `sllw` would do the same work in one instruction each, with a sign extension a `zext` would undo. They are an optimisation for later, and would need their own encoding, QEMU comparison and lowering proof.

## 3. What tests it

`test/w32_diff.py` (receipt `w32-diff`) builds, under the reading, programs for:
- libsodium's `rotl32(x, k)` at every `k` from 1 to 31, on 12 inputs including 0, `0xffffffff`, `0x80000000` and `0x7fffffff`;
- `+` and `-` at their wrap points;
- ChaCha's quarter round (RFC 8439 §2.1), the step HChaCha20 repeats.

For each case, three checks:
- **QEMU:** the compiled image, run under QEMU, writes what the model predicts. It does on all 806 runs.
- **clang:** a harness compiles the same operations on `uint32_t`, with libsodium's own `rotl32` at -O0 and at -O2, and gives the same four words. All 403 masked runs agree.
- **RFC 8439 §2.1.1:** the quarter round on that section's input gives `0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb` from L and from clang.

**Vacuity.** The same programs without the masks disagree with clang:
- 298 rotation runs;
- 6 additions;
- 6 subtractions;
- 9 quarter rounds.

So the inputs can tell the reading from no reading.

**Kill rule** (W32-01): a masked case that disagrees with clang stops the item. None did.

## 4. Not claimed

- That this is C's meaning in general: it is checked on these operations and inputs, on this machine's x86-64 clang, natively. Clang's riscv64 code is not compared.
- Anything about time: masks are ordinary instructions, so the constant-time certificates cover them as they cover any `&`, but nothing here measures it.
