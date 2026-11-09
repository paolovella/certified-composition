#!/usr/bin/env python3
"""W32-01 part 3: the C reading of `uint32_t`, tested against clang.

The reading (research/2026-11/W32-01-READING.md): a `uint32_t` is a word whose top 32 bits are zero, and each `+`, `-` and `<<` on it is
followed by `& 0xffffffff`. W32Pred.lean writes, by hand under that reading, programs for libsodium's `rotl32(x, k)` at every `k` from 1
to 31, for `+` and `-`, and for ChaCha's quarter round. For each program and input:

  QEMU   runs L's image, and its output must equal the model's;
  clang  compiles the same operations on `uint32_t`, natively, at -O0 and -O2, and its answers must equal L's;
  RFC    the quarter round on RFC 8439 §2.1.1's input gives that section's output, from L and from clang.

Kill rule (W32-01): if a masked case disagrees with clang on any input, the reading is wrong; the script says so and fails.

Vacuity: the `raw` programs are the same without the masks. QEMU must still agree with the model on them, and each family must disagree
with clang on some input, or the inputs could not tell the reading from no reading.

This says nothing about clang's riscv64 code, about time, or about a `uint32_t` declaration, which the front end does not read yet.

Usage, from l-core/: python3 test/w32_diff.py <scratch directory>
"""
import os
import random
import struct
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from image2_diff import elf  # noqa: E402

HARNESS = r"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* As libsodium's private/common.h, 1.0.20. */
static inline uint32_t rotl32(const uint32_t x, const int b) { return (x << b) | (x >> (32 - b)); }
int main(void) {
    char n[32];
    unsigned long long A, B, C, D;
    while (scanf("%31s %llu %llu %llu %llu", n, &A, &B, &C, &D) == 5) {
        uint32_t a = (uint32_t) A, b = (uint32_t) B, c = (uint32_t) C, d = (uint32_t) D;
        if (!strncmp(n, "rotlraw", 7)) a = rotl32(a, atoi(n + 7));
        else if (!strncmp(n, "rotl", 4)) a = rotl32(a, atoi(n + 4));
        else if (!strncmp(n, "add", 3)) a = a + b;
        else if (!strncmp(n, "sub", 3)) a = a - b;
        else if (!strncmp(n, "qr", 2)) {
            a += b; d ^= a; d = rotl32(d, 16); c += d; b ^= c; b = rotl32(b, 12);
            a += b; d ^= a; d = rotl32(d, 8);  c += d; b ^= c; b = rotl32(b, 7);
        } else return 2;
        printf("%llu %llu %llu %llu\n", (unsigned long long) a, (unsigned long long) b, (unsigned long long) c,
               (unsigned long long) d);
    }
    return 0;
}
"""

RFC_IN = (0x11111111, 0x01020304, 0x9b8d6f43, 0x01234567)
RFC_OUT = (0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb)


def cases():
    r = random.Random(20261109)
    u = [0, 1, 0xffffffff, 0x80000000, 0x80000001, 0x7fffffff, 0xdeadbeef, 0x01234567] + [r.randrange(2 ** 32) for _ in range(4)]
    out = []
    for raw in ("", "raw"):
        for k in range(1, 32):
            out += [(f"rotl{raw}{k}", (x, 0, 0, 0)) for x in u]
        pairs = [(0xffffffff, 1), (0, 1), (0x80000000, 0x80000000), (1, 0xffffffff), (0xdeadbeef, 0xdeadbeef)]
        pairs += [(r.randrange(2 ** 32), r.randrange(2 ** 32)) for _ in range(6)]
        out += [(f"add{raw}", (a, b, 0, 0)) for a, b in pairs] + [(f"sub{raw}", (a, b, 0, 0)) for a, b in pairs]
        out += [(f"qr{raw}", RFC_IN)] + [(f"qr{raw}", tuple(r.randrange(2 ** 32) for _ in range(4))) for _ in range(8)]
    return out


def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    cs = cases()
    lines = "".join(f"{n} {' '.join(map(str, w))}\n" for n, w in cs)
    g = subprocess.run(["lake", "env", "lean", "--run", "test/W32Pred.lean", d], input=lines, capture_output=True, text=True)
    if g.returncode != 0:
        sys.exit(f"prediction failed: {g.stdout[-1500:]} {g.stderr[-800:]}")
    pred = open(f"{d}/pred.txt").read().split("CASE ")[1:]
    assert len(pred) == len(cs), (len(pred), len(cs))

    open(f"{d}/harness.c", "w").write(HARNESS)
    clang = {}
    for opt in ("-O0", "-O2"):
        exe = f"{d}/harness{opt}"
        c = subprocess.run(["clang", opt, "-Wall", "-Werror", f"{d}/harness.c", "-o", exe], capture_output=True, text=True)
        if c.returncode != 0:
            sys.exit(f"clang failed: {c.stderr[-1500:]}")
        r = subprocess.run([exe], input=lines, capture_output=True, text=True, timeout=60)
        if r.returncode != 0:
            sys.exit(f"harness failed {opt}: {r.returncode}")
        clang[opt] = [tuple(int(x) for x in l.split()) for l in r.stdout.splitlines()]
        assert len(clang[opt]) == len(cs), opt
    same_opt = clang["-O0"] == clang["-O2"]

    bad = 0
    qemu_bad = 0
    refused = []
    raw_differs = {}
    for k, ((n, w), block) in enumerate(zip(cs, pred)):
        rows = dict(l.split(" ", 1) if " " in l else (l, "") for l in block.strip().split("\n")[1:])
        if rows["OK"] != "true":
            refused.append(n)
            continue
        img = bytes(int(x) for x in rows["IMG"].split())
        model = bytes(int(x) for x in rows["OUT"].split())
        p = f"{d}/c{k}"
        with open(p, "wb") as f:
            f.write(elf(img, struct.pack("<QQQQ", *w)))
        os.chmod(p, 0o700)
        q = subprocess.run(["qemu-riscv64", p], capture_output=True, timeout=60)
        if q.stdout != model or len(model) != 32:
            qemu_bad += 1
            print(f"FAIL qemu {n} {w}: qemu {q.stdout.hex()} model {model.hex()}")
        want = struct.pack("<QQQQ", *clang["-O2"][k])
        family = n.rstrip("0123456789")
        if family.endswith("raw"):
            raw_differs.setdefault(family, 0)
            raw_differs[family] += model != want
        elif model != want:
            bad += 1
            print(f"KILL the reading disagrees with clang: {n} {[hex(x) for x in w]}: L {model.hex()} clang {want.hex()}")

    total = len(cs) - len(refused)
    print(f"{'ok  ' if not refused else 'FAIL'} every program is accepted by the pipeline ({len(refused)} refused: {sorted(set(refused))})")
    print(f"{'ok  ' if not qemu_bad else 'FAIL'} QEMU equals the model on {total} runs, masked and raw")
    print(f"{'ok  ' if same_opt else 'FAIL'} clang -O0 and -O2 agree on every input")
    masked = sum(1 for n, _ in cs if not n.rstrip('0123456789').endswith('raw'))
    print(f"{'ok  ' if not bad else 'FAIL'} the reading equals clang on all {masked} masked runs: rotl32 at k = 1..31, +, -, the quarter round")
    k_rfc = cs.index(("qr", RFC_IN))
    rfc_l = struct.unpack("<QQQQ", bytes(int(x) for x in pred[k_rfc].strip().split("\n")[3].split()[1:]))
    rfc_ok = rfc_l == RFC_OUT == clang["-O2"][k_rfc]
    print(f"{'ok  ' if rfc_ok else 'FAIL'} RFC 8439 §2.1.1: L and clang give {', '.join(hex(x) for x in RFC_OUT)}")
    fams = ["rotlraw", "addraw", "subraw", "qrraw"]
    vac = all(raw_differs.get(f, 0) > 0 for f in fams)
    print(f"{'ok  ' if vac else 'FAIL'} vacuity: without the masks each family disagrees with clang somewhere "
          f"({', '.join(f'{f} {raw_differs.get(f, 0)}' for f in fams)})")
    fails = bool(refused) + bool(qemu_bad) + (not same_opt) + bool(bad) + (not rfc_ok) + (not vac)
    print(f"w32-diff: {fails} failed")
    return 1 if fails else 0


sys.exit(main())
