#!/usr/bin/env python3
"""RC-02 step 6: sodium_add's image under QEMU, against the model, against clang's compiled original, and against arithmetic.

`AddBytes.add_ct_bytes` says the 204-byte image is constant time on the model with its output: the same PCs, addresses, cost and outcome
whatever the two arrays hold. `add_bound_bytes` says it runs at most 1825 instructions. Here, on many pairs of 32-byte arrays:

  model     QEMU runs the image, and its stdout and instruction count equal the model's
  secret    every run's PC and address trace and cost equal the first run's: the arrays change neither
  budget    every run is within 1825 instructions
  clang     the lines of the vendored utils.c that L reads (313-318 and 355-360), compiled natively by clang at -O0 and -O2, unmodified,
            with <stdint.h> and <stddef.h>, give the same bytes as L's image
  sum       both equal (a + b) mod 2^256, little-endian, computed by Python
  vacuity   outputs differ between pairs; a harness that flips one output bit is seen to disagree; the leaky variant's trace is seen to
            depend on the arrays

clang compiles the same lines L reads, not the whole utils.c, whose other functions need the rest of libsodium. The test says so.
This says nothing about QEMU's fidelity to hardware, about time, or about clang's own riscv64 compilation.

Usage, from l-core/: python3 test/add_diff.py <scratch directory>
"""
import os
import random
import struct
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from image2_diff import elf, observe  # noqa: E402

UTILS = os.path.abspath("../third_party/libsodium-1.0.20/utils.c")
BUDGET = 1825

HARNESS = r"""
#include <stdio.h>
#include <stdint.h>
#include <stddef.h>
void sodium_add(unsigned char *a, const unsigned char *b, const size_t len);
int main(void) {
  unsigned char a[32], b[32];
  int flip = FLIP;
  while (1) {
    for (int k = 0; k < 32; k++) if (scanf("%hhu", &a[k]) != 1) return 0;
    for (int k = 0; k < 32; k++) if (scanf("%hhu", &b[k]) != 1) return 1;
    sodium_add(a, b, 32);
    a[0] ^= flip;
    for (int k = 0; k < 32; k++) printf("%u ", a[k]);
    printf("\n");
  }
}
"""


def pairs():
    r = random.Random(20261109)
    out = [(bytes(32), bytes(32)), (bytes([255] * 32), bytes([1] + [0] * 31)), (bytes([255] * 32), bytes([255] * 32)),
           (bytes([1] + [0] * 31), bytes([255] * 32)), (bytes([0x80] * 32), bytes([0x80] * 32))]
    for k in range(32):
        a = bytearray(32)
        a[k] = 0xff
        out.append((bytes([255] * k + [0] * (32 - k)), bytes([1] + [0] * 31)))
    for _ in range(40):
        out.append((bytes(r.randrange(256) for _ in range(32)), bytes(r.randrange(256) for _ in range(32))))
    return out


def words(x, y):
    return struct.unpack("<4Q", x) + struct.unpack("<4Q", y)


def total(x, y):
    s = (int.from_bytes(x, "little") + int.from_bytes(y, "little")) % 2 ** 256
    return s.to_bytes(32, "little")


def clang(d, ps, opt, flip=0):
    lines = open(UTILS, encoding="ascii").read().split("\n")
    with open(f"{d}/add.c", "w") as f:
        f.write("#include <stdint.h>\n#include <stddef.h>\n" + "\n".join(lines[312:318] + lines[354:360]) + "\n")
    with open(f"{d}/h.c", "w") as f:
        f.write(HARNESS.replace("FLIP", str(flip)))
    exe = f"{d}/native{opt}{flip}"
    c = subprocess.run(["clang", opt, f"{d}/add.c", f"{d}/h.c", "-o", exe], capture_output=True, text=True)
    if c.returncode != 0:
        sys.exit(f"clang failed: {c.stderr[-1500:]}")
    inp = "".join(" ".join(map(str, x)) + " " + " ".join(map(str, y)) + "\n" for x, y in ps)
    r = subprocess.run([exe], input=inp, capture_output=True, text=True, timeout=60)
    return [bytes(int(v) for v in l.split()) for l in r.stdout.strip().split("\n")]


def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    ps = pairs()
    g = subprocess.run(["lake", "env", "lean", "--run", "test/AddPred.lean", d],
                       input="".join(" ".join(map(str, words(x, y))) + "\n" for x, y in ps), capture_output=True, text=True)
    if g.returncode != 0:
        sys.exit(f"prediction failed: {g.stdout[-1500:]} {g.stderr[-800:]}")
    preds = []
    for line in open(f"{d}/pred.txt"):
        bs, rest = line.split("|")
        o, c = rest.split()
        preds.append((bytes(int(v) for v in bs.split()), o, int(c)))
    code = open(f"{d}/add.bin", "rb").read()
    bad = 0
    first = None
    outs = set()
    for k, ((x, y), (mout, mo, mc)) in enumerate(zip(ps, preds)):
        p = f"{d}/a{k}"
        with open(p, "wb") as f:
            f.write(elf(code, struct.pack("<8Q", *words(x, y))))
        os.chmod(p, 0o700)
        q = subprocess.run(["qemu-riscv64", p], capture_output=True, timeout=60)
        obs = observe(p, code, {}, [], f"{d}/a{k}.log")
        trace = obs["trace"] if obs else None
        n = obs["cost"] if obs else None
        ok = mo == "done" and q.stdout == mout and q.returncode == 0 and mout == total(x, y) and n == mc and mc <= BUDGET
        if first is None:
            first = (trace, mc)
        same = trace == first[0] and mc == first[1]
        bad += not (ok and same)
        outs.add(mout)
        if not (ok and same):
            print(f"FAIL pair {k}: model {mout.hex()} qemu {q.stdout.hex()} sum {total(x, y).hex()} cost {mc} logged {n} same {same}")
    print(f"{'ok  ' if not bad else 'FAIL'} model and sum: {len(ps)} runs, stdout equal to the model and to (a + b) mod 2^256")
    print(f"{'ok  ' if not bad else 'FAIL'} secret: one trace and one cost ({first[1]} instructions) for every pair, within {BUDGET}")
    for opt in ("-O0", "-O2"):
        cl = clang(d, ps, opt)
        agree = cl == [p[0] for p in preds]
        print(f"{'ok  ' if agree else 'FAIL'} clang {opt}: {len(ps)} pairs, clang's compiled lines and L's image give the same bytes")
        bad += not agree
    flipped = clang(d, ps[:3], "-O0", flip=1)
    seen = flipped != [p[0] for p in preds[:3]]
    print(f"{'ok  ' if seen else 'FAIL'} vacuity: a harness flipping one output bit disagrees")
    bad += not seen
    lcode = open(f"{d}/leaky.bin", "rb").read()
    lt = []
    for k, (x, y) in enumerate([(bytes([255] + [0] * 31), bytes([1] + [0] * 31)), (bytes(32), bytes([1] + [0] * 31))]):
        p = f"{d}/l{k}"
        with open(p, "wb") as f:
            f.write(elf(lcode, struct.pack("<8Q", *words(x, y))))
        os.chmod(p, 0o700)
        o = observe(p, lcode, {}, [], f"{d}/l{k}.log")
        lt.append((o["trace"], o["cost"]) if o else None)
    leaks = lt[0] is not None and lt[1] is not None and lt[0] != lt[1]
    print(f"{'ok  ' if leaks else 'FAIL'} vacuity: the leaky variant's trace depends on the arrays"
          f"{f' ({lt[0][1]} and {lt[1][1]} instructions)' if leaks else ''}")
    bad += not leaks
    distinct = len(outs) > 40
    print(f"{'ok  ' if distinct else 'FAIL'} vacuity: {len(outs)} distinct outputs over {len(ps)} pairs")
    bad += not distinct
    print(f"add-diff: {bad} failed")
    return 1 if bad else 0


sys.exit(main())
