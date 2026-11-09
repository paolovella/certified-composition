#!/usr/bin/env python3
"""CAP-01 part 3: literals past 12 bits, compiled and run.

For each constant c, the program `x0 := c; write(x0)` is compiled by the model. For every constant the model accepts, QEMU runs its
image, and the 8 bytes it writes must equal c, little-endian, and the model's own output. The constants: HChaCha20's four, 0xffffffff and
fe25519's 0x7ffffffffffff mask, the 12-bit and 32-bit edges, and random signed 32-bit values, plain and shifted right.

The named targets must be accepted. 0x7ffff800 must be refused: on RV64 `lui` sign-extends, so the naive split `lui 0x80000; addi -2048`
gives 0xffffffff7ffff800. `litPlan` computes the value of its split and sees that it is wrong, so the case is the validation's own vacuity
witness. Vacuity also: a constant no plan builds is refused, and plans of all three sizes are used.

Usage, from l-core/: python3 test/lit_diff.py <scratch directory>
"""
import os
import random
import struct
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from image2_diff import elf  # noqa: E402

M = 2 ** 64


def consts():
    cs = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574, 0xffffffff, 0x7ffffffffffff, 2047, 2048, M - 2048, M - 2049,
          0x7fffffff, M - 0x80000000, 0x7ffff800, 0x7ffff7ff, 19, 255]
    r = random.Random(20261109)
    for _ in range(12):
        v = r.randrange(-2 ** 31, 2 ** 31)
        cs.append(v % M)
        cs.append((v % M) >> r.randrange(1, 40))
    return cs


def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    cs = consts() + [0x123456789abcdef0]
    g = subprocess.run(["lake", "env", "lean", "--run", "test/LitPred.lean", d], input="".join(f"{c}\n" for c in cs),
                       capture_output=True, text=True)
    if g.returncode != 0:
        sys.exit(f"prediction failed: {g.stdout[-1500:]} {g.stderr[-800:]}")
    rows = [l.split(maxsplit=3) for l in open(f"{d}/pred.txt")]
    bad = 0
    sizes = set()
    refused = []
    for k, row in enumerate(rows[:-1]):
        c, ok, n = int(row[0]), row[1], int(row[2])
        model = bytes(int(v) for v in row[3].split()) if len(row) > 3 else b""
        code = open(f"{d}/l{k}.bin", "rb").read()
        p = f"{d}/l{k}"
        with open(p, "wb") as f:
            f.write(elf(code, bytes(8)))
        os.chmod(p, 0o700)
        if ok != "true":
            refused.append(c)
            continue
        q = subprocess.run(["qemu-riscv64", p], capture_output=True, timeout=60)
        want = struct.pack("<Q", c)
        good = q.stdout == want == model
        sizes.add(n)
        bad += not good
        if not good:
            print(f"FAIL {c:#x}: accepted {ok}, qemu {q.stdout.hex()}, model {model.hex()}, want {want.hex()}")
    acc = len(rows) - 1 - len(refused)
    print(f"{'ok  ' if not bad else 'FAIL'} {acc} accepted literals: QEMU writes each one, equal to the model's output and to the literal")
    targets = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574, 0xffffffff, 0x7ffffffffffff, 2048, M - 2049]
    tok = not any(t in refused for t in targets)
    print(f"{'ok  ' if tok else 'FAIL'} the targets are accepted: HChaCha20's constants, 0xffffffff, 0x7ffffffffffff, and the 12-bit edges")
    bad += not tok
    edge = 0x7ffff800 in refused
    print(f"{'ok  ' if edge else 'FAIL'} vacuity: 0x7ffff800 is refused, whose naive lui/addi split is wrong on RV64")
    bad += not edge
    print(f"     refused: {', '.join(hex(c) for c in refused)}")
    seen = sizes == {1, 2, 3}
    print(f"{'ok  ' if seen else 'FAIL'} vacuity: plans of 1, 2 and 3 instructions are all used ({sorted(sizes)})")
    bad += not seen
    nop = rows[-1][1] == "false"
    print(f"{'ok  ' if nop else 'FAIL'} vacuity: {cs[-1]:#x}, which no plan builds, is refused")
    bad += not nop
    print(f"lit-diff: {bad} failed")
    return 1 if bad else 0


sys.exit(main())
