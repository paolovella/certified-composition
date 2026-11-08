#!/usr/bin/env python3
"""RC-02 step 3: compiled outputs under QEMU, against the model.

For `put1` (one byte stored, then the word written) and `addOne` (16 bytes each plus one, then written), on several inputs: the image the
model compiles is run under qemu-riscv64, and its stdout and exit status must equal the model's emitted bytes and result. Vacuity: a harness
that flips one byte of the model's expected output is seen to disagree, and the outputs differ between inputs.

Usage, from l-core/: python3 test/out_diff.py <scratch directory>
"""
import os
import struct
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from image2_diff import elf  # noqa: E402

CASES = [("put1", 0x1122334455667788, 0), ("put1", 0, 0), ("put1", 2 ** 64 - 1, 0),
         ("addOne", 0, 0), ("addOne", 0x0102030405060708, 0xfffefdfcfbfaf9f8), ("addOne", 2 ** 64 - 1, 2 ** 64 - 1),
         ("addOne", 0x00ff00ff00ff00ff, 0x7f807f807f807f80)]


def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    g = subprocess.run(["lake", "env", "lean", "--run", "test/OutPred.lean", d],
                       input="".join(f"{n} {a} {b}\n" for n, a, b in CASES), capture_output=True, text=True)
    if g.returncode != 0:
        sys.exit(f"prediction failed: {g.stdout[-1500:]} {g.stderr[-800:]}")
    preds, cur = [], None
    for line in open(f"{d}/pred.txt"):
        t = line.split()
        if t[0] == "CASE":
            cur = {"name": t[1], "a": int(t[2]), "b": int(t[3])}
            preds.append(cur)
        elif t[0] == "IMG":
            cur["img"] = bytes(int(v) for v in t[1:])
        elif t[0] == "OUT":
            cur["out"] = bytes(int(v) for v in t[1:])
        elif t[0] == "RET":
            cur["ret"], cur["outcome"] = int(t[1]), t[2]
    bad = 0
    outs = set()
    for k, c in enumerate(preds):
        p = f"{d}/o{k}"
        with open(p, "wb") as f:
            f.write(elf(c["img"], struct.pack("<QQ", c["a"], c["b"])))
        os.chmod(p, 0o700)
        r = subprocess.run(["qemu-riscv64", p], capture_output=True, timeout=60)
        ok = c["outcome"].endswith("done") and r.stdout == c["out"] and r.returncode == c["ret"] % 256
        bad += not ok
        outs.add((c["name"], c["out"]))
        print(f"{'ok  ' if ok else 'FAIL'} {c['name']:7} {c['a']:#018x} {c['b']:#018x}: stdout {r.stdout.hex()} model {c['out'].hex()}, "
              f"rc {r.returncode} model {c['ret']}")
        if k == 0:
            flipped = bytes([c["out"][0] ^ 1]) + c["out"][1:]
            seen = r.stdout != flipped
            print(f"{'ok  ' if seen else 'FAIL'} vacuity: a flipped expected byte disagrees")
            bad += not seen
    distinct = len({o for n, o in outs if n == "addOne"}) == 4
    print(f"{'ok  ' if distinct else 'FAIL'} vacuity: addOne's four inputs give four outputs")
    bad += not distinct
    print(f"out-diff: {len(preds)} runs, {bad} failed")
    return 1 if bad else 0


sys.exit(main())
