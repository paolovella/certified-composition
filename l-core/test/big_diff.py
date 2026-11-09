#!/usr/bin/env python3
"""CAP-01: an image past the old ELF layout's 3920 bytes, loaded and run.

The model compiles a 300-statement program (S-USABLE S1's shape) to an image of more than 3920 bytes, which the old layout, with the data
segment at file offset 0x1000, could not hold. Here: the pipeline accepts it; Lean's `Rv.elf` and this repo's independent Python writer give
the same ELF, byte for byte; and QEMU runs it to the model's exit status and instruction count, reading the inputs the data segment holds.
Vacuity: a writer with the data segment at the old offset gives an ELF that does not run to the model's result.

Usage, from l-core/: python3 test/big_diff.py <scratch directory>
"""
import os
import struct
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from image2_diff import elf, observe  # noqa: E402


def old_elf(code, data):
    hdr = 64 + 2 * 56
    ident = bytes([0x7f, 0x45, 0x4c, 0x46, 2, 1, 1]) + bytes(9)
    head = ident + struct.pack("<HHIQQQIHHHHHH", 2, 243, 1, 0x10000 + hdr, 64, 0, 0, 64, 56, 2, 64, 0, 0)
    head += struct.pack("<IIQQQQQQ", 1, 5, 0, 0x10000, 0x10000, hdr + len(code), hdr + len(code), 0x1000)
    head += struct.pack("<IIQQQQQQ", 1, 6, 0x1000, 0x20000, 0x20000, len(data), 0x1000, 0x1000)
    return head + code + data


def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    g = subprocess.run(["lake", "env", "lean", "--run", "test/BigPred.lean", d], capture_output=True, text=True)
    if g.returncode != 0:
        sys.exit(f"prediction failed: {g.stdout[-1500:]} {g.stderr[-800:]}")
    ok_s, n, ret, cost, out = open(f"{d}/pred.txt").read().split(maxsplit=4)
    ret = int(ret.strip("[]"))
    code = open(f"{d}/big.bin", "rb").read()
    data = struct.pack("<4Q", 0x0123456789abcdef, 0xfedcba9876543210, 0x5555aaaa5555aaaa, 0x0f0f0f0f0f0f0f0f)
    bad = 0
    acc = ok_s == "true" and int(n) > 3920 and out.strip().endswith("done")
    print(f"{'ok  ' if acc else 'FAIL'} the pipeline accepts it: {n} bytes, past 3920; the model finishes")
    bad += not acc
    mine = elf(code, data)
    same = mine == open(f"{d}/big.elf", "rb").read()
    print(f"{'ok  ' if same else 'FAIL'} Lean's Rv.elf and the Python writer agree byte for byte ({len(mine)} bytes)")
    bad += not same
    p = f"{d}/big"
    with open(p, "wb") as f:
        f.write(mine)
    os.chmod(p, 0o700)
    o = observe(p, code, {}, [], f"{d}/big.log")
    run = o is not None and o["rc"] == ret % 256 and o["cost"] == int(cost)
    print(f"{'ok  ' if run else 'FAIL'} QEMU: exit {o and o['rc']} (model {ret % 256}), {o and o['cost']} instructions (model {cost})")
    bad += not run
    q = f"{d}/big_old"
    with open(q, "wb") as f:
        f.write(old_elf(code, data))
    os.chmod(q, 0o700)
    r = subprocess.run(["qemu-riscv64", q], capture_output=True, timeout=60)
    differs = r.returncode != ret % 256
    print(f"{'ok  ' if differs else 'FAIL'} vacuity: the old layout's ELF does not give the model's result (rc {r.returncode})")
    bad += not differs
    print(f"big-diff: {bad} failed")
    return 1 if bad else 0


sys.exit(main())
