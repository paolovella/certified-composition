#!/usr/bin/env python3
"""RC-01 step 6: crypto_verify_16's image under QEMU, against the model and against clang's compiled original.

`CTBytes.verify16_ct_bytes` says the 180-byte image is constant time on the model: the same PCs, addresses, cost and outcome whatever the
two secret arrays hold. `verify16_bound_bytes` says it runs at most 905 instructions. Here:

  model     QEMU runs the image on many pairs of arrays, and every run equals the model's prediction: PCs, addresses, result, cost
  secret    every run's trace and cost equal the first run's: the arrays change neither
  budget    every run is within 905 instructions
  clang     libsodium's verify.c, vendored and unmodified, compiled natively by clang at -O0 and -O2, gives the same answer as L's image on
            every pair, reading L's 64-bit result as its low 32 bits sign-extended (RC-01-READING section 3)
  vacuity   the checks can fail: the early exit's image has traces that depend on the arrays, both answers (0 and -1) occur among the
            pairs, and a harness that flips one bit of clang's answer is seen to disagree

Two stubs, stated: `export.h` defines SODIUM_EXPORT as empty, and `crypto_verify_64.h` defines its length as 64U, as the release does. The
headers L reads are the vendored ones. HAVE_EMMINTRIN_H is not defined, so clang compiles the portable branch, the one L reads.

This says nothing about QEMU's fidelity to hardware, about time, or about clang's own riscv64 compilation of the function.

Usage, from l-core/: python3 test/verify16_diff.py <scratch directory>
"""
import os
import random
import struct
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from image2_diff import literal, elf, observe  # noqa: E402

BYTES = "LCore/Slice2/CTBytes.lean"
SODIUM = os.path.abspath("../third_party/libsodium-1.0.20")
FUEL = 4000
BUDGET = 905
MASK = 2 ** 64 - 1

HARNESS = r"""
#include <stdio.h>
int crypto_verify_16(const unsigned char *x, const unsigned char *y);
int main(void) {
  unsigned char x[16], y[16];
  int flip = FLIP;
  while (1) {
    for (int k = 0; k < 16; k++) if (scanf("%hhu", &x[k]) != 1) return 0;
    for (int k = 0; k < 16; k++) if (scanf("%hhu", &y[k]) != 1) return 1;
    printf("%d\n", crypto_verify_16(x, y) ^ flip);
  }
}
"""


def pairs():
    r = random.Random(20261108)
    out = []
    base = bytes(r.randrange(256) for _ in range(16))
    out.append((base, base))
    for k in range(16):
        for delta in (1, 0x80, 0xff):
            y = bytearray(base)
            y[k] ^= delta
            out.append((base, bytes(y)))
    out.append((bytes(16), bytes([255] * 16)))
    out.append((bytes(16), bytes(16)))
    out.append((bytes([255] * 16), bytes([255] * 16)))
    for _ in range(40):
        x = bytes(r.randrange(256) for _ in range(16))
        out.append((x, x if r.random() < 0.3 else bytes(r.randrange(256) for _ in range(16))))
    return out


def words(x, y):
    return struct.unpack("<QQ", x) + struct.unpack("<QQ", y)


def predictions(d, cases):
    g = subprocess.run(["lake", "env", "lean", "--run", "test/Verify16Pred.lean", d],
                       input="".join(f"{i} {' '.join(map(str, w))} {FUEL}\n" for i, w in cases), capture_output=True, text=True)
    if g.returncode != 0:
        sys.exit(f"prediction failed: {g.stdout[-1500:]} {g.stderr[-800:]}")
    preds, cur = {}, None
    for line in open(f"{d}/pred.txt"):
        t = line.split()
        if t[0] == "CASE":
            cur = (t[1], tuple(int(v) for v in t[2:6]))
            preds[cur] = {"trace": []}
        elif t[0] in ("P", "A"):
            preds[cur]["trace"].append((t[0], int(t[1])))
        elif t[0] == "END":
            preds[cur].update(out=t[1], ret=None if t[2] == "none" else int(t[2]), cost=int(t[3]))
    return preds


def run_image(d, code, w):
    p = f"{d}/v"
    with open(p, "wb") as f:
        f.write(elf(code, struct.pack("<QQQQ", *w)))
    os.chmod(p, 0o700)
    return observe(p, code, {}, [], f"{d}/v.log")


def clang_answers(d, ps, opt, flip=0):
    inc = f"{d}/inc"
    os.makedirs(inc, exist_ok=True)
    with open(f"{inc}/export.h", "w") as f:
        f.write("#define SODIUM_EXPORT\n")
    with open(f"{inc}/crypto_verify_64.h", "w") as f:
        f.write("#include <stddef.h>\n#define crypto_verify_64_BYTES 64U\nsize_t crypto_verify_64_bytes(void);\n"
                "int crypto_verify_64(const unsigned char *x, const unsigned char *y);\n")
    with open(f"{d}/harness.c", "w") as f:
        f.write(HARNESS.replace("FLIP", str(flip)))
    exe = f"{d}/native{opt}{flip}"
    c = subprocess.run(["clang", opt, "-I", inc, "-I", SODIUM, f"{SODIUM}/verify.c", f"{d}/harness.c", "-o", exe],
                       capture_output=True, text=True)
    if c.returncode != 0:
        sys.exit(f"clang failed: {c.stderr[-1500:]}")
    inp = "".join(" ".join(map(str, x)) + " " + " ".join(map(str, y)) + "\n" for x, y in ps)
    r = subprocess.run([exe], input=inp, capture_output=True, text=True, timeout=60)
    return [int(v) for v in r.stdout.split()]


def as_int(v):
    low = v & 0xffffffff
    return low - (1 << 32) if low >= 1 << 31 else low


def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    img = literal("verify16Nats", BYTES)
    if img is None:
        print("verify16-diff: the literal was not found")
        return 2
    ps = pairs()
    cases = [("verify16", words(x, y)) for x, y in ps]
    # each pair differs somewhere: on equal arrays the early exit never exits
    early_ps = [(bytes([1] + [0] * 15), bytes(16)), (bytes([0] * 8 + [1] + [0] * 7), bytes(16)), (bytes([0] * 15 + [1]), bytes(16))]
    preds = predictions(d, cases)
    bad = 0

    obs = []
    for (i, w) in cases:
        o = run_image(d, img, w)
        m = preds[(i, w)]
        if o is None or m["out"] != "done" or o["rc"] < 0 or o["trace"] != m["trace"] or o["cost"] != m["cost"] or o["a0"] != m["ret"]:
            print(f"FAIL model {w}")
            bad += 1
        obs.append(o)
    if not bad:
        print(f"ok   model: {len(cases)} runs, every PC, address, result and cost equal the model's")

    first = obs[0]
    diff = sum(1 for o in obs if o is None or (o["trace"], o["cost"]) != (first["trace"], first["cost"]))
    if diff:
        print(f"FAIL secret: {diff} runs differ from the first in trace or cost")
        bad += 1
    else:
        print(f"ok   secret: {len(obs)} runs, one trace and one cost ({first['cost']} instructions), whatever the arrays hold")

    over = [o["cost"] for o in obs if o is not None and o["cost"] > BUDGET]
    if over:
        print(f"FAIL budget: {over[:3]} over {BUDGET}")
        bad += 1
    else:
        print(f"ok   budget: every run within {BUDGET} instructions; the machine runs {first['cost']}")

    l_answers = [as_int(o["a0"]) if o is not None else None for o in obs]
    for opt in ("-O0", "-O2"):
        c = clang_answers(d, ps, opt)
        if c != l_answers:
            print(f"FAIL clang {opt}: {sum(1 for a, b in zip(c, l_answers) if a != b)} of {len(ps)} disagree")
            bad += 1
        else:
            print(f"ok   clang {opt}: {len(ps)} pairs, clang's compiled original and L's image give the same answer")

    seen = set(l_answers)
    flipped = clang_answers(d, ps, "-O2", flip=1)
    early = [run_image(d, img_early, words(x, y)) for x, y in early_ps] if (img_early := early_image(d)) else []
    early_leaks = len(early) == 3 and all(o is not None for o in early) and len({(tuple(o["trace"]), o["cost"]) for o in early}) > 1
    if seen == {0, -1} and flipped != l_answers and early_leaks:
        print(f"ok   vacuity: answers 0 and -1 both occur; a harness flipping one bit is seen to disagree; the early exit's image runs "
              f"{sorted(o['cost'] for o in early)} instructions on three pairs")
    else:
        print(f"FAIL vacuity: answers {seen}, flipped disagrees {flipped != l_answers}, early exit leaks {early_leaks}")
        bad += 1

    print(f"verify16-diff: {bad} failed")
    return 1 if bad else 0


def early_image(d):
    g = subprocess.run(["lake", "env", "lean", "--run", "test/Verify16Pred.lean", d, "--dump-early"], input="", capture_output=True,
                       text=True)
    p = f"{d}/early.bin"
    return open(p, "rb").read() if g.returncode == 0 and os.path.exists(p) else None


if __name__ == "__main__":
    sys.exit(main())
