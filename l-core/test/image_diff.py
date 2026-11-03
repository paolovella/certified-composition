#!/usr/bin/env python3
"""VS-1 step 8: run the literal image under QEMU and compare it with the model and with itself.

Independent of the Lean side where it can be: it reads the bytes from Image.lean's source text, writes its own ELF, and decodes
loads and stores itself, so each address is derived from QEMU's registers and not from the model. Its own ELF must equal the Lean
`elf`'s, byte for byte.

Checks:
  model     every input: result, cost, outcome, and the whole leakage (PCs and addresses) equal the model's
  secret    inputs differing only in the secret word give identical PC and address traces, cost and result, in changed
            environments and argv
  vacuity   the same comparison finds a difference on the tampered image, and when the public word changes

It says nothing about QEMU's fidelity to hardware, about timing, or about any other program.

Usage, from l-core/: python3 test/image_diff.py <scratch directory>
"""
import os
import random
import re
import struct
import subprocess
import sys

MASK = 2 ** 64 - 1
SECRETS = [0, 1, 5, 6, 250, 2 ** 31, 2 ** 63, 2 ** 64 - 1, 0x0102030405060708]
PUBLICS = [0, 1, 3, 200, 2 ** 32, 2 ** 63, 2 ** 64 - 1, 2 ** 64 - 2]
ENVS = [
    ({}, []),
    ({"A": "b" * 40}, ["x", "y", "z"]),
    ({"LONG": "c" * 4000, "B": "1"}, ["only"]),
]

def literal():
    src = open("LCore/Slice/Image.lean").read()
    m = re.search(r"def imageNats : List Nat :=\s*\[([^\]]*)\]", src)
    return bytes(int(t) for t in m.group(1).replace("\n", " ").split(",")) if m else None

def elf(code, data):
    """A static RV64 ELF, written here and not in Lean."""
    hdr = 64 + 2 * 56
    ident = bytes([0x7f, 0x45, 0x4c, 0x46, 2, 1, 1]) + bytes(9)
    head = ident + struct.pack("<HHIQQQIHHHHHH", 2, 243, 1, 0x10000 + hdr, 64, 0, 0, 64, 56, 2, 64, 0, 0)
    head += struct.pack("<IIQQQQQQ", 1, 5, 0, 0x10000, 0x10000, hdr + len(code), hdr + len(code), 0x1000)
    head += struct.pack("<IIQQQQQQ", 1, 6, 0x1000, 0x20000, 0x20000, len(data), 0x1000, 0x1000)
    body = head + code
    return body + bytes(0x1000 - len(body)) + data

def inputs(a, b):
    return struct.pack("<QQ", a, b)

def write(d, name, code, a, b):
    p = f"{d}/{name}"
    with open(p, "wb") as f:
        f.write(elf(code, inputs(a, b)))
    os.chmod(p, 0o700)
    return p

def sext(v, n):
    return v - (1 << n) if v >= 1 << (n - 1) else v

def access(word, regs):
    """The address a load or store touches, from the instruction and the registers. None if it is neither."""
    op = word & 127
    rs1 = (word >> 15) & 31
    base = 0 if rs1 == 0 else regs.get(rs1, 0)
    if op == 0x03:
        return (base + sext(word >> 20, 12)) & MASK
    if op == 0x23:
        return (base + sext(((word >> 25) << 5) | ((word >> 7) & 31), 12)) & MASK
    return None

def observe(p, code, env, argv, log):
    """QEMU's run as the model's observation: leakage as PCs and addresses, a0 at the exit, instructions, how it ended."""
    if os.path.exists(log):
        os.remove(log)
    r = subprocess.run(["qemu-riscv64", "-one-insn-per-tb", "-d", "cpu,nochain", "-D", log, p] + argv,
                       capture_output=True, env=env)
    trace, regs, pc, a0 = [], {}, None, None
    steps = []
    for line in open(log, errors="replace"):
        m = re.match(r"\s*pc\s+([0-9a-f]+)", line)
        if m:
            if pc is not None:
                steps.append((pc, regs))
            pc, regs = int(m.group(1), 16), {}
            continue
        for name, val in re.findall(r"x(\d+)/\w+\s+([0-9a-f]+)", line):
            regs[int(name)] = int(val, 16)
    steps.append((pc, regs))
    for pc, regs in steps:
        trace.append(("P", pc))
        off = pc - 0x100b0
        word = struct.unpack("<I", code[off:off + 4])[0]
        a = access(word, regs)
        if a is not None:
            trace.append(("A", a))
    a0 = steps[-1][1].get(10)
    return {"trace": trace, "a0": a0, "cost": len(steps), "rc": r.returncode}

def predictions(d, cases):
    g = subprocess.run(["lake", "env", "lean", "--run", "test/ImagePred.lean", d],
                       input="".join(f"{a} {b}\n" for a, b in cases), capture_output=True, text=True)
    if g.returncode != 0:
        sys.exit(f"prediction failed: {g.stdout[-1500:]} {g.stderr[-800:]}")
    preds, cur = {}, None
    for line in open(f"{d}/pred.txt"):
        t = line.split()
        if t[0] == "CASE":
            cur = (int(t[1]), int(t[2]))
            preds[cur] = {"trace": []}
        elif t[0] in ("P", "A"):
            preds[cur]["trace"].append((t[0], int(t[1])))
        elif t[0] == "END":
            preds[cur].update(out=t[1], ret=int(t[2]), cost=int(t[3]))
    return preds

def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    code = literal()
    if code is None:
        print("image-diff: literal not found")
        return 2
    rng = random.Random(20261103)
    secrets = SECRETS + [rng.getrandbits(64) for _ in range(8)]
    publics = PUBLICS + [rng.getrandbits(64) for _ in range(4)]
    cases = [(a, b) for b in publics for a in secrets]
    preds = predictions(d, cases)
    bad = 0

    # The two ELF writers agree.
    if open(f"{d}/lean_elf", "rb").read() != elf(code, inputs(5, 3)):
        print("FAIL the script's ELF differs from the Lean elf")
        bad += 1
    else:
        print("ok   the script's ELF equals the Lean elf, byte for byte")

    # Every input against the model.
    obs = {}
    addrs = 0
    for k, (a, b) in enumerate(cases):
        env, argv = ENVS[k % len(ENVS)]
        p = write(d, "run", code, a, b)
        o = observe(p, code, env, argv, f"{d}/run.log")
        obs[(a, b)] = o
        m = preds[(a, b)]
        addrs += sum(1 for t in o["trace"] if t[0] == "A")
        why = None
        if m["out"] != "done" or o["rc"] < 0:
            why = f"outcome {m['out']}, rc {o['rc']}"
        elif o["trace"] != m["trace"]:
            why = "leakage differs"
        elif o["a0"] != m["ret"] or o["rc"] != m["ret"] % 256:
            why = f"result: a0 {o['a0']}, rc {o['rc']}, model {m['ret']}"
        elif o["cost"] != m["cost"]:
            why = f"cost {o['cost']}, model {m['cost']}"
        if why:
            print(f"FAIL model ({a}, {b}): {why}")
            bad += 1
    print(f"ok   model: {len(cases)} inputs, {sum(o['cost'] for o in obs.values())} instructions, {addrs} addresses compared"
          if not bad else f"FAIL model comparison")

    # The address comparison can fail: wrong addresses in a prediction are seen, and the addresses are not all one value.
    first = cases[0]
    real, want = obs[first]["trace"], preds[first]["trace"]
    no_addr = [t for t in want if t[0] != "A"]
    idx = next(i for i, t in enumerate(want) if t[0] == "A")
    shifted = want[:idx] + [("A", want[idx][1] + 8)] + want[idx + 1:]
    distinct = {t[1] for o in obs.values() for t in o["trace"] if t[0] == "A"}
    if real == no_addr or real == shifted or len(distinct) < 2:
        print("FAIL the address comparison cannot see a wrong address")
        bad += 1
    else:
        print(f"ok   addresses: a prediction with none, or with one shifted by 8, would fail; {len(distinct)} distinct addresses: "
              + ", ".join(hex(x) for x in sorted(distinct)))

    # Secrets do not show, on real runs, across environments.
    leaks = 0
    for b in publics:
        base = obs[(secrets[0], b)]
        for a in secrets[1:]:
            o = obs[(a, b)]
            if (o["trace"], o["cost"], o["a0"]) != (base["trace"], base["cost"], base["a0"]):
                leaks += 1
                print(f"FAIL secret: ({a}, {b}) differs from ({secrets[0]}, {b})")
    bad += leaks
    print(f"ok   secret: {len(cases) - len(publics)} comparisons, no difference" if not leaks else f"FAIL secret: {leaks}")

    # The comparison can see a difference.
    tampered = bytearray(code)
    tampered[30] = 3
    seen = 0
    for b in publics:
        ts = {}
        for a in (0, 5):
            p = write(d, "tamper", bytes(tampered), a, b)
            o = observe(p, bytes(tampered), {}, [], f"{d}/tamper.log")
            ts[a] = (o["trace"], o["cost"])
        seen += ts[0] != ts[5]
    pub = sum(1 for b in publics[1:] if obs[(5, b)]["a0"] != obs[(5, publics[0])]["a0"]
              or obs[(5, b)]["trace"] != obs[(5, publics[0])]["trace"])
    if seen == 0 or pub == 0:
        print(f"FAIL vacuity: tampered {seen}, public {pub}")
        bad += 1
    else:
        print(f"ok   vacuity: the tampered image's secret shows on {seen} of {len(publics)} public words; "
              f"{pub} of {len(publics) - 1} public words change the observation")

    print(f"image-diff: {bad} failed")
    return 1 if bad else 0

sys.exit(main())
