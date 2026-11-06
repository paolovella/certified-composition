#!/usr/bin/env python3
"""VS-2 step 8: run the second slice's literal images under QEMU and compare them with the model and with themselves.

Independent of the Lean side where it can be, as image_diff.py is: it reads the bytes from Image.lean's source text, writes its own ELF,
and derives every load's and store's address from QEMU's registers, not from the model. Its own ELF must equal `elf`'s, byte for byte.

Checks:
  model     scan, every input: result, cost, outcome, and the whole leakage (PCs and addresses) equal the model's
  prefix    spin, which never exits: QEMU's first N instructions equal the model's run at fuel N, PCs and addresses
  public    the public word moves the addresses: different counts, and the index wrapping at 64
  secret    inputs differing only in the secret word give identical traces, cost and result, in changed environments and argv;
            for spin, identical prefixes
  vacuity   on tamperedIndex the secret shows through an address while the PCs stay identical, and on tamperedGuard through the PCs:
            the same comparisons can see a difference

It says nothing about QEMU's fidelity to hardware, about timing, or about any other program.

Usage, from l-core/: python3 test/image2_diff.py <scratch directory>
"""
import os
import random
import re
import signal
import struct
import subprocess
import sys
import time

MASK = 2 ** 64 - 1
SECRETS = [0, 1, 5, 6, 250, 2 ** 31, 2 ** 63, 2 ** 64 - 1, 0x0102030405060708]
PUBLICS = [0, 1, 2, 3, 7, 63, 64, 65, 100]
PREFIX = 300
ENVS = [
    ({}, []),
    ({"A": "b" * 40}, ["x", "y", "z"]),
    ({"LONG": "c" * 4000, "B": "1"}, ["only"]),
]


def literal(name, path="LCore/Slice2/Image.lean"):
    src = open(path).read()
    m = re.search(r"def " + name + r" : List Nat :=\s*\[([^\]]*)\]", src)
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


def write(d, name, code, a, b):
    p = f"{d}/{name}"
    with open(p, "wb") as f:
        f.write(elf(code, struct.pack("<QQ", a, b)))
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


def observe(p, code, env, argv, log, limit=None):
    """QEMU's run as the model's observation. With `limit`, the program is not expected to exit: QEMU is stopped, as a process group, once
    its log holds more than `limit` instructions, and only the first `limit` are kept. A run that ends before then is reported."""
    if os.path.exists(log):
        os.remove(log)
    q = subprocess.Popen(["qemu-riscv64", "-one-insn-per-tb", "-d", "cpu,nochain", "-D", log, p] + argv,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env, start_new_session=True)
    t0 = time.time()
    stopped = False
    while q.poll() is None:
        time.sleep(0.05)
        if limit is not None and os.path.exists(log):
            with open(log, errors="replace") as f:
                n = sum(1 for line in f if re.match(r"\s*pc\s", line))
            if n > limit + 1:
                os.killpg(q.pid, signal.SIGKILL)
                q.wait()
                stopped = True
        if time.time() - t0 > 60:
            os.killpg(q.pid, signal.SIGKILL)
            q.wait()
            return None
    steps, regs, pc = [], {}, None
    for line in open(log, errors="replace"):
        m = re.match(r"\s*pc\s+([0-9a-f]+)", line)
        if m:
            if pc is not None:
                steps.append((pc, regs))
            pc, regs = int(m.group(1), 16), {}
            continue
        for name, val in re.findall(r"x(\d+)/\w+\s+([0-9a-f]+)", line):
            regs[int(name)] = int(val, 16)
    if pc is not None and not stopped:
        steps.append((pc, regs))
    if limit is not None:
        if len(steps) < limit:
            return None
        steps = steps[:limit]
    trace = []
    for pc, regs in steps:
        trace.append(("P", pc))
        off = pc - 0x100b0
        word = struct.unpack("<I", code[off:off + 4])[0]
        a = access(word, regs)
        if a is not None:
            trace.append(("A", a))
    return {"trace": trace, "a0": steps[-1][1].get(10), "cost": len(steps), "rc": q.returncode, "stopped": stopped}


def predictions(d, cases):
    g = subprocess.run(["lake", "env", "lean", "--run", "test/Image2Pred.lean", d],
                       input="".join(f"{i} {a} {b} {n}\n" for i, a, b, n in cases), capture_output=True, text=True)
    if g.returncode != 0:
        sys.exit(f"prediction failed: {g.stdout[-1500:]} {g.stderr[-800:]}")
    preds, cur = {}, None
    for line in open(f"{d}/pred.txt"):
        t = line.split()
        if t[0] == "CASE":
            cur = (t[1], int(t[2]), int(t[3]), int(t[4]))
            preds[cur] = {"trace": []}
        elif t[0] in ("P", "A"):
            preds[cur]["trace"].append((t[0], int(t[1])))
        elif t[0] == "END":
            preds[cur].update(out=t[1], ret=None if t[2] == "none" else int(t[2]), cost=int(t[3]))
    return preds


def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    img = {"scan": literal("scanNats"), "spin": literal("spinNats")}
    if None in img.values():
        print("image2-diff: a literal was not found")
        return 2
    tidx = bytearray(img["scan"]); tidx[23] = 0
    tguard = bytearray(img["scan"]); tguard[6] = 3
    img["tidx"], img["tguard"] = bytes(tidx), bytes(tguard)
    rng = random.Random(20261106)
    secrets = SECRETS + [rng.getrandbits(64) for _ in range(4)]
    fuel = lambda b: 27 * b + 20
    scan_cases = [("scan", a, b, fuel(b)) for b in PUBLICS for a in secrets]
    spin_cases = [("spin", a, b, PREFIX) for b in (0, 1, 9) for a in secrets]
    tamper_cases = [("tidx", a, 1, 14) for a in (1, 2)] + [("tguard", a, 1, 200) for a in (1, 2)]
    preds = predictions(d, scan_cases + spin_cases + tamper_cases)
    bad = 0

    if open(f"{d}/lean_elf", "rb").read() != elf(img["scan"], struct.pack("<QQ", 5, 3)):
        print("FAIL the script's ELF differs from the Lean elf")
        bad += 1
    else:
        print("ok   the script's ELF equals the Lean elf, byte for byte")

    # scan, every input, against the model.
    obs, addrs, fails = {}, 0, 0
    for k, (i, a, b, n) in enumerate(scan_cases):
        env, argv = ENVS[k % len(ENVS)]
        o = observe(write(d, "run", img[i], a, b), img[i], env, argv, f"{d}/run.log")
        m = preds[(i, a, b, n)]
        why = None
        if o is None:
            why = "QEMU gave no verdict"
        elif m["out"] != "done" or o["rc"] < 0:
            why = f"outcome {m['out']}, rc {o['rc']}"
        elif o["trace"] != m["trace"]:
            why = "leakage differs"
        elif o["a0"] != m["ret"] or o["rc"] != m["ret"] % 256:
            why = f"result: a0 {o['a0']}, rc {o['rc']}, model {m['ret']}"
        elif o["cost"] != m["cost"]:
            why = f"cost {o['cost']}, model {m['cost']}"
        if why:
            print(f"FAIL scan ({a}, {b}): {why}")
            fails += 1
        else:
            obs[(a, b)] = o
            addrs += sum(1 for t in o["trace"] if t[0] == "A")
    bad += fails
    if not fails:
        print(f"ok   scan against the model: {len(scan_cases)} inputs, {sum(o['cost'] for o in obs.values())} instructions, "
              f"{addrs} addresses")

    # spin, which never exits, as a prefix.
    sobs, fails = {}, 0
    for k, (i, a, b, n) in enumerate(spin_cases):
        env, argv = ENVS[k % len(ENVS)]
        o = observe(write(d, "spin", img[i], a, b), img[i], env, argv, f"{d}/spin.log", limit=n)
        m = preds[(i, a, b, n)]
        if o is None or not o["stopped"] or m["out"] != "fuel" or o["trace"] != m["trace"] or o["cost"] != m["cost"]:
            print(f"FAIL spin ({a}, {b}): " + ("no verdict" if o is None else f"stopped {o['stopped']}, model {m['out']}"))
            fails += 1
        else:
            sobs[(a, b)] = o
    bad += fails
    if not fails:
        print(f"ok   spin as a prefix: {len(spin_cases)} runs stopped by the harness, never by the program; the first {PREFIX} "
              f"instructions equal the model at fuel {PREFIX}")

    # The comparison can fail: a prediction with no addresses, or one shifted by 8, or one PC moved, would not equal the real run.
    k = ("scan", secrets[0], 3, fuel(3))
    real, want = obs[(secrets[0], 3)]["trace"], preds[k]["trace"]
    no_addr = [x for x in want if x[0] != "A"]
    ia = next(j for j, x in enumerate(want) if x[0] == "A")
    ip = max(j for j, x in enumerate(want) if x[0] == "P")
    shifted = want[:ia] + [("A", want[ia][1] + 8)] + want[ia + 1:]
    moved = want[:ip] + [("P", want[ip][1] + 4)] + want[ip + 1:]
    if real != want or real in (no_addr, shifted, moved):
        print("FAIL the comparison cannot see a wrong prediction")
        bad += 1
    else:
        print("ok   the comparison sees a wrong prediction: none of no addresses, one address shifted by 8, or the last PC moved, passes")

    # The public word moves the addresses.
    if obs:
        stores = {b: [t[1] for t in obs[(secrets[0], b)]["trace"] if t[0] == "A" and 0x20200 <= t[1] < 0x20400]
                  for b in PUBLICS}
        distinct = {b: len(set(v)) for b, v in stores.items()}
        # The counter starts at the public word and counts down, so its first access is at slot (n mod 64).
        wraps = stores[64][0] == 0x20200 and stores[65][0] == stores[1][0] == 0x20208 and stores[63][0] == 0x20200 + 8 * 63
        changes = len({tuple(v) for v in stores.values()})
        if changes < len(PUBLICS) - 1 or not wraps:
            print(f"FAIL public: {changes} distinct array traces over {len(PUBLICS)} words, wrap {wraps}")
            bad += 1
        else:
            print(f"ok   public: {changes} distinct array-address traces over {len(PUBLICS)} public words; the first access is "
                  f"slot 63 at 63, slot 0 at 64 and slot 1 at 65 as at 1, so the index wraps; at 100, {distinct[100]} distinct slots")

    # Secrets do not show, on real runs, across environments.
    leaks = 0
    for b in PUBLICS:
        base = obs.get((secrets[0], b))
        for a in secrets[1:]:
            o = obs.get((a, b))
            if base is None or o is None or (o["trace"], o["cost"], o["a0"]) != (base["trace"], base["cost"], base["a0"]):
                leaks += 1
    for b in (0, 1, 9):
        base = sobs.get((secrets[0], b))
        for a in secrets[1:]:
            o = sobs.get((a, b))
            if base is None or o is None or o["trace"] != base["trace"]:
                leaks += 1
    bad += leaks
    print(f"ok   secret: {(len(PUBLICS) + 3) * (len(secrets) - 1)} comparisons, scan and spin, no difference"
          if not leaks else f"FAIL secret: {leaks}")

    # The comparisons can see a difference.
    t = {}
    for i, a, b, n in tamper_cases:
        # tamperedIndex is cut at 14 instructions, where the address shows; tamperedGuard runs to its exit.
        o = observe(write(d, i, img[i], a, b), img[i], {}, [], f"{d}/{i}.log", limit=n if i == "tidx" else None)
        m = preds[(i, a, b, n)]
        same = o is not None and o["trace"] == m["trace"]
        t[(i, a)] = (o, same)
    ok = all(s for _, s in t.values())
    oi1, oi2 = t[("tidx", 1)][0], t[("tidx", 2)][0]
    og1, og2 = t[("tguard", 1)][0], t[("tguard", 2)][0]
    pcs = lambda o: [x for x in o["trace"] if x[0] == "P"]
    if ok and oi1 and oi2 and og1 and og2 and pcs(oi1) == pcs(oi2) and oi1["trace"] != oi2["trace"] and og1["trace"] != og2["trace"]:
        print("ok   vacuity: on tamperedIndex the secret shows in an address with the PCs identical, and on tamperedGuard in the PCs; "
              "both runs equal the model's")
    else:
        print("FAIL vacuity: the comparison did not see the tampered images' leaks, or they did not match the model")
        bad += 1

    print(f"image2-diff: {bad} failed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
