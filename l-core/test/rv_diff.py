#!/usr/bin/env python3
"""VS-1 step 4: compare the RV model with QEMU, instruction by instruction.

For each case in RvCases.lean, the model predicts its outcome, cost, and every step's PC and registers. QEMU runs the
same ELF and logs the same. The first step's sp is the loader's and is not compared: the first instruction replaces it.

Leaked addresses are compared too: this script decodes each load and store itself, and computes its address from QEMU's registers. It is
evidence on these cases, under QEMU, and no more.

Usage, from l-core/:
  python3 test/rv_diff.py <scratch directory>             compare the model with QEMU
  python3 test/rv_diff.py <scratch directory> --mutants   the harness finds a wrong model
Exit 0 if every exact case matches and every expected deviation really deviates, or, with --mutants, if every broken
model is caught.
"""
import os
import re
import subprocess
import sys

def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

def parse_log(path):
    """Each logged state: PC, then x1 to x31."""
    steps, cur = [], None
    for line in open(path, errors="replace"):
        m = re.match(r"\s*pc\s+([0-9a-f]+)", line)
        if m:
            cur = {"pc": int(m.group(1), 16), "x": {}}
            steps.append(cur)
            continue
        if cur is not None:
            for name, val in re.findall(r"x(\d+)/\w+\s+([0-9a-f]+)", line):
                cur["x"][int(name)] = int(val, 16)
    return steps

def sext(v, n):
    return v - (1 << n) if v >= 1 << (n - 1) else v

def access(word, regs):
    """The address a load or store touches, from the instruction and the registers. None if it is neither."""
    op = word & 127
    rs1 = (word >> 15) & 31
    base = 0 if rs1 == 0 else regs.get(rs1, 0)
    if op == 0x03:
        return (base + sext(word >> 20, 12)) & (2 ** 64 - 1)
    if op == 0x23:
        return (base + sext(((word >> 25) << 5) | ((word >> 7) & 31), 12)) & (2 ** 64 - 1)
    return None

def word_at(image, pc):
    off = pc - 0x100b0 + 176
    return int.from_bytes(image[off:off + 4], "little") if 176 <= off and off + 4 <= 0x1000 else 0

def compare(pred, steps, image):
    """The first difference between the model's steps and QEMU's, or None."""
    if len(pred) != len(steps):
        return f"{len(pred)} predicted steps, {len(steps)} logged"
    for i, (p, s) in enumerate(zip(pred, steps)):
        if p[0] != s["pc"]:
            return f"step {i}: pc model {p[0]:#x}, qemu {s['pc']:#x}"
        want = access(word_at(image, s["pc"]), s["x"])
        if p[32] != want:
            return f"step {i}: address model {p[32]}, qemu {want}"
        for r in range(1, 32):
            if i == 0 and r == 2:
                continue
            if p[r] != s["x"].get(r):
                return f"step {i}: x{r} model {p[r]:#x}, qemu {s['x'].get(r, 0):#x}"
    return None

def check(name, d):
    lines = open(f"{d}/{name}.pred").read().splitlines()
    out, a0, cost, kind = lines[0].split()
    a0, cost = int(a0, 16), int(cost)
    pred = [[None if t == "-" else int(t, 16) for t in l.split()] for l in lines[1:]]
    image = open(f"{d}/{name}", "rb").read()
    log = f"{d}/{name}.log"
    if os.path.exists(log):
        os.remove(log)
    r = subprocess.run(["qemu-riscv64", "-one-insn-per-tb", "-d", "cpu,nochain", "-D", log, f"{d}/{name}"],
                       capture_output=True)
    steps = parse_log(log)
    diff = compare(pred, steps, image)
    # A signal from the guest is a negative code. 255 is an exit status.
    faulted = r.returncode < 0
    if diff is None:
        if out == "done":
            if faulted:
                diff = f"model exits, qemu rc {r.returncode}"
            elif r.returncode != a0 % 256:
                diff = f"exit status {r.returncode}, model a0 {a0:#x}"
            elif steps[-1]["x"].get(10) != a0:
                diff = f"a0 at exit {steps[-1]['x'].get(10)}, model {a0:#x}"
            elif cost != len(steps):
                diff = f"cost {cost}, logged {len(steps)}"
        elif out == "abort":
            if not faulted:
                diff = f"model aborts, qemu rc {r.returncode}"
            elif cost != len(steps) - 1:
                diff = f"cost {cost}, logged {len(steps)} with the last not retired"
        else:
            diff = f"model ran out of fuel"
    if kind == "deviates":
        ok = diff is not None
        return ok, f"{'deviates as expected' if ok else 'NO DEVIATION'}: rc {r.returncode}, {diff}", len(steps)
    return diff is None, diff or f"match: {out}, rc {r.returncode}, {len(steps)} steps", len(steps)

# Broken models. Each must fail some case, except the ones named as blind spots.
MUTANTS = [
    ("lui: no sign extension", "wordOfInt (sext 32 (imm * 2 ^ 12))", "wordOfInt (Int.ofNat (imm * 2 ^ 12))", False),
    ("addi: immediate unsigned", ".addi (rdOf w) (rs1Of w) (sext 12 (w / 2 ^ 20))", ".addi (rdOf w) (rs1Of w) (Int.ofNat (w / 2 ^ 20))", False),
    ("add: drops the second operand", "W64.add (m.get a) (m.get b)", "m.get a", False),
    ("ld: offset unsigned", ".ld (rdOf w) (rs1Of w) (sext 12 (w / 2 ^ 20))", ".ld (rdOf w) (rs1Of w) (Int.ofNat (w / 2 ^ 20))", False),
    ("sd: offset unsigned", "sext 12 ((w / 2 ^ 25) * 32 + rdOf w)", "Int.ofNat ((w / 2 ^ 25) * 32 + rdOf w)", False),
    ("beq: offset unsigned", "(sext 13\n        ((w / 2 ^ 31)", "(Int.ofNat\n        ((w / 2 ^ 31)", False),
    ("beq: inverted", "if m.get a = m.get b then", "if m.get a ≠ m.get b then", False),
    # x0 is guarded where it is read and where it is written, so only breaking both changes anything.
    ("x0 unguarded", "if r = 0 then W64.ofNat 0 else m.x r", "if false then W64.ofNat 0 else m.x r", False,
     "if r = 0 then m.x else", "if false then m.x else"),
    ("ld: big-endian", "(m.mem ((a + i) % 2 ^ 64)).val + 256 * acc", "(m.mem ((a + 7 - i) % 2 ^ 64)).val + 256 * acc", False),
    ("sd: big-endian", "byteOf (v.val / 256 ^ i)", "byteOf (v.val / 256 ^ (7 - i))", False),
    ("everything readable", "inCode code a || inData a || e.rd a", "true", False),
    ("code writable", "inData a || (!inCode code a && e.wr a)", "inData a || inCode code a", False),
    ("data misplaced", "data (a - dataBase)", "data (a - dataBase + 8)", False),
    ("exit number wrong", "W64.ofNat 93", "W64.ofNat 94", False),
    ("a fault is counted", "cost := 0, out := .abort", "cost := 1, out := .abort", False),
    ("ld leaks no address", ".next [.addr (Int.ofNat a)] { m with pc := n, x :=", ".next [] { m with pc := n, x :=", False),
    ("sd leaks no address", ".next [.addr (Int.ofNat a)] { m with pc := n, mem :=", ".next [] { m with pc := n, mem :=", False),
    ("ld leaks a wrong address", ".next [.addr (Int.ofNat a)] { m with pc := n, x :=", ".next [.addr (Int.ofNat (a + 8))] { m with pc := n, x :=", False),
    ("a faulting load leaks none", "else .fault [.addr (Int.ofNat a)]\n      | .sd", "else .fault []\n      | .sd", False),
    ("andi: acts as add", "x := m.set rd (W64.and (m.get rs) (wordOfInt imm))", "x := m.set rd (W64.add (m.get rs) (wordOfInt imm))", False),
    ("andi: immediate unsigned", ".andi (rdOf w) (rs1Of w) (sext 12 (w / 2 ^ 20))", ".andi (rdOf w) (rs1Of w) (Int.ofNat (w / 2 ^ 20))", False),
]

def compare_all(d, gen):
    if gen.returncode != 0:
        print(gen.stdout[-3000:], gen.stderr[-1000:])
        return None
    names = sorted(f[:-5] for f in os.listdir(d) if f.endswith(".pred"))
    return [(n, check(n, d)) for n in names]

def mutants(d):
    """Build one file: the model up to its witnesses, mutated, then the cases. So the Lean witnesses do not catch it."""
    rv = open("LCore/Slice/Rv.lean").read()
    cut = rv.index("/-- Read input word 0")
    rv = rv[:cut] + "end LCore.Slice.Rv\n"
    cases = open("test/RvCases.lean").read().replace("import LCore.Slice.Rv\n", "")
    wrong = 0
    for k, (name, old, new, blind, *also) in enumerate(MUTANTS):
        assert rv.count(old) == 1, name
        mutated = rv.replace(old, new)
        if also:
            assert mutated.count(also[0]) == 1, name
            mutated = mutated.replace(also[0], also[1])
        w = f"{d}/mut{k}"
        os.makedirs(w)
        p = f"{w}/Mut.lean"
        open(p, "w").write(mutated + cases)
        res = compare_all(w, run(["lake", "env", "lean", "--run", p, w]))
        if res is None:
            print(f"BUILD {name}")
            wrong += 1
            continue
        fails = [n for n, (ok, _, _) in res if not ok]
        caught = bool(fails)
        good = caught != blind
        wrong += not good
        tag = "blind, as stated" if blind and not caught else ("caught" if caught else "SURVIVED")
        print(f"{'ok  ' if good else 'FAIL'} {name:32} {tag}: {len(fails)} cases {','.join(fails[:3])}")
    print(f"rv-diff mutants: {len(MUTANTS)} broken models, {wrong} wrong")
    return 1 if wrong else 0

def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    if "--mutants" in sys.argv:
        return mutants(d)
    g = run(["lake", "env", "lean", "--run", "test/RvCases.lean", d])
    if g.returncode != 0:
        print(g.stdout[-3000:], g.stderr[-1000:])
        return 2
    names = sorted(f[:-5] for f in os.listdir(d) if f.endswith(".pred"))
    bad = total = 0
    for name in names:
        ok, msg, n = check(name, d)
        total += n
        bad += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {name:24} {msg}")
    print(f"rv-diff: {len(names)} cases, {total} steps compared, {bad} failed")
    return 1 if bad or not names else 0

sys.exit(main())
