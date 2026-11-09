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
    # CAP-01: code may run past the ELF's first page, so the bound is the file, not 0x1000; a pc is only ever in the code
    off = pc - 0x100b0 + 176
    return int.from_bytes(image[off:off + 4], "little") if 176 <= off and off + 4 <= len(image) else 0

def compare(pred, steps, image):
    """The first difference between the model's steps and QEMU's, or None."""
    if len(pred) != len(steps):
        return f"{len(pred)} predicted steps, {len(steps)} logged"
    for i, (p, s) in enumerate(zip(pred, steps)):
        if p[0] != s["pc"]:
            return f"step {i}: pc model {p[0]:#x}, qemu {s['pc']:#x}"
        word = word_at(image, s["pc"])
        if word == 0x73 and s["x"].get(17) == 64:
            # RC-02: write(1, buf, len) reads buf .. buf + len - 1; QEMU's registers say which
            n = s["x"].get(12, 0)
            want, wantc = (s["x"].get(11, 0) if n else None), n
        else:
            want = access(word, s["x"])
            wantc = 0 if want is None else 1
        if p[32] != want or p[33] != wantc:
            return f"step {i}: address model {p[32]} x{p[33]}, qemu {want} x{wantc}"
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
    # RC-02: the bytes written to stdout must be the model's emitted bytes
    want_out = open(f"{d}/{name}.stdout", "rb").read() if os.path.exists(f"{d}/{name}.stdout") else b""
    if diff is None and out == "done" and r.stdout != want_out:
        diff = f"stdout {r.stdout!r}, model {want_out!r}"
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
        # Every stated deviation is the model aborting where Linux carries on (Rv.lean's header and sysWriteStep), so a
        # model that runs on, or deviates some other way, is not the stated deviation (RC-02).
        ok = diff is not None and out == "abort"
        return ok, f"{'deviates as expected' if ok else 'NOT THE STATED DEVIATION'}: model {out}, rc {r.returncode}, {diff}", len(steps)
    return diff is None, diff or f"match: {out}, rc {r.returncode}, {len(steps)} steps", len(steps)

# Broken models. Each must fail some case, except the ones named as blind spots.
MUTANTS = [
    ("lui: no sign extension", "wordOfInt (sext 32 (imm * 2 ^ 12))", "wordOfInt (Int.ofNat (imm * 2 ^ 12))", False),
    ("addi: immediate unsigned", ".addi (rdOf w) (rs1Of w) (sext 12 (w / 2 ^ 20))", ".addi (rdOf w) (rs1Of w) (Int.ofNat (w / 2 ^ 20))", False),
    ("add: drops the second operand", "W64.add (m.get a) (m.get b)", "m.get a", False),
    ("ld: offset unsigned", ".ld (rdOf w) (rs1Of w) (sext 12 (w / 2 ^ 20))", ".ld (rdOf w) (rs1Of w) (Int.ofNat (w / 2 ^ 20))", False),
    ("sd: offset unsigned", "some (.sd (rs2Of w) (rs1Of w) (sext 12 ((w / 2 ^ 25) * 32 + rdOf w)))", "some (.sd (rs2Of w) (rs1Of w) (Int.ofNat ((w / 2 ^ 25) * 32 + rdOf w)))", False),
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
    ("ld leaks no address", ".next [.addr (Int.ofNat a)] { m with pc := n, x := m.set rd (load8 m a) }", ".next [] { m with pc := n, x := m.set rd (load8 m a) }", False),
    ("sd leaks no address", ".next [.addr (Int.ofNat a)] { m with pc := n, mem := store8", ".next [] { m with pc := n, mem := store8", False),
    ("ld leaks a wrong address", ".next [.addr (Int.ofNat a)] { m with pc := n, x := m.set rd (load8 m a) }", ".next [.addr (Int.ofNat (a + 8))] { m with pc := n, x := m.set rd (load8 m a) }", False),
    ("a faulting load leaks none", "else .fault [.addr (Int.ofNat a)]\n      | .lbu", "else .fault []\n      | .lbu", False),
    ("a faulting lbu leaks none", "else .fault [.addr (Int.ofNat a)]\n      | .sb", "else .fault []\n      | .sb", False),
    ("a faulting sb leaks none", "else .fault [.addr (Int.ofNat a)]\n      | .sd", "else .fault []\n      | .sd", False),
    ("a faulting sd leaks none", "else .fault [.addr (Int.ofNat a)]\n      | .beq", "else .fault []\n      | .beq", False),
    ("andi: acts as add", "x := m.set rd (W64.and (m.get rs) (wordOfInt imm))", "x := m.set rd (W64.add (m.get rs) (wordOfInt imm))", False),
    ("andi: immediate unsigned", ".andi (rdOf w) (rs1Of w) (sext 12 (w / 2 ^ 20))", ".andi (rdOf w) (rs1Of w) (Int.ofNat (w / 2 ^ 20))", False),
    # RC-01 step 2a: the five instructions crypto_verify_16 needs.
    ("sub: acts as add", "x := m.set rd (W64.sub (m.get a) (m.get b))", "x := m.set rd (W64.add (m.get a) (m.get b))", False),
    ("sub: operands swapped", "x := m.set rd (W64.sub (m.get a) (m.get b))", "x := m.set rd (W64.sub (m.get b) (m.get a))", False),
    ("xor: acts as or", "x := m.set rd (W64.xor (m.get a) (m.get b))", "x := m.set rd (W64.or (m.get a) (m.get b))", False),
    ("or: acts as xor", "x := m.set rd (W64.or (m.get a) (m.get b))", "x := m.set rd (W64.xor (m.get a) (m.get b))", False),
    ("and: acts as or", "| .and rd a b => .next [] { m with pc := n, x := m.set rd (W64.and (m.get a) (m.get b)) }", "| .and rd a b => .next [] { m with pc := n, x := m.set rd (W64.or (m.get a) (m.get b)) }", False),
    ("srli: shamt 5 bits", "some (.srli (rdOf w) (rs1Of w) (w / 2 ^ 20 % 64))", "some (.srli (rdOf w) (rs1Of w) (w / 2 ^ 20 % 32))", False),
    ("srli: arithmetic", "x := m.set rd (W64.shr (m.get a) k)", "x := m.set rd (if (m.get a).val ≥ 2 ^ 63 then W64.ofNat ((m.get a).val >>> k + (2 ^ 64 - 2 ^ (64 - k))) else W64.shr (m.get a) k)", False),
    ("lbu: sign-extends", "x := m.set rd (W64.ofNat (m.mem a).val) }", "x := m.set rd (if (m.mem a).val ≥ 128 then W64.ofNat ((m.mem a).val + (2 ^ 64 - 256)) else W64.ofNat (m.mem a).val) }", False),
    ("lbu: the next byte", "x := m.set rd (W64.ofNat (m.mem a).val) }", "x := m.set rd (W64.ofNat (m.mem (a + 1)).val) }", False),
    ("lbu: offset unsigned", "some (.lbu (rdOf w) (rs1Of w) (sext 12 (w / 2 ^ 20)))", "some (.lbu (rdOf w) (rs1Of w) (Int.ofNat (w / 2 ^ 20)))", False),
    ("lbu leaks no address", ".next [.addr (Int.ofNat a)] { m with pc := n, x := m.set rd (W64.ofNat (m.mem a).val) }", ".next [] { m with pc := n, x := m.set rd (W64.ofNat (m.mem a).val) }", False),
    ("xor and or decoded swapped", "else if f3Of w = 4 ∧ w / 2 ^ 25 = 0 then some (.xor", "else if f3Of w = 6 ∧ w / 2 ^ 25 = 0 then some (.xor", False,
     "else if f3Of w = 6 ∧ w / 2 ^ 25 = 0 then some (.or", "else if f3Of w = 4 ∧ w / 2 ^ 25 = 0 then some (.or"),
    # RC-02 step 2: sb, and write(1, buf, len) as an emitted event.
    ("sb: stores the second byte", "byteOf (m.get rv).val else m.mem b", "byteOf ((m.get rv).val / 256) else m.mem b", False),
    ("sb: stores at the next address", "mem := fun b => if b = a then", "mem := fun b => if b = a + 1 then", False),
    ("sb: offset unsigned", "some (.sb (rs2Of w) (rs1Of w) (sext 12 ((w / 2 ^ 25) * 32 + rdOf w)))", "some (.sb (rs2Of w) (rs1Of w) (Int.ofNat ((w / 2 ^ 25) * 32 + rdOf w)))", False),
    ("sb leaks no address", ".next [.addr (Int.ofNat a)] { m with pc := n, mem := fun b", ".next [] { m with pc := n, mem := fun b", False),
    ("sb: decoded as sd", "else if f3Of w = 0 then some (.sb", "else if f3Of w = 0 then some (.sd", False),
    ("write: one byte short", "let as := (List.range len).map", "let as := (List.range (len - 1)).map", False),
    ("write: bytes reversed", "(.emit \"out\" (as.map fun b => (m.mem b).val))", "(.emit \"out\" (as.reverse.map fun b => (m.mem b).val))", False),
    ("write leaks no address", "(as.map fun b => .addr (Int.ofNat b))", "[]", False),
    ("write returns 0", "x := m.set 10 (m.get 12) }", "x := m.set 10 (W64.ofNat 0) }", False),
    ("write number wrong", "def sysWrite : W64 := W64.ofNat 64", "def sysWrite : W64 := W64.ofNat 63", False),
    ("write to any descriptor", "if m.get 10 = W64.ofNat 1 ∧ len", "if True ∧ len", False),
    # CAP-01 part 4a: jal
    ("jal links nothing", "x := m.set rd (W64.ofNat (m.pc + 4)) }", "x := m.x }", False),
    ("jal links pc, not pc + 4", "x := m.set rd (W64.ofNat (m.pc + 4)) }", "x := m.set rd (W64.ofNat m.pc) }", False),
    ("jal: offset unsigned", "some (.jal (rdOf w) (sext 21", "some (.jal (rdOf w) (Int.ofNat", False),
    ("jal: imm bit 11 misplaced", "+ (w / 2 ^ 20 % 2) * 2 ^ 11 +", "+ (w / 2 ^ 20 % 2) * 2 ^ 12 +", False),
    # W32-01 part 1: slli and sll
    ("slli: shifts right", "x := m.set rd (W64.shl (m.get a) k) }", "x := m.set rd (W64.shr (m.get a) k) }", False),
    ("slli: one short", "x := m.set rd (W64.shl (m.get a) k) }", "x := m.set rd (W64.shl (m.get a) (k - 1)) }", False),
    ("slli: shamt 5 bits", "some (.slli (rdOf w) (rs1Of w) (w / 2 ^ 20 % 64))", "some (.slli (rdOf w) (rs1Of w) (w / 2 ^ 20 % 32))", False),
    # Not masked at all, the model shifts by 2^64 - 1 at sll_amounts' last step, and Lean panics: a mask too wide is the runnable form
    ("sll: amount masked to 7 bits", "(W64.shl (m.get a) ((m.get b).val % 64))", "(W64.shl (m.get a) ((m.get b).val % 128))", False),
    ("sll: amount masked to 5 bits", "(W64.shl (m.get a) ((m.get b).val % 64))", "(W64.shl (m.get a) ((m.get b).val % 32))", False),
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
