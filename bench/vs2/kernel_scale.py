#!/usr/bin/env python3
"""VS-2 step 1: how far does kernel evaluation go, on each of the six kernels?

Each case is one module with one theorem, proved by `decide`, over the slice from VS-1. It is built, exported with its imports, and given
to each kernel the way tools/gate/export-check.sh runs them, except that kernels run one at a time, so the seconds mean something.
A `baseline` case has no theorem, to subtract.

  compile   the compiler's output equals a literal: `code (genP (compile p)) = img`
  run       the machine on a literal reaches its result: `(Rv.run img env0 F (init ...)).ev = [ret]`
  branch-*  variants on the compiled `secretBranch`, to explain why three kernels refuse it (VS-1 step 9)

Writes bench/vs2-kernel.tsv. Usage, from the repo root: python3 bench/vs2/kernel_scale.py <scratch directory>

With --rest: the variants the first run did not reach (it was stopped for low system memory). Writes bench/vs2-kernel-3.tsv. It records the lowest available memory seen in each case,
and stops cleanly below MEM_FLOOR_GB.
"""
import json
import os
import re
import resource
import signal
import subprocess
import sys
import threading
import time

LIMIT = 900
MEM_FLOOR_GB = 3.0
REST = {"baseline", "branch-same-untaken-f4", "branch-same-taken-f4", "branch-cost-taken", "branch-pc-taken",
        "tampered-differs-f12"}

# No child may take the machine. A first version killed only `lake` on timeout, and its `lean` child kept 21 GB for two hours.
MEM_CAP_BYTES = 12 * 2 ** 30

def capped():
    """In the child, before exec: its own process group, so a timeout reaches its children, and a hard memory limit."""
    os.setsid()
    resource.setrlimit(resource.RLIMIT_AS, (MEM_CAP_BYTES, MEM_CAP_BYTES))

def run_capped(cmd, timeout, **kw):
    """Run under the cap. On timeout, kill the whole group and wait for it."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, preexec_fn=capped, **kw)
    try:
        out, err = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        raise
    return subprocess.CompletedProcess(cmd, p.returncode, out, err)

def mem_available_gb():
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) / 1048576
    return 0.0

class MemWatch:
    """The lowest available memory while a case runs."""
    def __init__(self):
        self.low = mem_available_gb()
        self.stop = False
        self.t = threading.Thread(target=self.loop, daemon=True)
        self.t.start()
    def loop(self):
        while not self.stop:
            self.low = min(self.low, mem_available_gb())
            time.sleep(1)
    def done(self):
        self.stop = True
        return self.low
PRELUDE = """import LCore.Slice.Teeth
open LCore LCore.Slice LCore.Slice.Rv LCore.Slice.Slots LCore.Slice.Lower LCore.Slice.Image LCore.Slice.Teeth
set_option maxRecDepth 2000000
"""
CHAIN = """
def chain : Nat → Cmd
  | 0 => .skip
  | n + 1 => .seq (.assign "x" (.add (.var "x") (.var "a"))) (chain n)
def prog (n : Nat) : Prog := { inputs := ["a", "b"], body := chain n, ret := .var "x" }
"""

def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)

def literal(d, n):
    """The compiled bytes and instruction count for a chain of n assignments, evaluated outside the kernel, to be checked by it."""
    p = f"{d}/Lit{n}.lean"
    open(p, "w").write(PRELUDE + CHAIN + f"""
#eval (code (genP (compile (prog {n})))).map (·.val)
#eval (genP (compile (prog {n}))).length
""")
    r = sh(["lake", "env", "lean", p], cwd="l-core")
    nums = re.findall(r"\[([^\]]*)\]\s*(\d+)\s*$", r.stdout, re.S)
    if not nums:
        sys.exit(f"literal {n}: {r.stdout[-400:]} {r.stderr[-400:]}")
    return [int(x) for x in nums[0][0].replace("\n", " ").split(",")], int(nums[0][1])

def cases(d, sizes):
    out = [("baseline", 0, PRELUDE)]
    for n in sizes:
        lit, count = literal(d, n)
        img = f"def img : List Byte := ({lit} : List Nat).map byteOf\n"
        out.append((f"compile-{len(lit)}B", len(lit), PRELUDE + CHAIN + img +
                    f"theorem t : code (genP (compile (prog {n}))) = img := by decide\n"))
        out.append((f"run-{len(lit)}B", len(lit), PRELUDE + img +
                    f"theorem t : (Rv.run img env0 {count + 5} (init img (encBytes (inp 3 1)) env0)).ev = "
                    f"[Rv.retEv (W64.ofNat {3 * n})] := by decide\n"))
    run = lambda a, s: f"((rvLang sec0).run {s} secretBranchImage (encBytes (inp {a} 1), env0))"
    out += [
        ("branch-differs-f4", 44, PRELUDE + f"theorem t : {run(0, 4)}.lk ≠ {run(6, 4)}.lk := by decide\n"),
        ("branch-same-untaken-f4", 44, PRELUDE + f"theorem t : {run(5, 4)}.lk = {run(6, 4)}.lk := by decide\n"),
        ("branch-same-taken-f4", 44, PRELUDE + f"theorem t : {run(0, 4)}.lk = {run(0, 4)}.lk := by decide\n"),
        ("branch-cost-taken", 44, PRELUDE + f"theorem t : {run(0, 40)}.cost = 9 := by decide\n"),
        ("branch-pc-taken", 44, PRELUDE +
         "theorem t : (match Rv.step secretBranchImage env0 (init secretBranchImage (encBytes (inp 0 1)) env0) with\n"
         "  | .next _ m => m.pc | _ => 0) = 65716 := by decide\n"),
        ("tampered-differs-f12", 76, PRELUDE +
         "theorem t : ((rvLang sec0).run 12 tampered (encBytes (inp 0 3), env0)).lk ≠ "
         "((rvLang sec0).run 12 tampered (encBytes (inp 5 3), env0)).lk := by decide\n"),
    ]
    return out

def kernels(exp, tmp, root):
    bin_ = sh(["lake", "env", "printenv", "LEAN_SYSROOT"], cwd=root).stdout.strip() + "/bin"
    cfg = f"{tmp}/nanoda.json"
    json.dump({"export_file_path": exp, "use_stdin": False, "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
               "unpermitted_axiom_hard_error": False, "num_threads": 1, "nat_extension": True, "string_extension": True,
               "print_success_message": True}, open(cfg, "w"))
    return [
        ("lean", [f"{bin_}/leanchecker", "--silent", "--from-export", exp]),
        ("paranoid", [f"{bin_}/leanchecker-paranoid", "--silent", "--from-export", exp]),
        ("lean4lean", [f"{bin_}/lean4lean", "--import", exp]),
        ("nanoda", ["bash", "-c", 'ulimit -s unlimited && exec "$0" "$1"', f"{bin_}/nanoda_bin", cfg]),
        ("con-leche", [f"{bin_}/con-leche", exp]),
        ("con-ron", [f"{bin_}/con-ron", exp]),
    ]

def main():
    d = os.path.abspath(sys.argv[1])
    os.makedirs(d, exist_ok=True)
    root = os.getcwd()
    rest = "--rest" in sys.argv
    out_tsv = "bench/vs2-kernel-3.tsv" if rest else "bench/vs2-kernel.tsv"
    rows = ["case\tbytes\telaborate_s\telaborate\tkernel\tseconds\tverdict\tdetail\tlowest_mem_gb"]
    for name, size, src in cases(d, [] if rest else [4, 47, 475]):
        if rest and name not in REST:
            continue
        if rest and name.startswith("run-"):
            src = src.replace("by decide", "by decide +kernel")
        if mem_available_gb() < MEM_FLOOR_GB:
            print(f"kernel-scale: stopped before {name}: {mem_available_gb():.1f} GB available")
            break
        watch = MemWatch()
        mod = "K" + re.sub(r"\W", "_", name)
        path = f"{d}/{mod}.lean"
        open(path, "w").write(src)
        env = dict(os.environ)
        lp = sh(["lake", "env", "printenv", "LEAN_PATH"], cwd="l-core").stdout.strip()
        env["LEAN_PATH"] = f"{d}:{lp}"
        t0 = time.time()
        try:
            b = run_capped(["lake", "env", "lean", f"--root={d}", "-o", f"{d}/{mod}.olean", path], LIMIT, cwd="l-core")
            ok = b.returncode == 0
            msg = "" if ok else re.sub(r"\s+", " ", (b.stdout + b.stderr))[-140:]
        except subprocess.TimeoutExpired:
            ok, msg = False, f"timeout {LIMIT} s"
        el = time.time() - t0
        print(f"{name}: elaborated {ok} in {el:.1f} s {msg}", flush=True)
        if not ok:
            if name == "baseline":
                print("kernel-scale: the baseline does not build, so nothing here is a measurement")
                return 2
            rows.append(f"{name}\t{size}\t{el:.1f}\tfail\t-\t-\t-\t{msg}")
            continue
        exp = f"{d}/{mod}.ndjson"
        with open(exp, "w") as f:
            sysroot = sh(["lake", "env", "printenv", "LEAN_SYSROOT"], cwd=root).stdout.strip()
            x = subprocess.run([f"{sysroot}/bin/leanexport", mod], stdout=f, stderr=subprocess.PIPE, text=True, env=env)
        if x.returncode != 0:
            rows.append(f"{name}\t{size}\t{el:.1f}\tok\t-\t-\texport-failed\t{x.stderr[-120:]}")
            continue
        for kname, cmd in kernels(exp, d, root):
            t1 = time.time()
            try:
                r = run_capped(cmd, LIMIT, cwd=d)
                verdict = "accepts" if r.returncode == 0 else "REJECTS"
                tail = (r.stdout + r.stderr).strip().splitlines()
                detail = "" if r.returncode == 0 else (tail[-1][:110] if tail else f"exit {r.returncode}")
            except subprocess.TimeoutExpired:
                verdict, detail = "TIMEOUT", f"over {LIMIT} s"
            s = time.time() - t1
            rows.append(f"{name}\t{size}\t{el:.1f}\tok\t{kname}\t{s:.1f}\t{verdict}\t{detail}\t{watch.low:.1f}")
            print(f"  {kname}: {verdict} {s:.1f} s, lowest {watch.low:.1f} GB available {detail[:80]}", flush=True)
            if watch.low < MEM_FLOOR_GB:
                break
        watch.done()
        os.remove(exp)
        open(out_tsv, "w").write("\n".join(rows) + "\n")
        if watch.low < MEM_FLOOR_GB:
            print(f"kernel-scale: stopped after {name}: {watch.low:.1f} GB available")
            break
    open(out_tsv, "w").write("\n".join(rows) + "\n")
    return 0

sys.exit(main())
