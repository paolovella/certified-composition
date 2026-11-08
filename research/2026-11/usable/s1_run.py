#!/usr/bin/env python3
"""S-USABLE S1 driver: for each shape:size, print the image, write the kernel file, run it under the profiler, and
append one row per theorem to a tsv: shape, size, source nodes, image bytes, theorem, kernel ms, elaboration ms, status.

Each Lean run is capped: `timeout` with a kill after, in its own process group, and `prlimit` on address space is
not used because Lean reserves large virtual ranges; peak RSS is read from /usr/bin/time instead.

Usage, from l-core/: python3 ../research/2026-11/usable/s1_run.py SCRATCH OUT.tsv TIMEOUT shape:size ...
"""
import os
import re
import signal
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import s1_gen  # noqa: E402

THMS = ["ok", "okP", "ct", "lit", "pipe", "bytes", "counted"]


def run_lean(path, timeout):
    cmd = ["/usr/bin/time", "-f", "MAXRSS %M", "lake", "env", "lean", "-D", "autoImplicit=false", str(path)]
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        out, _ = p.communicate(timeout=timeout)
        return out, p.returncode
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        out, _ = p.communicate()
        return out + "\nTIMEOUT", -9


PARTIAL = """
def L : List Byte := ([{nats}] : List Nat).map byteOf

#eval IO.println "== okP"
set_option profiler true in
theorem t_okP : okP (compile P) = true := by decide
#eval IO.println "== ct"
set_option profiler true in
theorem t_ct : CT.ctCheck S P = true := by decide
#eval IO.println "== lit"
set_option profiler true in
theorem t_lit : code (genP (compile P)) = L := by decide
"""


def kernel_file(scratch, name, shape, lit, partial=False):
    prog = (scratch / f"{name}_prog.lean").read_text()
    nats = ", ".join(str(b) for b in lit)
    if partial:
        body = PARTIAL.replace("{nats}", nats)
        if shape in ("loop", "verify"):
            body += """#eval IO.println "== counted"
set_option profiler true in
theorem t_counted : Budget.counted P = true := by decide
"""
        body += '#eval IO.println "== end"\n'
        path = scratch / f"{name}_kernel.lean"
        path.write_text(prog + body)
        return path
    body = f"""
def L : List Byte := ([{nats}] : List Nat).map byteOf

#eval IO.println "== ok"
set_option profiler true in
theorem t_ok : fits P = true ∧ okP (compile P) = true := by decide
#eval IO.println "== ct"
set_option profiler true in
theorem t_ct : CT.ctCheck S P = true := by decide
#eval IO.println "== lit"
set_option profiler true in
theorem t_lit : code (genP (compile P)) = L := by decide
#eval IO.println "== pipe"
set_option profiler true in
theorem t_pipe : (pipeline S).comp P = .ok (L, Xform.id.then (xf (compile P))) := by
  rw [← t_lit]; exact OnMachine.pipeline_comp S t_ok.1 t_ok.2
#eval IO.println "== bytes"
set_option profiler true in
theorem t_bytes : Cert.relView (rvLang S) (rvLang S).lowIn CT.noRet L :=
  (pipeline S).relView_transfer t_pipe (pipeline S).low_cover (CT.ctCheck_relView t_ct)
"""
    if shape in ("loop", "verify"):
        body += """#eval IO.println "== counted"
set_option profiler true in
theorem t_counted : Budget.counted P = true := by decide
"""
    body += '#eval IO.println "== end"\n'
    path = scratch / f"{name}_kernel.lean"
    path.write_text(prog + body)
    return path


def parse(out):
    """Kernel ms = 'type checking' lines; elaboration ms = tactic/elaboration lines; per '== name' section."""
    res, cur = {}, None
    for line in out.splitlines():
        m = re.match(r"== (\w+)", line.strip())
        if m:
            cur = m.group(1)
            res.setdefault(cur, {"kernel": 0.0, "elab": 0.0, "err": ""})
            continue
        if cur is None:
            continue
        m = re.search(r"(type checking|tactic execution of [\w.]+|elaboration|simp) took ([\d.]+)(ms|s)", line)
        if m:
            v = float(m.group(2)) * (1000 if m.group(3) == "s" else 1)
            res[cur]["kernel" if m.group(1) == "type checking" else "elab"] += v
        if "error" in line and not res[cur]["err"]:
            res[cur]["err"] = line.strip()[:120]
    return res


def main():
    scratch, tsv, timeout = Path(sys.argv[1]), Path(sys.argv[2]), int(sys.argv[3])
    specs = sys.argv[4:]
    s1_gen.sys.argv = ["s1_gen", str(scratch)] + specs
    s1_gen.main()
    new = not tsv.exists()
    with tsv.open("a") as f:
        if new:
            f.write("shape\tsize\timage_bytes\ttheorem\tkernel_ms\telab_ms\tstatus\tmaxrss_kb\n")
        for spec in specs:
            shape, size = spec.split(":")
            name = f"{shape}{size}"
            out, rc = run_lean(scratch / f"{name}_bytes.lean", timeout)
            lines = [l for l in out.splitlines() if l.startswith("[")]
            okl = [l for l in out.splitlines() if l.startswith("ok ")]
            if not lines or not okl:
                f.write(f"{shape}\t{size}\t-\tbytes\t-\t-\tno image: {out.strip()[-120:]}\t-\n")
                f.flush()
                continue
            partial = "ok true ct true" not in okl[0]
            if partial:
                # refused by fits or okP: record it, and time the parts that do not need it
                f.write(f"{shape}\t{size}\t-\tpipeline\t-\t-\trefused: {okl[0]}\t-\n")
            lit = [int(x) for x in lines[0].strip("[]").split(",") if x.strip()]
            path = kernel_file(scratch, name, shape, lit, partial)
            out, rc = run_lean(path, timeout)
            (scratch / f"{name}_kernel.out").write_text(out)
            rss = (re.findall(r"MAXRSS (\d+)", out) or ["-"])[-1]
            res = parse(out)
            for t in THMS:
                if t not in res:
                    if (t == "counted" and shape == "line") or (partial and t in ("ok", "pipe", "bytes")) \
                            or (not partial and t == "okP"):
                        continue
                    status = "timeout" if "TIMEOUT" in out else "not reached"
                    f.write(f"{shape}\t{size}\t{len(lit)}\t{t}\t-\t-\t{status}\t{rss}\n")
                    continue
                r = res[t]
                status = "error: " + r["err"] if r["err"] else "ok"
                f.write(f"{shape}\t{size}\t{len(lit)}\t{t}\t{r['kernel']:.0f}\t{r['elab']:.0f}\t{status}\t{rss}\n")
            f.flush()
            print(name, len(lit), "bytes", {t: round(res[t]["kernel"]) for t in res if t in THMS}, "rss", rss)


if __name__ == "__main__":
    main()
