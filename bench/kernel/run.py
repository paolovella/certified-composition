#!/usr/bin/env python3
"""S-KERNEL driver: probe, generate, time, write bench/kernel.tsv.

usage: python3 bench/kernel/run.py OUTDIR [--only REGEX]     (run from the repo root)

Times are wall-clock seconds of `lake env lean FILE` from conf-typing/, minus the median of
three runs of an import-only baseline. A file that fails to check is recorded as FAIL with
its first error line, never dropped. Every theorem must print exactly the axioms it uses;
the set is recorded, and anything outside the standard three is a failure.
The elaborator mode (`decide`) gets 120 s, the kernel mode 1800 s.
"""
import json
import os
import re
import statistics
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen  # noqa: E402

LEAN = ["lake", "env", "lean"]
CWD = "conf-typing"
STD = {"propext", "Classical.choice", "Quot.sound"}


def run(fn, timeout=1800):
    t0 = time.monotonic()
    try:
        p = subprocess.run(LEAN + [os.path.abspath(fn)], cwd=CWD, capture_output=True,
                           text=True, timeout=timeout)
        out, rc = p.stdout + p.stderr, p.returncode
    except subprocess.TimeoutExpired:
        out, rc = "TIMEOUT", -1
    return time.monotonic() - t0, rc, out


def probe_term(outdir, name, src, task, term):
    """RHS for a term task with no string twin: one untrusted #eval over the same term."""
    expr, ty = gen.TASKS[task]
    fn = os.path.join(outdir, f"{name}__{task}__probe.lean")
    with open(fn, "w") as f:
        f.write(gen.HEAD + gen.SKETCH + f"\ndef src : String := {gen.lean_str(src)}\n"
                f"def prog : UCmd := {term}\n#eval IO.println (\"RHS\\t\" ++ reprStr ({expr} : {ty}))\nend Bench\n")
    _, rc, out = run(fn)
    m = re.search(r"^RHS\t(.*)$", out, re.M)
    if not m:
        sys.exit(f"term probe failed for {name} {task}:\n{out[:2000]}")
    return m.group(1)


def main():
    outdir = sys.argv[1]
    only = re.compile(sys.argv[sys.argv.index("--only") + 1]) if "--only" in sys.argv else None
    os.makedirs(outdir, exist_ok=True)
    cs = gen.cases()
    gen.probe(outdir, cs)
    _, rc, out = run(os.path.join(outdir, "probe.lean"))
    if rc != 0:
        print(out)
        sys.exit("probe failed")
    rhs = {}
    for line in out.splitlines():
        if line.startswith("PROBE\t"):
            _, name, *vals = line.split("\t")
            rhs[name] = vals
    b = gen.baseline(outdir)
    base = statistics.median(run(b)[0] for _ in range(3))
    print(f"baseline {base:.2f}s", flush=True)
    rows = []
    for name, src, tasks in cs:
        nodes, term, *strvals = rhs[name]
        nodes = nodes.removeprefix("some ")
        strtasks = [t for t in tasks if t not in gen.TERM_TASKS]
        for task in tasks:
            if task in gen.TERM_TASKS:
                if term == "none":
                    continue                      # did not parse: no term to start from
                # the term RHS is not probed: it is the string task's value (same program)
                r = {"elabT": nodes,
                     "bcheckT": strvals[strtasks.index("bcheck")] if "bcheck" in strtasks else None,
                     "compileT": None}[task]
            else:
                r = strvals[strtasks.index(task)]
            for mode in ("decide", "kernel"):
                if only and not only.search(f"{name}__{task}__{mode}"):
                    continue
                rr = r if r is not None else probe_term(outdir, name, src, task, term)
                fn = gen.emit(outdir, name, src, task, mode, rr, term if task in gen.TERM_TASKS else None)
                dt, rc, out = run(fn, timeout=120 if mode == "decide" else 1800)
                ax = re.search(r"'Bench\.t' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", out)
                if rc == 0 and ax:
                    used = set(a.strip() for a in (ax.group(1) or "").split(",") if a.strip())
                    # the definitions themselves carry these (tools/axioms.expected); decide
                    # must add nothing beyond the standard three
                    verdict = "ok" if used <= STD else "AXIOMS " + ",".join(sorted(used))
                    verdict += " [" + ",".join(sorted(used)) + "]"
                elif out == "TIMEOUT":
                    verdict = "TIMEOUT"
                else:
                    err = next((l for l in out.splitlines() if "error" in l), out.strip()[:120])
                    verdict = "FAIL " + err.replace("\t", " ")[:160]
                rows.append((name, nodes, task, mode, rr, f"{max(0.0, dt - base):.2f}", verdict))
                print("\t".join(rows[-1]), flush=True)
    with open(os.path.join(outdir, "kernel.tsv"), "w") as f:
        f.write(f"# baseline_s\t{base:.2f}\n")
        f.write("case\tnodes\ttask\tmode\trhs\tseconds\tverdict\n")
        for r in rows:
            f.write("\t".join(r) + "\n")


if __name__ == "__main__":
    main()
