#!/usr/bin/env python3
"""Mechanical rule mutants for the Lean checkers (P0-05).

Every checker the witness registry finds (tools/witnesses.expected) is mutated one site at a
time by fixed operators, never by a model:

  refuse->accept   a `none` result becomes `some default`; a `false` verdict becomes `true`
  accept->refuse   a `some x` result becomes `none` (as `Option.filter (fun _ => false) <| some x`,
                   which takes its type from context); a `true` verdict becomes `false`

A site is a result position in the checker's own definition: right after `=>`, `then` or
`else`. Each mutant is built in a copy of conf-typing:
  killed      the build fails outside the mutated definition (a proof noticed)
  stillborn   the mutated definition itself does not elaborate (no `Inhabited`, say)
  survived    everything builds: no theorem constrains that rule
Survivors are the output. The operators are deliberately few and dumb; a 100% kill rate over
several cycles means they are too weak (PLAN-2026-10 §8), not that the checkers are perfect.

  tools/mutants.py --list            print the sites
  tools/mutants.py [--jobs N] [--only NAME,...]   build every mutant, print one row each and a
                                                  summary line
  tools/mutants.py --write    also rewrite tools/mutants.expected (site, operator, verdict)
  tools/mutants.py --check    fail on any survivor, or if tools/mutants.expected is stale: a
                              site that changes verdict, appears or disappears is a reviewed diff
"""
import argparse, os, re, shutil, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

# the repo is the script's parent's parent, as for tools/ci.sh: copies without .git work too
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CT = os.path.join(ROOT, "conf-typing")

def checkers():
    rows = open(os.path.join(ROOT, "tools/witnesses.expected")).read().splitlines()
    return [r.split("\t")[0].removeprefix("ConfTyping.") for r in rows if "\t" in r]

TOP = re.compile(r"^(?:@\[|/--|theorem |lemma |def |abbrev |instance |inductive |structure |"
                 r"end |namespace |section |open |example |private |noncomputable |#|"
                 r"termination_by|decreasing_by|attribute )")

def definition(name):
    """(file, first line, last line) of `def name`, 0-based, end exclusive."""
    pat = re.compile(rf"^(?:private |noncomputable )*def {re.escape(name)}(?:\s|$)")
    for dirpath, _, files in os.walk(os.path.join(CT, "ConfTyping")):
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            path = os.path.join(dirpath, f)
            lines = open(path, encoding="utf-8").read().split("\n")
            for i, l in enumerate(lines):
                if pat.match(l):
                    j = i + 1
                    while j < len(lines) and not TOP.match(lines[j]):
                        j += 1
                    return path, i, j
    return None

# a result position: after `=>`, `then` or `else`, before the result
SITE = re.compile(r"(=>|\bthen\b|\belse\b)(\s+)(none\b|some\b|true\b|false\b)")

def sites():
    out = []
    for c in checkers():
        d = definition(c)
        if d is None:
            print(f"mutants: definition of {c} not found", file=sys.stderr)
            sys.exit(2)
        path, a, b = d
        lines = open(path, encoding="utf-8").read().split("\n")
        for ln in range(a, b):
            if lines[ln].lstrip().startswith("--"):
                continue
            for m in SITE.finditer(lines[ln]):
                out.append((c, path, a, b, ln, m.start(3), m.group(3)))
    return out

REPL = {"none": "some default", "false": "true",
        "some": "Option.filter (fun _ => false) <| some", "true": "false"}
OP = {"none": "refuse->accept", "false": "refuse->accept",
      "some": "accept->refuse", "true": "accept->refuse"}

def mutate(text_lines, ln, col, tok):
    l = text_lines[ln]
    return text_lines[:ln] + [l[:col] + REPL[tok] + l[col + len(tok):]] + text_lines[ln + 1:]

def run(site, base):
    c, path, a, b, ln, col, tok = site
    work = tempfile.mkdtemp(prefix="mutant-", dir=base)
    try:
        shutil.copytree(CT, os.path.join(work, "conf-typing"), symlinks=True)
        shutil.copytree(os.path.join(ROOT, "transport-calculus"),
                        os.path.join(work, "transport-calculus"), symlinks=True)
        shutil.copytree(os.path.join(ROOT, "l-core"), os.path.join(work, "l-core"), symlinks=True)
        rel = os.path.relpath(path, CT)
        mp = os.path.join(work, "conf-typing", rel)
        lines = open(mp, encoding="utf-8").read().split("\n")
        open(mp, "w", encoding="utf-8").write("\n".join(mutate(lines, ln, col, tok)))
        r = subprocess.run(["lake", "build"], cwd=os.path.join(work, "conf-typing"),
                           capture_output=True, text=True)
        if r.returncode == 0:
            return "survived", ""
        errs = re.findall(r"error: ([^\s:]+\.lean):(\d+):\d+", r.stdout + r.stderr)
        if not errs:
            tail = (r.stdout + r.stderr).strip().splitlines()
            return "unexplained", tail[-1] if tail else "no output"
        first_file, first_line = errs[0][0], int(errs[0][1]) - 1
        inside = os.path.normpath(first_file).endswith(os.path.normpath(rel)) and a <= first_line < b
        return ("stillborn" if inside else "killed"), f"{first_file}:{first_line + 1}"
    finally:
        shutil.rmtree(work, ignore_errors=True)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--only", default="")
    ap.add_argument("--write", action="store_true", help="rewrite tools/mutants.expected")
    ap.add_argument("--sites-check", action="store_true",
                    help="no builds: fail unless tools/mutants.expected lists exactly today's sites")
    ap.add_argument("--check", action="store_true",
                    help="fail unless every mutant is killed and tools/mutants.expected is current")
    a = ap.parse_args()
    ss = sites()
    if a.only:
        keep = set(a.only.split(","))
        ss = [s for s in ss if s[0] in keep]
    if a.sites_check:
        exp = os.path.join(ROOT, "tools/mutants.expected")
        old = [l.rsplit("\t", 1)[0] for l in open(exp).read().splitlines() if l.count("\t") == 3]
        now = [f"{c}\t{os.path.relpath(path, ROOT)}:{ln + 1}:{col + 1}\t{OP[tok]}"
               for c, path, _, _, ln, col, tok in ss]
        if old != now:
            print("mutants: the checkers changed since tools/mutants.expected was written; "
                  "run tools/mutants.py --write")
            for l in sorted(set(old) - set(now))[:10]: print("  - " + l)
            for l in sorted(set(now) - set(old))[:10]: print("  + " + l)
            sys.exit(1)
        print(f"mutants: tools/mutants.expected covers all {len(now)} sites")
        return
    if a.list:
        for c, path, _, _, ln, col, tok in ss:
            print(f"{c}\t{os.path.relpath(path, ROOT)}:{ln + 1}:{col + 1}\t{OP[tok]}\t{tok}")
        print(f"mutants: {len(ss)} sites in {len({s[0] for s in ss})} checkers")
        return
    base = tempfile.mkdtemp(prefix="mutants-")
    # The accepted witness: the unmutated copy must build, or every "killed" below means nothing.
    work = tempfile.mkdtemp(prefix="pristine-", dir=base)
    shutil.copytree(CT, os.path.join(work, "conf-typing"), symlinks=True)
    shutil.copytree(os.path.join(ROOT, "transport-calculus"), os.path.join(work, "transport-calculus"),
                    symlinks=True)
    shutil.copytree(os.path.join(ROOT, "l-core"), os.path.join(work, "l-core"), symlinks=True)
    if subprocess.run(["lake", "build"], cwd=os.path.join(work, "conf-typing"),
                      capture_output=True).returncode != 0:
        print("mutants: the unmutated copy does not build; no verdict")
        shutil.rmtree(base, ignore_errors=True)
        sys.exit(2)
    shutil.rmtree(work, ignore_errors=True)
    try:
        with ThreadPoolExecutor(max_workers=a.jobs) as ex:
            results = list(ex.map(lambda s: run(s, base), ss))
    finally:
        shutil.rmtree(base, ignore_errors=True)
    count = {"killed": 0, "stillborn": 0, "survived": 0, "unexplained": 0}
    table = []
    for (c, path, _, _, ln, col, tok), (verdict, where) in zip(ss, results):
        count[verdict] += 1
        site = f"{c}\t{os.path.relpath(path, ROOT)}:{ln + 1}:{col + 1}\t{OP[tok]}"
        table.append(f"{site}\t{verdict}")
        print(f"{site}\t{verdict}\t{where}")
    summary = (f"mutants: {len(ss)} built, {count['killed']} killed, {count['stillborn']} stillborn, "
               f"{count['survived']} survived, {count['unexplained']} unexplained")
    print(summary)
    # The committed table: where the kill happened is left out, it moves with every edit.
    table.append(summary)
    expected = os.path.join(ROOT, "tools/mutants.expected")
    if a.write:
        open(expected, "w").write("\n".join(table) + "\n")
        print("mutants: wrote tools/mutants.expected")
    bad = count["survived"] or count["unexplained"]
    if a.check:
        old = open(expected).read().splitlines() if os.path.exists(expected) else []
        if old != table:
            gone = sorted(set(old) - set(table))[:10]
            new = sorted(set(table) - set(old))[:10]
            print("mutants: tools/mutants.expected is stale; run tools/mutants.py --write")
            for l in gone: print("  - " + l)
            for l in new: print("  + " + l)
            bad = True
    sys.exit(1 if bad else 0)

if __name__ == "__main__":
    main()
