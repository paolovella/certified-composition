"""Write bench/s435.tsv from the S-435 receipts and manifests. Run from the repo root: python3 s435tsv.py S"""
import collections
import glob
import re
import sys

S = sys.argv[1]


def load(p):
    d = {}
    for line in open(p):
        n, m, a = line.rstrip("\n").split("\t")
        d[n] = (m, frozenset(x for x in a.split(",") if x))
    return d


old = load("tools/axioms.expected")
A = load(S + "/axA.txt")
B = load(S + "/axB.txt")
grewA = collections.Counter(old[k][0] for k in old if k in A and A[k][1] != old[k][1])
grewB = collections.Counter(old[k][0] for k in old if k in B and B[k][1] != old[k][1])
gone = collections.Counter(old[k][0] for k in old if k not in A)

err = collections.Counter()
for line in open("tools/receipts/s435b-ct1.log"):
    m = re.match(r"^error: (\S+?)\.lean:\d+", line)
    if m:
        err[m.group(1).replace("/", ".")] += 1

w = collections.defaultdict(collections.Counter)
for f in ("tools/receipts/s435b-ctA.log", "tools/receipts/s435b-tc.log"):
    for line in open(f):
        m = re.match(r"^warning: (\S+?)\.lean:\d+:\d+: (.*)", line)
        if not m:
            continue
        mod, msg = m.group(1).replace("/", "."), m.group(2)
        d = re.match(r"`([^`]+)` has been deprecated", msg)
        if d:
            k = "deprecated:" + d.group(1)
        elif "simp argument is unused" in msg:
            k = "unused-simp-arg"
        elif "not explicitly referenced" in msg:
            k = "unused-variable"
        elif "already closes the goal" in msg:
            k = "already-closes"
        elif "is a proposition" in msg:
            k = "prop-def"
        else:
            k = "other"
        w[mod][k] += 1

deps = {}
for f in glob.glob("conf-typing/ConfTyping/*.lean"):
    mod = f[len("conf-typing/"):-len(".lean")].replace("/", ".")
    deps[mod] = set(re.findall(r"^import (\S+)", open(f).read(), re.M))
down = {"ConfTyping.Pleak"}
changed = True
while changed:
    changed = False
    for m, ds in deps.items():
        if m not in down and ds & down:
            down.add(m)
            changed = True
down.discard("ConfTyping.Pleak")

mods = sorted(deps) + ["TransportCalculus"]
rows = [
    "# S-435 (backlog/S-435.md): conf-typing + transport-calculus moved from Lean v4.31.0 to v4.35.0 on a",
    "# scratch copy of 13be027. errors_unmodified: errors building the unmodified source (receipt",
    "# s435b-ct1). reached_unmodified: no if the module imports Pleak, so that build never reached it.",
    "# warnings: the full build after the one Pleak fix (s435b-ctA, s435b-tc). footprint_changed:",
    "# declarations whose axiom set differs from tools/axioms.expected after the Pleak fix (every one",
    "# grew). after_pin: still different once `BEq Int` is pinned to instBEqOfDecidableEq in Imp.lean",
    "# (s435b-ctB). removed: declarations absent from the 4.35 manifest (all auto-generated toCtorIdx).",
    "module\terrors_unmodified\treached_unmodified\twarnings\tfootprint_changed\tafter_pin\tremoved\twarning_kinds",
]
for m in mods:
    kinds = ",".join(f"{k}={v}" for k, v in sorted(w[m].items())) or "-"
    rows.append("\t".join([m, str(err[m]), "no" if m in down else "yes", str(sum(w[m].values())),
                           str(grewA[m]), str(grewB[m]), str(gone[m]), kinds]))
open("bench/s435.tsv", "w").write("\n".join(rows) + "\n")
print(f"{len(mods)} modules; errors {sum(err.values())}; not reached {len(down)}; "
      f"changed {sum(grewA.values())} in {sum(1 for m in mods if grewA[m])} modules; "
      f"after pin {sum(grewB.values())}; removed {sum(gone.values())}; "
      f"warnings {sum(sum(c.values()) for c in w.values())}")
