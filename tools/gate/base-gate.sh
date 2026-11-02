#!/usr/bin/env bash
# The base-branch gate (P0-06): judge a PR tree with the BASE tree's gate, so a PR cannot weaken
# the checks it is judged by.
#
#   tools/gate/base-gate.sh [--heavy] BASE_DIR PR_DIR
#
# --heavy (the self-hosted heavy runner): ci runs `tools/ci.sh --require-heavy`, the full run with
# every tool required, and the mathlib build cache is copied too.
#
# BASE_DIR and PR_DIR are git checkouts (the workflow checks out master and the PR head). The
# PR tree is copied, BASE's gate code is laid over the copy, and in the copy:
#   ring0     paths the PR changes that are Ring 0 (CLAUDE.md) are listed. If there are any,
#             the check fails: such a PR merges only with the user's key.
#   manifest  every line of BASE's tools/axioms.expected must still be in the PR's: the
#             manifest may grow, not change (PLAN-2026-10 §7, tier G-C).
#   checkers  at most CHECKER_LIMIT checkers may differ between BASE's tools/checkers.lock and
#             the PR's (P0-11). A checker edit cannot weaken a frozen statement, which must still
#             be proved against tools/ring0.lock, so it needs no key; the limit keeps one change
#             from rewriting the checkers wholesale. ci checks that the PR's checkers.lock is
#             current.
#   registry  the PR's tools/witnesses.expected may grow, never shrink (P0-13): every checker in
#             BASE's registry is still there, no checker's accepted or refused count goes down,
#             every checker has at least one of each, and none is missing a witness. A change
#             that adds a checker (EXPR-02 added `bcheckF`) then needs no key. ci checks the
#             PR's registry is current.
#   mutants   every row of the PR's tools/mutants.expected is `killed`: a checker edit moves the
#             mutation sites, so the table moves with it, but no survivor merges without the key.
#             ci checks the sites are today's; the heavy runner rebuilds every mutant.
#   ci        BASE's tools/ci.sh --fast runs on the overlaid copy.
# Gate code = tools/ and .github/ minus the data a PR may change: tools/axioms.expected (judged
# by `manifest`), tools/checkers.lock (`checkers`), tools/mutants.expected (`mutants`),
# tools/witnesses.expected (`registry`) and tools/receipts/ (written by every long job).
#
# GATE_ONLY="ring0 manifest" runs only those checks and prints no verdict. It exists for the
# refused witnesses (tools/gate/base-gate-witness.sh); the workflow never sets it.
#
# The PR's code is built here. Whoever runs this must hold nothing worth stealing: the workflow
# gives it a read-only token and no secrets.
set -uo pipefail
HEAVY=0; [ "${1:-}" = --heavy ] && { HEAVY=1; shift; }
CHECKER_LIMIT=3   # checkers one change may touch without the user's key (P0-11)
DATA_FILES="axioms.expected checkers.lock mutants.expected witnesses.expected"   # under tools/
[ $# -eq 2 ] || { echo "usage: base-gate.sh [--heavy] BASE_DIR PR_DIR"; exit 2; }
base=$(cd "$1" && pwd) && pr=$(cd "$2" && pwd) || exit 2
only=${GATE_ONLY:-}
want() { [ -z "$only" ] || [[ " $only " == *" $1 "* ]]; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
work="$tmp/pr"
mkdir -p "$work"
# the PR as git sees it (tracked + untracked-not-ignored), with its .git so the scripts that ask
# git for the file list keep working; a build cache is reused when present.
( cd "$pr" && git ls-files -co --exclude-standard -z | tar --null -T - -cf - ) | tar -x -C "$work"
cp -a "$pr/.git" "$work/.git"
# transport-kernel/.lake (mathlib, ~7.5 GB) only for --heavy: the hosted gate runs --fast.
caches=(.lake conf-typing/.lake transport-calculus/.lake l-core/.lake)
[ "$HEAVY" = 1 ] && caches+=(transport-kernel/.lake)
for d in "${caches[@]}"; do
  [ -d "$pr/$d" ] && mkdir -p "$work/$(dirname "$d")" && cp -a --reflink=auto "$pr/$d" "$work/$d"
done

overlay() {
  local keep="$tmp/keep"; mkdir -p "$keep"
  local f
  for f in $DATA_FILES; do [ -f "$work/tools/$f" ] && cp "$work/tools/$f" "$keep/"; done
  [ -d "$work/tools/receipts" ] && cp -a "$work/tools/receipts" "$keep/"
  rm -rf "$work/tools" "$work/.github"
  ( cd "$base" && git ls-files -co --exclude-standard -z tools .github | tar --null -T - -cf - ) | tar -x -C "$work"
  rm -rf "$work/tools/receipts"
  for f in $DATA_FILES; do [ -f "$keep/$f" ] && cp "$keep/$f" "$work/tools/$f"; done
  [ -d "$keep/receipts" ] && cp -a "$keep/receipts" "$work/tools/receipts"
  return 0
}

fail=0
# Ring 0 as CLAUDE.md states it until l-core/ exists; data paths are left out (see header).
ring0() {
  local changed
  changed=$(python3 -I - "$base" "$pr" <<'EOF'
import fnmatch, hashlib, subprocess, sys
def files(d):
    out = subprocess.run(["git", "-C", d, "ls-files", "-co", "--exclude-standard", "-z"],
                         capture_output=True, check=True).stdout.split(b"\0")
    res = {}
    for p in filter(None, out):
        p = p.decode()
        try:
            res[p] = hashlib.sha256(open(f"{d}/{p}", "rb").read()).hexdigest()
        except FileNotFoundError:
            pass
    return res
b, p = files(sys.argv[1]), files(sys.argv[2])
changed = sorted(f for f in set(b) | set(p) if b.get(f) != p.get(f))
RING0 = ["tools/*", ".github/*", "CLAUDE.md", ".claude/*", "*/lean-toolchain", "*/lakefile*",
         "*/lake-manifest.json", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
         "workspace/*", "comparator.json", "AUTONOMY", "l-core/LCore/Kernel/*"]
DATA = ["tools/axioms.expected", "tools/checkers.lock", "tools/mutants.expected",
        "tools/witnesses.expected", "tools/receipts/*"]
for f in changed:
    if any(fnmatch.fnmatch(f, g) for g in RING0) and not any(fnmatch.fnmatch(f, g) for g in DATA):
        print(f)
EOF
  ) || { echo "gate: ring0 could not compare the trees"; return 1; }
  if [ -n "$changed" ]; then
    echo "gate: ring0 TOUCHED, needs the user's key:"; echo "$changed" | sed 's/^/  /'
    return 1
  fi
  echo "gate: ring0 untouched"
}

manifest() {
  local b="$base/tools/axioms.expected" p="$work/tools/axioms.expected" gone added
  [ -f "$p" ] || { echo "gate: manifest MISSING in the PR"; return 1; }
  gone=$(LC_ALL=C comm -23 <(LC_ALL=C sort "$b") <(LC_ALL=C sort "$p"))
  added=$(LC_ALL=C comm -13 <(LC_ALL=C sort "$b") <(LC_ALL=C sort "$p") | wc -l)
  if [ -n "$gone" ]; then
    echo "gate: manifest lines REMOVED or CHANGED ($(echo "$gone" | wc -l)):"
    echo "$gone" | head -20 | sed 's/^/  /'
    return 1
  fi
  echo "gate: manifest additions only ($added added)"
}

checkers() {
  local b="$base/tools/checkers.lock" p="$work/tools/checkers.lock" touched n
  [ -f "$p" ] || { echo "gate: checkers.lock MISSING in the PR"; return 1; }
  if [ ! -f "$b" ]; then
    echo "gate: checkers: the base has no tools/checkers.lock, so there is no limit to apply (Ring 0 decides this PR)"
    return 0
  fi
  touched=$(LC_ALL=C comm -3 <(LC_ALL=C sort "$b") <(LC_ALL=C sort "$p") | sed 's/^\t//' | cut -f2 | LC_ALL=C sort -u)
  n=$(printf '%s' "$touched" | grep -c . || true)
  if [ "$n" -gt "$CHECKER_LIMIT" ]; then
    echo "gate: checkers: $n changed, over the limit of $CHECKER_LIMIT; needs the user's key:"
    echo "$touched" | sed 's/^/  /'
    return 1
  fi
  echo "gate: checkers: $n changed (limit $CHECKER_LIMIT)${touched:+: $(echo $touched)}"
}

registry() {
  local b="$base/tools/witnesses.expected" p="$work/tools/witnesses.expected" out
  [ -f "$p" ] || { echo "gate: registry MISSING in the PR"; return 1; }
  [ -f "$b" ] || { echo "gate: registry: the base has none, nothing to compare (Ring 0 decides this PR)"; return 0; }
  out=$(python3 -I - "$b" "$p" <<'PYR'
import re, sys
def load(f):
    rows, summary = {}, None
    for l in open(f).read().splitlines():
        if l.startswith("registry: "):
            summary = l
            continue
        c = l.split("\t")
        if len(c) >= 3 and c[1].isdigit() and c[2].isdigit():
            rows[c[0]] = (int(c[1]), int(c[2]))
    return rows, summary
b, _ = load(sys.argv[1]); p, ps = load(sys.argv[2])
errs = []
for k, (a, r) in sorted(b.items()):
    if k not in p:
        errs.append(f"{k} removed")
    elif p[k][0] < a or p[k][1] < r:
        errs.append(f"{k} witnesses {a}/{r} -> {p[k][0]}/{p[k][1]}")
for k, (a, r) in sorted(p.items()):
    if a < 1 or r < 1:
        errs.append(f"{k} has {a} accepted, {r} refused")
if not ps or not re.fullmatch(r"registry: \d+ checkers, 0 missing a witness", ps):
    errs.append(f"summary: {ps}")
added = sorted(set(p) - set(b))
if errs:
    print("FAIL\t" + "; ".join(errs[:10]))
else:
    print(f"OK\t{len(p)} checkers, {len(added)} added" + (": " + " ".join(added) if added else ""))
PYR
  )
  case "$out" in
    OK*)   echo "gate: registry: ${out#OK	}" ;;
    *)     echo "gate: registry SHRANK or a checker lacks a witness, needs the user's key: ${out#FAIL	}"; return 1 ;;
  esac
}

mutants() {
  local p="$work/tools/mutants.expected" bad
  [ -f "$p" ] || { echo "gate: mutants.expected MISSING in the PR"; return 1; }
  bad=$(grep -v '^mutants: ' "$p" | awk -F'\t' '$4 != "killed"')
  if [ -n "$bad" ] || ! grep -qE '^mutants: .* 0 survived, 0 unexplained$' "$p"; then
    echo "gate: mutants: rows not killed ($(printf '%s' "$bad" | grep -c . || true)), needs the user's key:"
    printf '%s\n' "$bad" | head -10 | sed 's/^/  /'
    return 1
  fi
  echo "gate: mutants: all $(grep -vc '^mutants: ' "$p") killed"
}

ci() {
  local mode=--fast; [ "$HEAVY" = 1 ] && mode=--require-heavy
  ( cd "$work" && bash tools/ci.sh "$mode" ) > "$tmp/ci.log" 2>&1
  local rc=$?
  grep -E "^=== |^    (FAILED|ABSENT|DEFERRED)|^CI: " "$tmp/ci.log" | sed 's/^/  /'
  if [ "$rc" = 0 ]; then echo "gate: ci passed"; else echo "gate: ci FAILED"; return 1; fi
}

overlay
want ring0    && { ring0    || fail=1; }
want manifest && { manifest || fail=1; }
want checkers && { checkers || fail=1; }
want registry && { registry || fail=1; }
want mutants  && { mutants  || fail=1; }
want ci       && { ci       || fail=1; }
if [ -n "$only" ]; then
  echo "gate: partial run (GATE_ONLY=$only), no verdict"
elif [ "$fail" = 0 ]; then
  echo "gate: PASS"
else
  echo "gate: FAIL"
fi
exit "$fail"
