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
#   ci        BASE's tools/ci.sh --fast runs on the overlaid copy.
# Gate code = tools/ and .github/ minus the data a PR may change: tools/axioms.expected (judged
# by `manifest`) and tools/receipts/ (written by every long job).
#
# GATE_ONLY="ring0 manifest" runs only those checks and prints no verdict. It exists for the
# refused witnesses (tools/gate/base-gate-witness.sh); the workflow never sets it.
#
# The PR's code is built here. Whoever runs this must hold nothing worth stealing: the workflow
# gives it a read-only token and no secrets.
set -uo pipefail
HEAVY=0; [ "${1:-}" = --heavy ] && { HEAVY=1; shift; }
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
caches=(.lake conf-typing/.lake transport-calculus/.lake)
[ "$HEAVY" = 1 ] && caches+=(transport-kernel/.lake)
for d in "${caches[@]}"; do
  [ -d "$pr/$d" ] && mkdir -p "$work/$(dirname "$d")" && cp -a --reflink=auto "$pr/$d" "$work/$d"
done

overlay() {
  local keep="$tmp/keep"; mkdir -p "$keep"
  [ -f "$work/tools/axioms.expected" ] && cp "$work/tools/axioms.expected" "$keep/"
  [ -d "$work/tools/receipts" ] && cp -a "$work/tools/receipts" "$keep/"
  rm -rf "$work/tools" "$work/.github"
  ( cd "$base" && git ls-files -co --exclude-standard -z tools .github | tar --null -T - -cf - ) | tar -x -C "$work"
  rm -rf "$work/tools/receipts"
  [ -f "$keep/axioms.expected" ] && cp "$keep/axioms.expected" "$work/tools/axioms.expected"
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
         "workspace/*", "comparator.json", "AUTONOMY"]
DATA = ["tools/axioms.expected", "tools/receipts/*"]
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
want ci       && { ci       || fail=1; }
if [ -n "$only" ]; then
  echo "gate: partial run (GATE_ONLY=$only), no verdict"
elif [ "$fail" = 0 ]; then
  echo "gate: PASS"
else
  echo "gate: FAIL"
fi
exit "$fail"
