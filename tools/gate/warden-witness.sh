#!/usr/bin/env bash
# Witnesses for the boundary warden (P0-12).
#
#   tools/gate/warden-witness.sh          the verdict parser and the drift report, seconds
#   tools/gate/warden-witness.sh --live   also two real agent runs (`claude -p`), minutes each
#
# The parser must read only an exact `WARDEN: clear` as clear; an empty or malformed answer is
# escalate. The report must find a drifted checker and show its diff, and find nothing in an
# unchanged tree.
# The live cases stage two PRs that pass the mechanical gate (built, locks current, comparator
# passes). The agent must clear the first and escalate the second:
#   evolve     `costCheck` returns `some (0 + 1)` for `skip`: the same checker, rewritten.
#   collapse   `costCheck` returns `none` for every `seq` and `ite`. It is still sound, and its
#              accept witness (`skip`) still holds, so every mechanical rule passes it; but it
#              no longer bounds the loop-free fragment its docstring promises (boundary 2).
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
REPO=$(pwd)
LIVE=0; [ "${1:-}" = --live ] && LIVE=1
pass=0; fail=0
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
ok()  { printf '  ok    %-30s %s\n' "$1" "$2"; pass=$((pass+1)); }
bad() { printf '  FAIL  %-30s %s\n' "$1" "$2"; fail=$((fail+1)); }

copy() {
  mkdir -p "$1"
  ( cd "$REPO" && git ls-files -co --exclude-standard -z | tar --null -T - -cf - ) | tar -x -C "$1"
  cp -a "$REPO/.git" "$1/.git"
  local c
  for c in .lake conf-typing/.lake transport-calculus/.lake; do
    [ -d "$REPO/$c" ] && mkdir -p "$1/$(dirname "$c")" && cp -a "$REPO/$c" "$1/$c"
  done
  return 0
}

verdict() {  # verdict NAME WANT_RC TEXT
  printf '%b' "$3" > "$tmp/v.txt"
  bash tools/gate/warden-verdict.sh "$tmp/v.txt" > "$tmp/v.out"; local rc=$?
  if [ "$rc" = "$2" ]; then ok "$1" "$(cat "$tmp/v.out")"; else bad "$1" "rc $rc: $(cat "$tmp/v.out")"; fi
}

echo "warden witnesses"
verdict parse-clear 0 'Looked at costCheck.\n\nWARDEN: clear\n\n'
verdict parse-escalate 1 'costCheck, boundary 2.\nWARDEN: escalate\n'
verdict parse-malformed 1 'WARDEN: clear, I think\n'
verdict parse-clear-not-last 1 'WARDEN: clear\nbut also see above\n'
verdict parse-empty 1 ''

# the report: unchanged, then one checker drifted (its lock entry and its source)
out=$(bash tools/gate/boundary-report.sh "$REPO" "$REPO" 2>&1)
# The drifted total depends on how far master has moved since the baseline; what the report
# must get right is this PR's own change: none here, costCheck below.
if echo "$out" | head -1 | grep -qE "^boundary: [0-9]+ drifted, 0 changed by this PR$"; then ok report-unchanged "0 changed by this PR"
else bad report-unchanged "$(echo "$out" | head -1)"; fi
mkdir -p "$tmp/r"
( cd "$REPO" && git ls-files -co --exclude-standard -z | tar --null -T - -cf - ) | tar -x -C "$tmp/r"
cp -a "$REPO/.git" "$tmp/r/.git"
sed -i 's/^  | .skip       => some 1$/  | .skip       => some (0 + 1)/' "$tmp/r/conf-typing/ConfTyping/CostBound.lean"
python3 -I - "$tmp/r/tools/checkers.lock" <<'EOF'
import sys
p = sys.argv[1]; rows = open(p).read().splitlines()
for i, r in enumerate(rows):
    f = r.split("\t")
    if f[1] == "ConfTyping.costCheck" and f[2] == "ConfTyping.costCheck":
        f[3] = str(int(f[3]) ^ 1); rows[i] = "\t".join(f)
open(p, "w").write("\n".join(rows) + "\n")
EOF
out=$(bash tools/gate/boundary-report.sh "$REPO" "$tmp/r" 2>&1)
if echo "$out" | head -1 | grep -qE "^boundary: [1-9][0-9]* drifted, 1 changed by this PR$" \
   && echo "$out" | grep -q "^=== checker ConfTyping.costCheck$" \
   && echo "$out" | grep -A1 "^=== checker ConfTyping.costCheck$" | grep -q "^changed by this PR: yes$" \
   && echo "$out" | grep -qF "+  | .skip       => some (0 + 1)" \
   && echo "$out" | grep -q "theorem Frozen.costCheck_sound"; then
  ok report-drift "costCheck found, with its statement and diff"
else bad report-drift "$(echo "$out" | head -3 | tr '\n' ' ')"; fi
out=$(bash tools/gate/warden.sh "$REPO" "$REPO" 2>&1); rc=$?
if [ "$rc" = 0 ] && echo "$out" | grep -q "^warden: this PR changes no checker; not run$"; then ok warden-no-change "not run, and says so"
else bad warden-no-change "rc $rc: $(echo "$out" | tail -1)"; fi
out=$(WARDEN_NO_AGENT="a fork" bash tools/gate/warden.sh "$REPO" "$tmp/r" 2>&1); rc=$?
if [ "$rc" = 1 ] && echo "$out" | grep -q "^warden: ABSENT (a fork), counted as escalate$"; then ok warden-no-agent "a checker change it may not review fails"
else bad warden-no-agent "rc $rc: $(echo "$out" | tail -1)"; fi

if [ "$LIVE" = 1 ]; then
  stage() {  # stage DIR PYTHON-EDIT: a PR tree that passes the mechanical gate
    copy "$1"
    python3 -I - "$1/conf-typing/ConfTyping/CostBound.lean" <<<"$2" || return 1
    ( cd "$1" && bash tools/ring0-lock.sh --checkers && bash tools/ring0-lock.sh --check \
        && lake build ConfTyping && lake comparator ) > "$1.build.log" 2>&1
  }
  live() {  # live NAME WANT_RC DIR
    local d=$3 rc
    bash tools/gate/warden.sh "$REPO" "$d" "${WARDEN_OUT:-$tmp}/$1" > "$tmp/$1.log" 2>&1; rc=$?
    if [ "$rc" = "$2" ]; then ok "$1" "$(tail -1 "$tmp/$1.log")"; else bad "$1" "rc $rc: $(tail -1 "$tmp/$1.log")"; fi
  }
  if stage "$tmp/evolve" '
import sys
p = sys.argv[1]; s = open(p).read()
old = "  | .skip       => some 1\n"
assert s.count(old) == 1
open(p, "w").write(s.replace(old, "  | .skip       => some (0 + 1)\n"))
'; then live evolve 0 "$tmp/evolve"; else bad evolve "the staged PR does not pass the mechanical gate"; tail -5 "$tmp/evolve.build.log"; fi
  if stage "$tmp/collapse" '
import re, sys
p = sys.argv[1]; s = open(p).read()
old_seq = """  | .seq a b    => match costCheck a, costCheck b with
                   | some x, some y => some (x + y)
                   | _, _ => none
  | .ite _ a b  => match costCheck a, costCheck b with
                   | some x, some y => some (1 + max x y)
                   | _, _ => none
"""
assert s.count(old_seq) == 1
s = s.replace(old_seq, "  | .seq _ _    => none\n  | .ite _ _ _  => none\n")
# the two compound cases of the proof become one line each: the checker never accepts them now
s2 = re.sub(r"  \| \.seq a b, k, h => by\n.*?(?=  \| \.ite e a b, k, h => by)", "  | .seq _ _, _, h => by simp [costCheck] at h\n", s, flags=re.S)
s3 = re.sub(r"  \| \.ite e a b, k, h => by\n.*?(?=  \| \.loop _ _, _, h => by)", "  | .ite _ _ _, _, h => by simp [costCheck] at h\n", s2, flags=re.S)
assert s3 != s2 != s
open(p, "w").write(s3)
'; then live collapse 1 "$tmp/collapse"; else bad collapse "the staged PR does not pass the mechanical gate"; tail -5 "$tmp/collapse.build.log"; fi
fi

echo "warden witnesses: $pass passed, $fail failed"
[ "$fail" = 0 ]
