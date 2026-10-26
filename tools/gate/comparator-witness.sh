#!/usr/bin/env bash
# Witnesses for the frozen-statement comparator (P0-03). The accepted witness is `lake comparator`
# passing on the real tree (tools/ci.sh). Refused, in a copy:
#   weakened   the solution proves a weaker `Frozen.costCheck_sound` (an extra `False`
#              hypothesis makes it trivial): the statements differ, so the comparator must refuse.
#   missing    the solution drops a frozen theorem altogether.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
REPO=$(pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
pass=0; fail=0

copy() {
  mkdir -p "$1"
  ( cd "$REPO" && git ls-files -co --exclude-standard -z | tar --null -T - -cf - ) | tar -x -C "$1"
  local c
  for c in .lake conf-typing/.lake transport-calculus/.lake; do
    [ -d "$REPO/$c" ] && mkdir -p "$1/$(dirname "$c")" && cp -a "$REPO/$c" "$1/$c"
  done
  return 0
}

refuses() {  # refuses NAME DIR
  if ( cd "$2" && lake comparator ) > "$tmp/$1.log" 2>&1; then
    printf '  FAIL  %-24s the comparator ACCEPTED it\n' "$1"; fail=$((fail+1))
  else
    printf '  ok    %-24s refused: %s\n' "$1" "$(grep -m1 -iE "mismatch|not found|missing|error|does not" "$tmp/$1.log" | cut -c1-90)"
    pass=$((pass+1))
  fi
}

echo "comparator witnesses"
copy "$tmp/w"
python3 -I - "$tmp/w/workspace/StatementsProof.lean" <<'EOF'
import sys
p = sys.argv[1]
s = open(p).read()
old = "theorem Frozen.costCheck_sound :"
assert s.count(old) == 1
s = s.replace(old, "theorem Frozen.costCheck_sound (_hweak : False) :")
s = s.replace("theorem Frozen.costCheck_sound (_hweak : False) : ∀ (c : WCmd) (k : Nat), costCheck c = some k → CostAtMost c k := by",
              "theorem Frozen.costCheck_sound (_hweak : False) : ∀ (c : WCmd) (k : Nat), costCheck c = some k → CostAtMost c k := by\n  exact absurd _hweak id\n  all_goals")
open(p, "w").write(s)
EOF
refuses weakened "$tmp/w"
copy "$tmp/m"
python3 -I - "$tmp/m/workspace/StatementsProof.lean" <<'EOF'
import re, sys
p = sys.argv[1]
s = open(p).read()
s2 = re.sub(r"namespace ConfTyping\n\ntheorem Frozen\.wcheck_sound.*?end ConfTyping\n", "", s, flags=re.S)
assert s2 != s
open(p, "w").write(s2)
EOF
refuses missing "$tmp/m"
echo "comparator witnesses: $pass passed, $fail failed"
[ "$fail" = 0 ]
