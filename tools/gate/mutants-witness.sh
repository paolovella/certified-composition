#!/usr/bin/env bash
# Witnesses for the mutant runner (P0-05). Without a refused case, "0 survived" would also be
# printed by a runner that kills everything, for instance because every copy fails to build.
#   accepted: on this tree, secCheckD's one mutant is killed.
#   refused:  with secCheckD_accepts_skip deleted (the witness P0-05 added to kill exactly that
#             mutant), the same mutant survives.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
REPO=$(pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
pass=0; fail=0

copy() {  # a git checkout-like copy with the two packages and tools, so ROOT resolves to it
  mkdir -p "$1"
  ( cd "$REPO" && git ls-files -co --exclude-standard -z conf-typing transport-calculus tools \
      | tar --null -T - -cf - ) | tar -x -C "$1"
  cp -a "$REPO/conf-typing/.lake" "$1/conf-typing/.lake" 2>/dev/null
  cp -a "$REPO/transport-calculus/.lake" "$1/transport-calculus/.lake" 2>/dev/null
  ( cd "$1" && git init -q && git add -A >/dev/null 2>&1 )
}

check() {  # check NAME EXPECTED_SURVIVORS DIR
  local out got
  out=$(cd "$3" && python3 tools/mutants.py --only secCheckD --jobs 1 2>&1 | tail -1)
  got=$(echo "$out" | sed -nE 's/.* ([0-9]+) survived.*/\1/p')
  if [ "$got" = "$2" ]; then
    printf '  ok    %-34s %s\n' "$1" "$out"; pass=$((pass+1))
  else
    printf '  FAIL  %-34s expected %s survived, got: %s\n' "$1" "$2" "$out"; fail=$((fail+1))
  fi
}

echo "mutant runner witnesses"
copy "$tmp/a"
check "secCheckD as committed" 0 "$tmp/a"
copy "$tmp/r"
# the theorem and its doc comment, the line above it
python3 -I - "$tmp/r/conf-typing/ConfTyping/Witnesses.lean" <<'EOF2'
import sys
p = sys.argv[1]
ls = open(p).read().split("\n")
i = next(k for k, l in enumerate(ls) if l.startswith("theorem secCheckD_accepts_skip"))
assert ls[i - 1].startswith("/--")
open(p, "w").write("\n".join(ls[:i - 1] + ls[i + 1:]))
EOF2
check "secCheckD witness deleted" 1 "$tmp/r"
echo "mutant runner witnesses: $pass passed, $fail failed"
[ "$fail" = 0 ]
