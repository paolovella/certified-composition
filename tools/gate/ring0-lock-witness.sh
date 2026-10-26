#!/usr/bin/env bash
# Witnesses for tools/ring0.lock (P0-03). Accepted: `ring0-lock.sh --check` on the real tree
# (tools/ci.sh). Refused, in a copy:
#   definition   `CostAtMost`, which `costCheck_sound` states, is edited to `k ≥ o.2.1`:
#                definitionally the same, so every proof still builds and `lake comparator`
#                still accepts (checked here: that is the comparator's blind spot). Only the lock
#                notices. The build cannot tell an edit that keeps the meaning from one that
#                weakens it, so both need the user's key. (`True` breaks the proofs, and
#                `k + 0` a unification, so the refusal would be the build's, not the lock's.)
#   challenge    one byte of the challenge's prose changes.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
REPO=$(pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
pass=0; fail=0

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

refuses() {  # refuses NAME DIR
  if ( cd "$2" && bash tools/ring0-lock.sh --check ) > "$tmp/$1.log" 2>&1; then
    printf '  FAIL  %-12s the lock did not change\n' "$1"; fail=$((fail+1))
  elif ! grep -q "^ring0-lock: tools/ring0.lock does not match" "$tmp/$1.log"; then
    printf '  FAIL  %-12s refused, but not by the lock: %s\n' "$1" "$(tail -1 "$tmp/$1.log")"; fail=$((fail+1))
  else
    printf '  ok    %-12s refused: %s\n' "$1" "$(grep -m1 -E '^[-+][^-+]' "$tmp/$1.log" | cut -c1-80)"
    pass=$((pass+1))
  fi
}

echo "ring0.lock witnesses"
copy "$tmp/d"
python3 -I - "$tmp/d/conf-typing/ConfTyping/CostBound.lean" <<'EOF'
import re, sys
p = sys.argv[1]
s = open(p).read()
old = "  ∀ (n : Nat) (σ : Store) (o : Outcome), wexec n c σ = some o → o.2.1 ≤ k\n"
assert s.count(old) == 1, "CostAtMost body not found"
s = s.replace(old, "  ∀ (n : Nat) (σ : Store) (o : Outcome), wexec n c σ = some o → k ≥ o.2.1\n")
open(p, "w").write(s)
EOF
# built first, as tools/ci.sh does: inside its sandbox the comparator can write only the root
# .lake, so it cannot rebuild a changed module of a path dependency (conf-typing).
if ( cd "$tmp/d" && lake build StatementsProof && lake comparator ) > "$tmp/comparator.log" 2>&1; then
  printf '  ok    %-12s the comparator accepts the edited definition (its blind spot)\n' comparator
  pass=$((pass+1))
else
  printf '  FAIL  %-12s the comparator refused; the edit is not the case this witness is about\n' comparator; grep -E "error" -A6 "$tmp/comparator.log" | head -20
  fail=$((fail+1))
fi
refuses definition "$tmp/d"
copy "$tmp/c"
sed -i '0,/frozen statements (P0-03/s//frozen statements  (P0-03/' "$tmp/c/workspace/Statements.lean"
refuses challenge "$tmp/c"
echo "ring0.lock witnesses: $pass passed, $fail failed"
[ "$fail" = 0 ]
