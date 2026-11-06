#!/usr/bin/env bash
# F6: a one-off witness that ring0.lock covers the kernel's seventh shape, which the comparator cannot see.
# In a copy, Cert.boundR's body is rewritten as `k ≥ cost` in place of `cost ≤ k`: definitionally the same, so every proof
# builds and `lake comparator` accepts. The lock must refuse. Not in CI: the edit rebuilds everything downstream of the kernel.
# Usage, from the repo root: bash research/2026-11/f6_lock_witness.sh <scratch directory>
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
REPO=$(pwd)
d="$1/f6-lock"
case "$d" in /tmp/*) ;; *) echo "refusing a scratch directory outside /tmp: $d"; exit 2;; esac
[ -e "$d" ] && { echo "$d exists; remove it first"; exit 2; }
mkdir -p "$d"
( cd "$REPO" && git ls-files -co --exclude-standard -z | tar --null -T - -cf - ) | tar -x -C "$d"
cp -a "$REPO/.git" "$d/.git"
for c in .lake conf-typing/.lake transport-calculus/.lake l-core/.lake; do
  [ -d "$REPO/$c" ] && mkdir -p "$d/$(dirname "$c")" && cp -a "$REPO/$c" "$d/$c"
done
python3 -I - "$d/l-core/LCore/Kernel/Cert.lean" <<'EOF'
import sys
p = sys.argv[1]
s = open(p).read()
old = "  ∀ (i : L.In), L.Adm i → ∃ k, R i k ∧ ∀ (n : Nat), (L.run n p i).cost ≤ k\n"
assert s.count(old) == 1, "boundR body not found"
s = s.replace(old, "  ∀ (i : L.In), L.Adm i → ∃ k, R i k ∧ ∀ (n : Nat), k ≥ (L.run n p i).cost\n")
open(p, "w").write(s)
EOF
ok=0
if ( cd "$d" && lake build StatementsProof && lake comparator ) > "$d/comparator.log" 2>&1; then
  echo "ok    the edited kernel builds and the comparator accepts it (its blind spot)"
else
  echo "FAIL  the comparator or the build refused: the edit is not the case this witness is about"; tail -5 "$d/comparator.log"; ok=1
fi
if ( cd "$d" && bash tools/ring0-lock.sh --check ) > "$d/lock.log" 2>&1; then
  echo "FAIL  the lock did not change"; ok=1
elif grep -q "^ring0-lock: tools/ring0.lock does not match" "$d/lock.log"; then
  echo "ok    the lock refuses: $(grep -m1 -E '^[-+][^-+]' "$d/lock.log" | cut -c1-90)"
else
  echo "FAIL  refused, but not by the lock: $(tail -1 "$d/lock.log")"; ok=1
fi
exit $ok
