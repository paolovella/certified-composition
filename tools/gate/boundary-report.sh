#!/usr/bin/env bash
# The boundary warden's input (P0-12): how far the checkers have drifted since the user's last
# sign-off, mechanically. Nothing here judges; tools/gate/warden.sh hands this to the agent.
#
#   tools/gate/boundary-report.sh BASE_DIR PR_DIR
#
# The sign-off is BASE's tools/checkers.baseline (Ring 0: a PR cannot move it). For every
# checker whose entries differ between the baseline and the PR's tools/checkers.lock, it prints
# whether this PR changes it too, its frozen soundness statement, and the diff of the module that
# defines it since the baseline commit (or since BASE, if that commit is not in PR_DIR's history).
# The first line is a summary the scripts read: `boundary: N drifted, M changed by this PR`.
set -uo pipefail
[ $# -eq 2 ] || { echo "usage: boundary-report.sh BASE_DIR PR_DIR"; exit 2; }
base=$(cd "$1" && pwd) && pr=$(cd "$2" && pwd) || exit 2
bl="$base/tools/checkers.baseline"
[ -f "$bl" ] || { echo "boundary: NO BASELINE (tools/checkers.baseline missing on the base)"; exit 1; }
[ -f "$pr/tools/checkers.lock" ] || { echo "boundary: NO checkers.lock in the PR"; exit 1; }
since=$(sed -n '1s/^baseline\t//p' "$bl")
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
tail -n +2 "$bl" | LC_ALL=C sort > "$tmp/bl"
LC_ALL=C sort "$pr/tools/checkers.lock" > "$tmp/pr"
if [ -f "$base/tools/checkers.lock" ]; then LC_ALL=C sort "$base/tools/checkers.lock" > "$tmp/base"; else : > "$tmp/base"; fi
names() { LC_ALL=C comm -3 "$1" "$2" | sed 's/^\t//' | cut -f2 | LC_ALL=C sort -u; }
drifted=$(names "$tmp/bl" "$tmp/pr")
changed=$(names "$tmp/base" "$tmp/pr")
nd=$(printf '%s' "$drifted" | grep -c . || true)
nc=$(printf '%s' "$changed" | grep -c . || true)
echo "boundary: $nd drifted, $nc changed by this PR"
echo "baseline commit: ${since:-unknown}"
[ "$nd" = 0 ] && exit 0
if git -C "$pr" cat-file -e "${since}^{commit}" 2>/dev/null; then from=$since; fromlabel="the baseline commit"
else from=""; fromlabel="BASE (the baseline commit is not in the PR's history)"; fi
for k in $drifted; do
  short=${k##*.}
  echo
  echo "=== checker $k"
  if printf '%s\n' "$changed" | grep -qxF "$k"; then echo "changed by this PR: yes"; else echo "changed by this PR: no (earlier changes)"; fi
  echo "entries differing from the baseline:"
  LC_ALL=C comm -3 "$tmp/bl" "$tmp/pr" | sed 's/^\t/+ /; t; s/^/- /' | awk -F'\t' -v k="$k" '$2 == k {print "  " $1 " " $3}'
  echo "frozen statement:"
  awk -v n="theorem Frozen.${short}_sound" 'index($0, n) == 1 {p=1} p {print "  " $0} p && /:= sorry/ {exit}' "$pr/workspace/Statements.lean"
  file=$(cd "$pr" && grep -rlE "^(private |protected )?def ${short}( |$)" conf-typing/ConfTyping transport-calculus 2>/dev/null | head -1)
  if [ -z "$file" ]; then echo "defining module: NOT FOUND"; continue; fi
  echo "defining module: $file; diff since $fromlabel:"
  if [ -n "$from" ]; then git -C "$pr" diff "$from" -- "$file" | sed 's/^/  /'
  else diff -u "$base/$file" "$pr/$file" | sed 's/^/  /'; fi
done
