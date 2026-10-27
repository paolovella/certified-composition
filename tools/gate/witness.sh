#!/usr/bin/env bash
# The refused witnesses for the two kernel gates (P0-02): both must refuse a package whose one
# theorem uses a planted axiom. The accepted witnesses are the gates passing on the real tree
# (tools/ci.sh). Prints one line per route; exits non-zero if a gate accepted.
#
# The package config lives in tools/gate/witness/; its one Lean file is written here, into a
# scratch copy, at run time. The pre-commit hook refuses any staged Lean change containing the
# axiom keyword, so no tracked Lean file holds the planted declaration. It exists only for the
# length of this run, outside the root workspace and the manifest.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0
pkg="$tmp/pkg"
mkdir -p "$pkg" && cp tools/gate/witness/lakefile.toml tools/gate/witness/lean-toolchain \
  tools/gate/witness/lake-manifest.json "$pkg/"
printf '%s\n' "axiom planted : (1 : Nat) = 2" \
  "theorem uses_planted : (1 : Nat) = 2 := planted" > "$pkg/GateWitness.lean"
( cd "$pkg" && lake build >/dev/null 2>&1 ) || { echo "witness: the witness package does not build"; exit 1; }

if ( cd "$pkg" && lake check ) > "$tmp/r1.log" 2>&1; then
  echo "witness: route 1 ACCEPTED the planted axiom"; fail=1
elif grep -q "Axiom 'planted' is not permitted" "$tmp/r1.log"; then
  echo "witness: route 1 refuses"
else
  echo "witness: route 1 failed for another reason: $(grep -m1 error "$tmp/r1.log")"; fail=1
fi

if ! ( cd "$pkg" && lake env leanexport GateWitness ) > "$tmp/w.ndjson" 2>/dev/null; then
  echo "witness: could not export the witness package"; fail=1
elif EXPORT_CHECK_ONLY="axioms nanoda" bash tools/gate/export-check.sh "$tmp/w.ndjson" > "$tmp/r2.log" 2>&1; then
  echo "witness: route 2 ACCEPTED the planted axiom"; fail=1
elif grep -q "^export-check: axioms REJECTS" "$tmp/r2.log" && grep -q "^export-check: nanoda REJECTS" "$tmp/r2.log"; then
  echo "witness: route 2 refuses"
else
  echo "witness: route 2 failed, but not on the axiom:"; cat "$tmp/r2.log"; fail=1
fi
exit "$fail"
