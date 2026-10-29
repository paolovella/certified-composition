#!/usr/bin/env bash
# Gate route 2 (P0-02): export the root workspace and replay the export through every kernel the
# toolchain bundles, each run directly.
#
#   tools/gate/export-check.sh [EXPORT.ndjson]   (run from anywhere; exports if no file is given)
#
# Why not `lake check --paranoid`: Lean 4.35's Lake runs nanoda with `num_threads: 4` and a cleared
# environment, and on conf-typing nanoda's worker threads overflow their stacks whatever
# RUST_MIN_STACK says. One thread with an unlimited main stack checks it (S-435, P0-02 Log). Route 1
# (`lake check` from the repo root, in its sandbox) stays the primary gate; this route adds the
# five external kernels.
#
# Limit, stated where the gate is: an accepted export shows the export is well-typed with the
# allowed axioms. It does not show the export is this project. Here the export is built by this
# script from the checked-out tree, outside the sandbox.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
bin="$(lake env printenv LEAN_SYSROOT 2>/dev/null || dirname "$(dirname "$(elan which lean)")")/bin"
[ -x "$bin/leanchecker-paranoid" ] || { echo "export-check: ABSENT: bundled checkers not found in $bin"; exit 2; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
exp="${1:-}"
if [ -z "$exp" ]; then
  exp="$tmp/export.ndjson"
  lake build >/dev/null 2>&1 || { echo "export-check: root workspace does not build"; exit 1; }
  lake env leanexport CertifiedComposition > "$exp" || { echo "export-check: leanexport failed"; exit 1; }
fi
cat > "$tmp/nanoda.json" <<EOF
{"export_file_path": "$exp", "use_stdin": false,
 "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
 "unpermitted_axiom_hard_error": false, "num_threads": 1,
 "nat_extension": true, "string_extension": true, "print_success_message": true}
EOF
fail=0
# EXPORT_CHECK_ONLY="axioms nanoda" restricts the run to those checks; only the refused witness
# (tools/gate/witness.sh) uses it, and the real gate never sets it.
only="${EXPORT_CHECK_ONLY:-}"
# The kernels are independent readers of one export, so they run side by side (F1): the step
# takes as long as the slowest kernel (lean4lean, ~73 s on the WSL box), not the sum (~265 s).
# Peak memory together is ~7 GB (nanoda ~3 GB). Each verdict is still its own exit code, and
# the verdicts are printed in this fixed order once all have finished.
names=()
run() {  # run NAME cmd...: one kernel, in the background; its verdict is its exit code
  local name="$1"; shift
  if [ -n "$only" ] && [[ " $only " != *" $name "* ]]; then return; fi
  names+=("$name")
  ( "$@" > "$tmp/$name.log" 2>&1; echo $? > "$tmp/$name.rc" ) &
}
run axioms       python3 tools/gate/export-axioms.py "$exp"
run lean         "$bin/leanchecker" --silent --from-export "$exp"
run paranoid     "$bin/leanchecker-paranoid" --silent --from-export "$exp"
run lean4lean    "$bin/lean4lean" --import "$exp"
run nanoda       bash -c 'ulimit -s unlimited && exec "$0" "$1"' "$bin/nanoda_bin" "$tmp/nanoda.json"
run con-leche    "$bin/con-leche" "$exp"
run con-ron      "$bin/con-ron" "$exp"
wait
for name in "${names[@]}"; do
  rc=$(cat "$tmp/$name.rc" 2>/dev/null || echo "no verdict")
  if [ "$rc" = 0 ]; then echo "export-check: $name accepts"
  else echo "export-check: $name REJECTS (exit $rc): $(tail -1 "$tmp/$name.log")"; fail=1; fi
done
[ "$fail" = 0 ] && [ -z "$only" ] && echo "export-check: all kernels accept"
exit "$fail"
