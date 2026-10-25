#!/usr/bin/env bash
# S-SAIL: the changes that make opencompl/sail-riscv-lean 51c635c460 build under Lean v4.35.0.
# Run on a fresh clone of that commit: bash apply-435.sh DIR [--opaque]
#
#  1. toolchain v4.35.0, and lean-sail moved from v5 (0794631345) to 01bb54c7c8, five commits
#     on that only add code, the last providing `sail_assert`.
#  2. every call `assert c "msg"` becomes `sail_assert c "msg"`: 4.35 parses `assert` differently
#     ("Function expected"), and newer Sail emits `sail_assert` for this reason.
#  3. `instruction` has 353 constructors; 4.35 refuses to generate code for a constructor with
#     fields whose tag is above the runtime limit, and the two inductives that contain it then fail
#     too. The model is never run, so those three code-generation errors are dropped. The kernel
#     still checks the declarations.
#  --opaque: the 75 `axiom` declarations in RiscvExtras.lean (platform hooks: softfloat,
#     terminal, reservations, random bits, config flags) become `opaque`, so nothing is assumed.
set -euo pipefail
d=$1
cd "$d"
echo leanprover/lean4:v4.35.0 > lean-toolchain
sed -i 's/^rev = "v5"$/rev = "01bb54c7c8a69e52ba11863c67e7c403a6cd198a"/' lakefile.toml
lake update Sail >/dev/null
grep -rl "assert" LeanRV64D | xargs perl -pi -e \
  's/(?<![A-Za-z0-9_.«"])assert (?=\S)/sail_assert /g; s/PreSail\.assert p s/PreSail.sail_assert p s/'
for t in instruction ExecutionResult Step; do
  sed -i "s/^inductive $t where\$/#guard_msgs (drop error) in\ninductive $t where/" LeanRV64D/Defs.lean
done
[ "${2:-}" = --opaque ] && sed -i 's/^axiom /opaque /' LeanRV64D/RiscvExtras.lean
echo "apply-435: done"
