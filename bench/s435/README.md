# S-435 artifacts (Lean v4.31.0 → v4.35.0)

The evidence behind `backlog/S-435.md` and `bench/s435.tsv`, kept so P0-02 can start from it.
Everything here was produced on a scratch copy of the two mathlib-free packages with both
`lean-toolchain` files set to `leanprover/lean4:v4.35.0`. Nothing here is built by CI.

| file | what |
|---|---|
| `pleak-fix.patch` | the one source change 4.35 needs to build `conf-typing` |
| `pin-beq-int.patch` | experiment B: pin `BEq Int` to the 4.31 instance in `Imp.lean` |
| `axioms-4.35.txt` | `AxiomManifest.lean` output under 4.35 with the Pleak fix (experiment A) |
| `axioms-4.35-pinned.txt` | the same with the pin as well (experiment B) |
| `AxiomsBlocked.lean` | footprint collector that treats named constants as opaque; with an empty set it reproduces `collectAxioms` exactly |
| `AxPath.lean` | prints a shortest dependency path from a declaration to an axiom |
| `nanoda.json` | nanoda config used directly (replace `S435_DIR`); ~~run with `RUST_MIN_STACK=1073741824`~~ run with `ulimit -s unlimited` and one thread (corrected in `backlog/S-435.md`) |
| `tsv.py` | regenerates `bench/s435.tsv` from the receipts' logs and the two manifests |

Reproduce: copy `transport-calculus/` and `conf-typing/` side by side (no `.lake`), set the
toolchains, apply `pleak-fix.patch`, `lake build ConfTyping`, then
`lake env lean AxiomManifest.lean` and diff with `tools/axioms.expected`. The `.lean` files here
go next to `AxiomManifest.lean` in the copy. `tsv.py` expects `axA.txt` and `axB.txt` (the two
manifests) in the directory it is given, and the `s435b-*` logs, which are not tracked.
