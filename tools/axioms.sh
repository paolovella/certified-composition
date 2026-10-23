#!/usr/bin/env bash
# Regenerate the axiom manifest from the built code, or check that the committed one is current.
#   tools/axioms.sh          rewrite tools/axioms.expected
#   tools/axioms.sh --check  fail (and show the diff) if tools/axioms.expected is stale
# A stale manifest would let tools/axiom-claims.py confirm doc claims against old footprints,
# which is the "checked once, believed forever" failure the manifest exists to end.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
fresh=$(mktemp)
trap 'rm -f "$fresh"' EXIT
( cd conf-typing && lake env lean AxiomManifest.lean ) > "$fresh"
if [ "${1:-}" = "--check" ]; then
  if ! diff -u tools/axioms.expected "$fresh"; then
    echo "axioms: tools/axioms.expected is stale; run tools/axioms.sh and review the diff"
    exit 1
  fi
  echo "axioms: manifest current ($(wc -l < "$fresh") declarations)"
else
  cp "$fresh" tools/axioms.expected
  echo "axioms: wrote tools/axioms.expected ($(wc -l < "$fresh") declarations)"
fi
