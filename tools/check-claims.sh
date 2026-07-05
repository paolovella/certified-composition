#!/usr/bin/env bash
# Guard against README/status drift: run after landing any tier or theorem.
# Exits nonzero if a known drift pattern reappears.
set -u
fail=0

# 1. Retired claims must not resurface — in ANY readme, including the top-level one
#    (the top-level README carried "remaining brick" for nine sessions because this
#    check originally skipped it).
for phrase in "is the remaining extension" "generalization is the next brick" \
              "remaining brick" "not yet formally linked" \
              "Dobrushin DPI built (finite)"; do
  if grep -qF "$phrase" README.md transport-calculus/README.md transport-kernel/README.md 2>/dev/null; then
    echo "DRIFT: retired phrase present: '$phrase'"; fail=1
  fi
done

# 1b. The top-level README must mention every tier-bearing module family and note file.
for name in DobrushinMeasureReceive tvDist_toMeasure QuantumDobrushinReceive \
            OmegaOneCoherent NOTES-coherent-escapee.md PROBLEM-dip-schedulability.md \
            reps_implies_trivial; do
  if ! grep -q "$name" README.md; then
    echo "DRIFT: top-level README does not mention $name"; fail=1
  fi
done

# 2. Every transport-kernel Lean module must be mentioned in its README.
for f in transport-kernel/TransportKernel/*.lean; do
  base=$(basename "$f")
  if ! grep -q "$base" transport-kernel/README.md; then
    echo "DRIFT: $base not mentioned in transport-kernel/README.md"; fail=1
  fi
done

# 3. Every research-note/problem file must be mentioned in transport-calculus/README.md.
for f in transport-calculus/NOTES-*.md transport-calculus/PROBLEM-*.md; do
  base=$(basename "$f")
  if ! grep -q "$base" transport-calculus/README.md; then
    echo "DRIFT: $base not mentioned in transport-calculus/README.md"; fail=1
  fi
done

# 4. Same for transport-kernel notes.
for f in transport-kernel/NOTES-*.md; do
  [ -e "$f" ] || continue
  base=$(basename "$f")
  if ! grep -q "$base" transport-kernel/README.md; then
    echo "DRIFT: $base not mentioned in transport-kernel/README.md"; fail=1
  fi
done

[ $fail -eq 0 ] && echo "check-claims: clean"
exit $fail
