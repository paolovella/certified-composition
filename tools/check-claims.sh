#!/usr/bin/env bash
# Guard against README/status drift: run after landing any tier or theorem.
# Exits nonzero if a known drift pattern reappears.
set -u
fail=0

# 1. Claims retired by transport-kernel tiers 3b/3c must not resurface.
for phrase in "is the remaining extension" "generalization is the next brick" \
              "not yet formally linked"; do
  if grep -qF "$phrase" transport-calculus/README.md transport-kernel/README.md 2>/dev/null; then
    echo "DRIFT: retired phrase present: '$phrase'"; fail=1
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
