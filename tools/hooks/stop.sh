#!/usr/bin/env bash
# Stop: warn (never fail) when the session ends with uncommitted work. Stage K sat uncommitted
# from August to October; this makes the dirty tree visible at the moment it would be forgotten.
cd "$(git rev-parse --show-toplevel)" || exit 0
n=$(git status --porcelain | grep -v ' STATE.md$' | wc -l)
if [ "$n" -gt 0 ]; then
  printf '{"systemMessage": "certified-composition: %s uncommitted path(s). Commit, push to a wip/ branch, or record why it is abandoned (CLAUDE.md session protocol)."}\n' "$n"
fi
