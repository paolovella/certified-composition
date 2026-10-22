#!/usr/bin/env bash
# SessionStart: regenerate and print STATE.md so every session begins from the repo's real state
# (dirty tree, jobs without end receipts, backlog), not from memory of the last session.
cd "$(git rev-parse --show-toplevel)" || exit 0
bash tools/render-state.sh >/dev/null 2>&1 && cat STATE.md
