#!/usr/bin/env bash
# PreToolUse(Bash): refuse a command that both edits via heredoc and commits. That shape is how
# CHANGELOG edits failed twice while the commit still landed (memory: changelog-anchor-failure-mode):
# the edit and the commit must be separate calls, so the edit's result is seen before committing.
python3 -I -c '
import json, sys
cmd = json.load(sys.stdin).get("tool_input", {}).get("command", "")
if "<<" in cmd and "git commit" in cmd:
    print(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PreToolUse",
        "permissionDecision": "deny",
        "permissionDecisionReason": "certified-composition house rule: do not heredoc-edit and git commit in one command; run the edit, check it, then commit separately (CLAUDE.md, Edits)."}}))
'
