#!/usr/bin/env bash
# The boundary warden (P0-12): an agent reads how far the checkers have drifted since the
# user's last sign-off and may escalate. It can only escalate: `clear` grants nothing the
# mechanical gate (tools/gate/base-gate.sh) did not, and `escalate` or a malformed answer makes
# the change need the user's key.
#
#   tools/gate/warden.sh BASE_DIR PR_DIR [OUT_DIR]
#
# Runs only when the PR changes tools/checkers.lock; otherwise it says so and passes. The
# prompt is BASE's .claude/agents/boundary-warden.md, so a PR cannot rewrite its reviewer. The
# agent is `claude -p` with Read, Grep and Glob only, in --restricted mode (the PR's settings
# and hooks are not loaded), and --bare when ANTHROPIC_API_KEY is set. With
# CLAUDE_CODE_OAUTH_TOKEN instead (a subscription token, `claude setup-token`) it runs without
# --bare, which accepts only an API key; --restricted still keeps the PR's settings out. It never executes
# PR code, which is why the workflow can give this job the key and not the build job.
# The report and the answer are kept in OUT_DIR (default: a temporary directory).
set -uo pipefail
[ $# -ge 2 ] || { echo "usage: warden.sh BASE_DIR PR_DIR [OUT_DIR]"; exit 2; }
base=$(cd "$1" && pwd) && pr=$(cd "$2" && pwd) || exit 2
here=$(dirname "$(readlink -f "$0")")
if [ -n "${3:-}" ]; then out=$3; mkdir -p "$out"; out=$(cd "$out" && pwd)
else out=$(mktemp -d); trap 'rm -rf "$out"' EXIT; fi
bash "$here/boundary-report.sh" "$base" "$pr" > "$out/report.txt" 2>&1
rc=$?
head -1 "$out/report.txt"
[ "$rc" = 0 ] || { echo "warden: the report failed, counted as escalate"; exit 1; }
if head -1 "$out/report.txt" | grep -q ", 0 changed by this PR$"; then
  echo "warden: this PR changes no checker; not run"
  exit 0
fi
# the workflow sets WARDEN_NO_AGENT when it may not run the agent (a fork, no key)
[ -z "${WARDEN_NO_AGENT:-}" ] || { echo "warden: ABSENT ($WARDEN_NO_AGENT), counted as escalate"; exit 1; }
agent="$base/.claude/agents/boundary-warden.md"
[ -f "$agent" ] || { echo "warden: ABSENT (no $agent on the base)"; exit 1; }
command -v claude >/dev/null || { echo "warden: ABSENT (claude CLI not installed), counted as escalate"; exit 1; }
# the agent's instructions without the frontmatter
awk 'NR == 1 && /^---$/ {f=1; next} f && /^---$/ {f=0; next} !f' "$agent" > "$out/prompt.md"
flags=(-p --restricted --tools "Read,Grep,Glob" --strict-mcp-config --add-dir "$out"
       --model "${WARDEN_MODEL:-claude-opus-5-5}" --append-system-prompt-file "$out/prompt.md")
[ -n "${ANTHROPIC_API_KEY:-}" ] && flags+=(--bare)
( cd "$pr" && timeout "${WARDEN_TIMEOUT:-1800}" claude "${flags[@]}" \
    "Review the boundary report at $out/report.txt. The change's tree is the working directory. End with the verdict line." \
) > "$out/answer.txt" 2> "$out/stderr.txt"
echo "warden: agent exited $?; answer in $out/answer.txt"
bash "$here/warden-verdict.sh" "$out/answer.txt"
