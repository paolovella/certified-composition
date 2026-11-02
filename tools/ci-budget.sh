#!/usr/bin/env bash
# Per-step time budgets for tools/ci.sh (F1), so CI time cannot grow unnoticed.
#
#   tools/ci-budget.sh check STEP SECONDS   exit 1 if STEP took longer than its budget;
#                                           exit 3 (and say so) if this machine has no budgets
#   tools/ci-budget.sh write RECEIPT.steps  write this machine's budgets from a timed run
#   tools/ci-budget.sh host                 print the key this machine's budgets are filed under
#
# Budgets are per machine (tools/ci-budget/<host>.tsv): a hosted GitHub runner is not the WSL
# box. A machine with no budget file is reported by ci.sh, never treated as within budget.
# A budget is max(ceil(1.3 x seconds), seconds + 15): two identical runs on the WSL box agreed
# within 6% on every step over 10 s (F1 log), and steps under 5 s vary by whole seconds, which
# the 15 s floor absorbs. Raising a budget is a change to a data file and says why.
set -uo pipefail
cd "$(dirname "$0")/.."
host="${CI_BUDGET_HOST:-$(hostname)}"
file="${CI_BUDGET_FILE:-tools/ci-budget/$host.tsv}"

case "${1:-}" in
  host) echo "$host" ;;
  check)
    step="$2"; secs="$3"
    [ -f "$file" ] || { echo "no budgets for host $host"; exit 3; }
    b=$(awk -F'\t' -v s="$step" 'NR > 1 && $2 == s { print $1 }' "$file")
    [ -n "$b" ] || { echo "no budget for this step on $host"; exit 1; }
    if [ "$secs" -gt "$b" ]; then echo "over budget: $secs s > $b s"; exit 1; fi
    echo "within budget ($b s)" ;;
  write)
    steps="$2"
    mkdir -p "$(dirname "$file")"
    { printf 'budget\tstep\n'
      awk -F'\t' 'NR > 1 && $2 == "ok" {
        a = int($1 * 1.3 + 0.999); b = $1 + 15; printf "%d\t%s\n", (a > b ? a : b), $3 }' "$steps" \
        | sort -t$'\t' -k2
    } > "$file"
    echo "ci-budget: wrote $file from $steps" ;;
  *) echo "usage: tools/ci-budget.sh check STEP SECONDS | write RECEIPT.steps | host" >&2; exit 2 ;;
esac
