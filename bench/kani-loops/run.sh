#!/usr/bin/env bash
# P0-08: run every split cell of the Kani loop search (cross-check/leak-kani, mod split), each
# through tools/run-job.sh with a time cap, JOBS at a time, and write bench/kani-loops.tsv.
#   bash bench/kani-loops/run.sh [CAP_SECONDS] [JOBS]
#   bash bench/kani-loops/run.sh --summarize   only rebuild the table from the existing receipts
#   bash bench/kani-loops/run.sh [--summarize] --seq    the seq root's 16 sub-cells (bench/kani-loops-seq.tsv)
#   bash bench/kani-loops/run.sh [--summarize] --cover  the two covering harnesses (bench/kani-loops-cover.tsv)
# The compound-root cells (seq, ite, loop) need several GB each: three at once exhausted 23 GB
# (2026-10-26). Run them one at a time.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
ROOT=$(pwd)
SUMMARIZE=0; [ "${1:-}" = --summarize ] && { SUMMARIZE=1; shift; }
SEQ=0; [ "${1:-}" = --seq ] && { SEQ=1; shift; }   # the seq root cut by its children (l, r)
COVER=0; [ "${1:-}" = --cover ] && { COVER=1; shift; }   # the cells exhaust well_formed
CAP=${1:-3600}
JOBS=${2:-1}
# a per-cell address-space cap (18 GB of the 23 GB machine), so a cell that needs more fails by
# itself instead of starving the session
MEMKB=${MEMKB:-18000000}
tags="skip alloc free assign load check seq ite loop"
cells=()
if [ "$COVER" = 1 ]; then
  cells=(cells_cover seq_cells_cover)
elif [ "$SEQ" = 1 ]; then
  for l in 1 2 3 4; do for r in 1 2 3 4; do cells+=("no_leak_seq_l${l}_r${r}" "can_alloc_seq_l${l}_r${r}"); done; done
else
  for t in $tags; do cells+=("no_leak_$t" "can_alloc_$t" "leaks_$t"); done
fi

one() {  # one HARNESS: run it with receipts; the log is the job's
  local h=$1
  RUNJOB_ROOT="$ROOT" tools/run-job.sh "p008-kani-$h" -- bash -c \
    "cd '$ROOT/cross-check/leak-kani' && ulimit -v $MEMKB && timeout $CAP cargo kani --harness split::$h 2>&1 \
       | grep -E 'VERIFICATION|Runtime Symex|Runtime Solver|VCC|Failed Checks|Complete'" >/dev/null
}
export -f one; export ROOT CAP MEMKB
if [ "$SUMMARIZE" = 0 ]; then
  ( cd cross-check/leak-kani && cargo kani --only-codegen >/dev/null 2>&1 ) || true
  printf '%s\n' "${cells[@]}" | xargs -P "$JOBS" -I{} bash -c 'one {}'
fi

out=bench/kani-loops.tsv; [ "$SEQ" = 1 ] && out=bench/kani-loops-seq.tsv; [ "$COVER" = 1 ] && out=bench/kani-loops-cover.tsv
printf 'cell\troot\tverdict\tmeaning\tsymex_s\tvccs_after_simplification\tsolver_s\twall_s\treceipt\n' > "$out"
for h in "${cells[@]}"; do
  log="tools/receipts/p008-kani-$h.log"; end="tools/receipts/p008-kani-$h.end"
  root=${h#*_}; root=${root#*_}; [ "$SEQ" = 0 ] && root=${h##*_}; [ "$COVER" = 1 ] && root=-
  symex=$(grep -oE 'Runtime Symex: [0-9.]+' "$log" 2>/dev/null | awk '{s+=$3} END {printf "%.1f", s}')
  vccs=$(grep -oE '[0-9]+ remaining after simplification' "$log" 2>/dev/null | awk '{s+=$1} END {print s+0}')
  solver=$(grep -oE 'Runtime Solver: [0-9.]+' "$log" 2>/dev/null | awk '{s+=$3} END {printf "%.1f", s}')
  if [ ! -f "$end" ]; then v="NOT RUN"; wall=""
  else
    wall=$(sed -n 's/^seconds: //p' "$end")
    if grep -q "VERIFICATION:- SUCCESSFUL" "$log"; then v=SUCCESSFUL
    elif grep -q "VERIFICATION:- FAILED" "$log"; then v=FAILED
    else v="NO VERDICT ($(sed -n 's/^exit: //p' "$end"))"; fi
  fi
  case "$h:$v" in
    no_leak_*:SUCCESSFUL) m="no accepted program with this root leaks" ;;
    no_leak_*:FAILED)     m="COUNTEREXAMPLE: leakSafe accepts a leaking program" ;;
    can_alloc_*:FAILED)   m="witness found: an accepted program with this root allocates" ;;
    can_alloc_*:SUCCESSFUL) m="no accepted program with this root allocates" ;;
    leaks_*:FAILED)       m="witness found: a program with this root leaks" ;;
    leaks_*:SUCCESSFUL)   m="no program with this root leaks" ;;
    *cells_cover:SUCCESSFUL) m="the cells cover every well_formed program" ;;
    *cells_cover:FAILED)  m="GAP: a well_formed program falls outside the cells" ;;
    *) m="open" ;;
  esac
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$h" "$root" "$v" "$m" "$symex" "$vccs" "$solver" "$wall" "p008-kani-$h" >> "$out"
done
column -t -s $'\t' "$out"
