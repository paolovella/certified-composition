#!/usr/bin/env bash
# S-USABLE S2 driver: run each generated read_*.lean under the profiler with a time cap, in its own process group,
# and append name, characters, kernel ms, elaboration ms, status and peak RSS to a tsv.
#   bash research/2026-11/usable/s2_run.sh SCRATCH OUT.tsv TIMEOUT m1 m2 ...   (from the repo root)
set -uo pipefail
S=$1; OUT=$2; T=$3; shift 3
mkdir -p "$S"
python3 research/2026-11/usable/s2_gen.py "$S" "$@" > "$S/names.txt" || exit 1
[ -f "$OUT" ] || printf 'text\tchars\tkernel_ms\telab_ms\tstatus\tmaxrss_kb\n' > "$OUT"
cd l-core
while read -r name chars; do
  log="$S/$name.out"
  setsid timeout --kill-after=10 "$T" /usr/bin/time -f 'MAXRSS %M' lake env lean -D autoImplicit=false "$S/$name.lean" > "$log" 2>&1
  rc=$?
  k=$(sed -n '/== read/,/== end/p' "$log" | grep -o 'type checking took [0-9.]*m\?s' | awk '{v=$4; if (v ~ /ms$/) {sub(/ms/,"",v)} else {sub(/s/,"",v); v*=1000}; t+=v} END {printf "%.0f", t}')
  e=$(sed -n '/== read/,/== end/p' "$log" | grep -o 'tactic execution of [A-Za-z.]* took [0-9.]*m\?s' | awk '{v=$NF; if (v ~ /ms$/) {sub(/ms/,"",v)} else {sub(/s/,"",v); v*=1000}; t+=v} END {printf "%.0f", t}')
  rss=$(grep -o 'MAXRSS [0-9]*' "$log" | tail -1 | cut -d' ' -f2)
  if [ "$rc" = 124 ] || [ "$rc" = 137 ]; then st="timeout ${T}s"; elif grep -q 'error' "$log"; then st="error: $(grep -m1 error "$log" | cut -c1-100)"; else st=ok; fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$name" "$chars" "$k" "$e" "$st" "${rss:--}" >> "../$OUT"
  echo "$name $chars chars: kernel ${k} ms, elab ${e} ms, $st"
done < "$S/names.txt"
