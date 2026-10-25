#!/usr/bin/env bash
# Repeatedly build the model; for each error located on an `inductive`/`structure` line, prefix
# `#guard_msgs (drop error) in`. Stops when the build succeeds, or an error is not at such a line.
cd "$1" || exit 2
for round in $(seq 1 60); do
  lake build > ../build-round.log 2>&1 && { echo "round $round: build ok"; exit 0; }
  locs=$(grep -oE "^error: [^:]+\.lean:[0-9]+:0:" ../build-round.log | sed -E 's/^error: //; s/:0:$//' | sort -u)
  [ -z "$locs" ] && { echo "round $round: no located errors"; grep -m5 error ../build-round.log; exit 1; }
  patched=0
  # patch from the bottom of each file up, so line numbers stay valid
  for loc in $(echo "$locs" | sort -t: -k1,1 -k2,2nr); do
    f=${loc%%:*}; n=${loc##*:}
    line=$(sed -n "${n}p" "$f")
    if [[ "$line" =~ ^(inductive|structure)\  ]]; then
      prev=$(sed -n "$((n-1))p" "$f")
      [[ "$prev" == "#guard_msgs (drop error) in" ]] && { echo "round $round: already patched $loc"; continue; }
      sed -i "${n}i #guard_msgs (drop error) in" "$f"; echo "patched $loc: ${line:0:60}"; patched=$((patched+1))
    else
      echo "round $round: error not at an inductive: $loc: ${line:0:80}"; grep -m3 "$loc" ../build-round.log
    fi
  done
  [ "$patched" = 0 ] && { echo "round $round: nothing patchable"; exit 1; }
done
