#!/usr/bin/env bash
# Everything that must hold before a commit is honest. The CI workflow calls this and
# nothing else, so what runs on push is exactly what runs locally -- the two cannot drift.
#
#   tools/ci.sh                  full run (includes the mathlib package; slow)
#   tools/ci.sh --fast           skip transport-kernel (mathlib), for the inner loop
#   tools/ci.sh --require-heavy  full run on the heavy runner: an absent tool is a failure
#   tools/ci.sh --quick          the inner loop (F1): --fast, and the slow witnesses deferred.
#                                Every deferred step is printed; it is never merge evidence.
#
# A step that does not run is never silent (P0-06): it prints DEFERRED or ABSENT with the
# reason, and the last line lists every step not run.
set -uo pipefail
cd "$(dirname "$0")/.."

FAST=0; HEAVY=0; QUICK=0
for a in "$@"; do
  case "$a" in
    --fast) FAST=1 ;;
    --quick) QUICK=1; FAST=1 ;;
    --require-heavy) HEAVY=1 ;;
    *) echo "ci.sh: unknown option $a"; exit 2 ;;
  esac
done
[ "$FAST" = 1 ] && [ "$HEAVY" = 1 ] && { echo "ci.sh: --fast or --quick and --require-heavy contradict"; exit 2; }
# The steps --quick defers: the slow witnesses and the external kernels (F1 baseline, 2026-10-29:
# together ~390 s of the ~614 s full run). The full run and the gate still run all of them.
QUICK_DEFER=$'lake check from the root workspace (route 1)\nring0.lock catches what the comparator cannot (witness)\nexport accepted by all six kernels (route 2)\nboth kernel gates refuse a planted axiom (witness)\nwalk-check (numeric claims in the notes)'

fail=0
notrun=()
# Per-step seconds (F1): every step's time, status and name, printed slowest first at the end
# and written to $RUNJOB_STEPS when tools/run-job.sh runs this, so the receipt says where the
# time went.
times=()
nobudget=0
step() {
  local name="$1" st t0; shift
  if [ "$QUICK" = 1 ] && grep -qxF "$name" <<< "$QUICK_DEFER"; then
    not_run "$name" DEFERRED "--quick; the full run and the gate run it"; return
  fi
  printf '\n=== %s\n' "$name"
  t0=$(date +%s)
  if "$@"; then st=ok; else st=FAILED; fail=1; fi
  local dt=$(( $(date +%s) - t0 )) bmsg brc
  # The time ratchet (tools/ci-budget.sh): on a machine with budgets, a step over its budget,
  # or with none, fails; a machine without budgets is reported at the end.
  if [ "$st" = ok ]; then
    bmsg=$(bash tools/ci-budget.sh check "$name" "$dt"); brc=$?
    if [ "$brc" = 1 ]; then st="FAILED ($bmsg)"; fail=1
    elif [ "$brc" = 3 ]; then nobudget=1; fi
  fi
  printf '    %s (%d s)\n' "$st" "$dt"
  times+=("$dt"$'\t'"$st"$'\t'"$name")
}
# not_run <step> <DEFERRED|ABSENT> <reason>: an ABSENT tool fails under --require-heavy.
not_run() {
  printf '\n=== %s\n    %s: %s\n' "$1" "$2" "$3"
  if [ "$2" = ABSENT ] && [ "$HEAVY" = 1 ]; then printf '    FAILED\n'; fail=1; fi
  notrun+=("$1")
  times+=("0"$'\t'"$2"$'\t'"$1")
}

build() {  # build a lake package, succeed only on a clean build
  local dir="$1"
  ( cd "$dir" && lake build 2>&1 | tail -3 | grep -q "Build completed successfully" )
}

step "conf-typing builds"          build conf-typing
step "transport-calculus builds"   build transport-calculus
if [ "$FAST" = 0 ]; then
  step "transport-kernel builds (mathlib)" build transport-kernel
else
  not_run "transport-kernel builds (mathlib)" DEFERRED "--fast; the full run and the heavy runner build it"
fi

# The stage D combinator is an executable, so `lake build` on the library does not cover
# it. Build it and run it on the emission corpus: a parser that stops parsing real bytes
# is the one failure the Lean samples cannot catch.
step "certcompose builds and consumes the emission" \
     bash -c 'cd conf-typing && lake build certcompose >/dev/null 2>&1 &&
              ./.lake/build/bin/certcompose corpus/jasmin/accept.expected \
                | grep -q "^  SCT level:  #secret"'

# The cross-check crate is an independent re-implementation used as an adversary. Its
# concrete witnesses are cheap and must not rot; the Kani harnesses are minutes-long and are
# run by hand, not here. Without cargo the step is reported ABSENT, so the Lean gates still run.
if command -v cargo >/dev/null 2>&1; then
  step "cross-check witnesses (independent Rust port)" \
       bash -c 'cd cross-check/leak-kani && cargo test --quiet 2>&1 | grep -q "test result: ok"'
else
  not_run "cross-check witnesses (independent Rust port)" ABSENT "cargo not on PATH"
fi

# Stage K's verified checker. Verus is not assumed present (it is not on PATH by default
# here); when it is, the file must verify and the binary must still decide correctly.
VERUS_BIN="${VERUS:-/home/paolo/verus/verus-bin/verus-x86-linux/verus}"
if [ -x "$VERUS_BIN" ]; then
  step "verus lcheck verifies and runs" \
       bash -c 'cd cross-check/verus && "'"$VERUS_BIN"'" --compile lcheck.rs -o lcheck-bin 2>&1 \
                  | grep -q "0 errors" &&
                ./lcheck-bin > /tmp/lcheck-verdicts.txt &&
                grep -q "^alloc p ; free p .*ACCEPT" /tmp/lcheck-verdicts.txt &&
                grep -q "^alloc p  *REFUSE"          /tmp/lcheck-verdicts.txt &&
                grep -q "^b06 (CWE-401) *REFUSE"     /tmp/lcheck-verdicts.txt &&
                grep -q "^b06, repaired *ACCEPT"     /tmp/lcheck-verdicts.txt &&
                grep -q "^while c { alloc x } *REFUSE"          /tmp/lcheck-verdicts.txt &&
                grep -q "^while c { alloc x ; free x } *ACCEPT" /tmp/lcheck-verdicts.txt'
else
  not_run "verus lcheck verifies and runs" ABSENT "no Verus at $VERUS_BIN"
fi

# certcheck is the tool the README tells a reader to run (P0-06). Each documented example must
# get the verdict the README states: the accepted one exits 0, each rejected one exits 3 and
# names its checker. The two secret examples need `--secret pw`; without it, secret-branch.uc
# is accepted (correction of record in README.md).
certcheck_examples() (  # a subshell: the cd must not leak into the steps after it
  cd conf-typing && lake build certcheck >/dev/null 2>&1 || return 1
  local b=./.lake/build/bin/certcheck out rc
  out=$("$b" examples/handler.uc); rc=$?
  [ "$rc" = 0 ] && echo "$out" | grep -q "^examples/handler.uc: ACCEPTED$" || { echo "    handler.uc: exit $rc"; return 1; }
  local ex flag want
  for ex in injection:string-integrity unmediated:certificate use-after-free:certificate \
            unbounded-loop:certificate secret-leak:certificate secret-branch:certificate; do
    want=${ex#*:}; ex=${ex%%:*}; flag=()
    case "$ex" in secret-*) flag=(--secret pw) ;; esac
    out=$("$b" "examples/rejected/$ex.uc" "${flag[@]}" 2>&1); rc=$?
    [ "$rc" = 3 ] && echo "$out" | grep -q ": REJECTED by the $want checker" \
      || { echo "    $ex.uc: exit $rc, $(echo "$out" | head -1)"; return 1; }
  done
)
step "certcheck gives every documented example its verdict" certcheck_examples

# The two kernel gates (P0-02). Route 1: `lake check` from the repo-root workspace builds,
# exports and replays everything inside a bwrap sandbox and refuses any non-standard axiom.
# Without a usable bwrap it cannot run, and that is a failure with its reason, not a skip.
lake_check() {
  if ! command -v bwrap >/dev/null 2>&1 || ! bwrap --ro-bind / / true >/dev/null 2>&1; then
    echo "    ABSENT: bwrap missing or unprivileged user namespaces disabled; lake check cannot run"
    return 1
  fi
  # The exit code is the verdict: on a refused axiom lake check still prints "Lean default kernel
  # accepts" after its error, so grepping its output would pass a refusal.
  lake build >/dev/null 2>&1 && lake check >/dev/null 2>&1
}
step "lake check from the root workspace (route 1)" lake_check
# The frozen statements (P0-03). `lake comparator` builds and exports inside the same bwrap sandbox,
# where only the root .lake is writable, so the tree is built first. It must accept the real
# solution and refuse a weakened one; ring0.lock covers what it cannot see, an edited definition.
lake_comparator() {
  if ! command -v bwrap >/dev/null 2>&1 || ! bwrap --ro-bind / / true >/dev/null 2>&1; then
    echo "    ABSENT: bwrap missing or unprivileged user namespaces disabled; lake comparator cannot run"
    return 1
  fi
  lake build StatementsProof >/dev/null 2>&1 && lake comparator >/dev/null 2>&1
}
step "frozen statements: lake comparator accepts the solution" lake_comparator
check_baseline() {
  [ -f tools/checkers.baseline ] || return 1
  sed -n '1p' tools/checkers.baseline | grep -qE $'^baseline\t[0-9a-f]{40}$' || return 1
  # every checker the baseline covers is one ring0.lock lists, and the reverse
  diff <(tail -n +2 tools/checkers.baseline | cut -f2 | LC_ALL=C sort -u) \
       <(sed -n $'s/^checkers\t[0-9]*\t//p' tools/ring0.lock | tr ' ' '\n' | LC_ALL=C sort -u) >/dev/null
}
step "frozen statements: the comparator refuses a weakened solution (witness)" \
     bash -c 'bash tools/gate/comparator-witness.sh | tail -1 | grep -qx "comparator witnesses: 2 passed, 0 failed"'
step "ring0.lock is current"       bash tools/ring0-lock.sh --check
step "ring0.lock catches what the comparator cannot (witness)" \
     bash -c 'bash tools/gate/ring0-lock-witness.sh | tail -1 | grep -qx "ring0.lock witnesses: 5 passed, 0 failed"'
# P0-12: the boundary warden's mechanical half (verdict parser, drift report). The agent runs in
# the gate workflow's warden job; its live witnesses are `warden-witness.sh --live`.
step "checkers.baseline names a commit and the checkers ring0.lock lists" check_baseline
step "boundary warden: parser and drift report (witness)" \
     bash -c 'bash tools/gate/warden-witness.sh | tail -1 | grep -qx "warden witnesses: 9 passed, 0 failed"'

# Route 2: the export replayed through all six bundled kernels, each run directly
# (tools/gate/export-check.sh says why not `lake check --paranoid`).
step "export accepted by all six kernels (route 2)" \
     bash -c 'bash tools/gate/export-check.sh | tail -1 | grep -q "^export-check: all kernels accept$"'
# ...and both refuse a planted axiom: without this, the two steps above would also pass for gates
# that accept everything.
step "both kernel gates refuse a planted axiom (witness)" \
     bash -c 'bash tools/gate/witness.sh | grep -c "refuses$" | grep -qx 2'
# The base-branch gate's own rules (Ring 0 classifier, manifest additions only), each with an
# accepted and a refused PR. The two cases that run ci.sh are --full, outside ci.sh: inside it
# they would recurse.
step "base gate: ring0 and manifest rules accept and refuse (witness)" \
     bash -c 'bash tools/gate/base-gate-witness.sh | tail -1 | grep -qE "^base-gate witnesses: 21 passed, 0 failed$"'

# `sorry` is allowed in exactly one file, the frozen-statement challenge (P0-03); check-claims (k)
# polices that file.
step "no sorry in our sources"     bash -c '! git ls-files "*.lean" | grep -vxF workspace/Statements.lean | xargs grep -n "\\bsorry\\b"'
step "axiom manifest is current"   bash tools/axioms.sh --check
# P0-04: every checker has an accepted and a refused witness, computed from the environment;
# and the registry itself both counts and misses (registry-witness.sh).
step "witness registry: every checker accepts and refuses" bash tools/witnesses.sh --check
step "witness registry finds what is missing (witness)" \
     bash -c 'bash tools/gate/registry-witness.sh | tail -1 | grep -qx "registry witnesses: 4 passed, 0 failed"'
# P0-05: every mechanical rule mutant of every checker is killed, and the per-site verdicts match
# tools/mutants.expected. A few minutes, so the full run and the heavy runner only.
if [ "$FAST" = 0 ]; then
  step "rule mutants: every one killed, table current" python3 tools/mutants.py --check --jobs 4
  step "rule mutants: the runner finds a survivor (witness)" \
       bash -c 'bash tools/gate/mutants-witness.sh | tail -1 | grep -qx "mutant runner witnesses: 2 passed, 0 failed"'
else
  not_run "rule mutants: every one killed, table current" DEFERRED "--fast; the full run and the heavy runner run them"
fi
budget_witness() (  # accepted and refused cases of the time ratchet, on a planted budget file
  t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
  printf 'budget\tstep\n10\tplanted step\n' > "$t/b.tsv"
  c() { CI_BUDGET_FILE="$1" bash tools/ci-budget.sh check "$2" "$3" >/dev/null; echo $?; }
  [ "$(c "$t/b.tsv" "planted step" 10)" = 0 ] &&      # at the budget: accepted
  [ "$(c "$t/b.tsv" "planted step" 11)" = 1 ] &&      # over it: refused
  [ "$(c "$t/b.tsv" "unbudgeted step" 1)" = 1 ] &&    # a step with no budget: refused
  [ "$(c "$t/none.tsv" "planted step" 1)" = 3 ]       # a machine with none: reported
)
step "time budgets accept and refuse (witness)" budget_witness
step "check-claims (drift guards)" bash -c 'bash tools/check-claims.sh | tail -1 | grep -q "^check-claims: clean$"'
step "guard-selftest (the guards actually fire)" \
     bash -c 'bash tools/guard-selftest.sh | tail -1 | grep -qE "^guard self-test: [0-9]+ passed, 0 failed$"'
step "walk-check (numeric claims in the notes)" \
     bash -c 'python3 tools/walk-check.py | tail -1 | grep -q "^all checks PASS$"'

printf '\n--- seconds per step, slowest first\n'
table=$(printf '%s\n' "${times[@]}" | sort -t$'\t' -k1,1nr)
printf '%s\n' "$table" | awk -F'\t' '{ printf "  %6s s  %-8s %s\n", $1, $2, $3 }'
if [ -n "${RUNJOB_STEPS:-}" ]; then
  { printf 'seconds\tstatus\tstep\n'; printf '%s\n' "$table"; } > "$RUNJOB_STEPS"
fi

[ "$nobudget" = 1 ] && printf '\nTIME BUDGET: none for host %s; step times were not checked\n' "$(bash tools/ci-budget.sh host)"

printf '\n'
nr=""
[ "${#notrun[@]}" -gt 0 ] && nr="; ${#notrun[@]} not run: $(IFS=';'; echo "${notrun[*]}" | sed 's/;/; /g')"
[ "$QUICK" = 1 ] && printf 'CI: quick tier, not merge evidence\n'
if [ "$fail" = 0 ]; then printf 'CI: all steps that ran passed%s\n' "$nr"; else printf 'CI: FAILURES ABOVE%s\n' "$nr"; fi
exit "$fail"
