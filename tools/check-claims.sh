#!/usr/bin/env bash
# Guard against README/status drift: run after landing any tier or theorem.
# Exits nonzero if a known drift pattern reappears.
set -u
fail=0

# 1. Retired claims must not resurface — in ANY readme, including the top-level one
#    (the top-level README carried "remaining brick" for nine sessions because this
#    check originally skipped it).
for phrase in "is the remaining extension" "generalization is the next brick" \
              "remaining brick" "not yet formally linked" \
              "Dobrushin DPI built (finite)"; do
  if grep -qF "$phrase" README.md transport-calculus/README.md transport-kernel/README.md 2>/dev/null; then
    echo "DRIFT: retired phrase present: '$phrase'"; fail=1
  fi
done

# 1b. The top-level README must mention every tier-bearing module family and note file.
for name in DobrushinMeasureReceive tvDist_toMeasure QuantumDobrushinReceive \
            OmegaOneCoherent NOTES-coherent-escapee.md PROBLEM-dip-schedulability.md \
            reps_implies_trivial VULN-COVERAGE.md; do
  if ! grep -q "$name" README.md; then
    echo "DRIFT: top-level README does not mention $name"; fail=1
  fi
done

# 1c. Every Lean name VULN-COVERAGE.md cites must exist in the Lean sources —
#     the map's verdicts are only as good as their citations.
for name in qualitative_admissible_is_JNI simA3_iff_respectsCoarsening A3_factors_kernel \
            no_irreducible_admissible ksafety_above_twosafety Rbad_nonseparable \
            summary_not_composable confidential_transport pleak_confidential_deploy \
            taint_is_JNI admissible_taint_is_Jtaint InfluencedAtMost \
            sanitize_const_is_taint value_predicate_not_admissible \
            blacklist_not_admissible ReleasesAtMost attest_is_not_J_evidence \
            releases_seq seqRelease boundaryNI_seq outNI_seq seq_all_channels \
            taint_result_seq boundaryNI_iff_resultNI bridge_iff_releases \
            comp_reconstructs_seq_release broken_seam \
            channel_certs_do_not_compose pleak_chain_releases \
            secCheck boundaryNI_of_check pleak_rejected typed_but_wall_leaks \
            secCheckD relOf_seq checker_rederives_pleak_bound pfull_ledger \
            multiplex_isolates_B leaky_not_isolated certified_pipeline \
            certified_pipeline_reconstruction; do
  if ! grep -rq "$name" conf-typing/ConfTyping/ transport-calculus/TransportCalculus.lean 2>/dev/null; then
    echo "DRIFT: VULN-COVERAGE cites $name but it is not in the Lean sources"; fail=1
  fi
done

# 1d. Row 3's [proved] verdict is only valid while its theorems are in the build.
if grep -q "proved: T1, T2" VULN-COVERAGE.md; then
  for thm in "theorem taint_is_JNI" "theorem blacklist_not_admissible"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/Integrity.lean 2>/dev/null; then
      echo "DRIFT: VULN-COVERAGE row 3 is [proved] but '$thm' is missing"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.Integrity" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: Integrity.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1e. Row 12's end-to-end [proved] is only valid while the seam and reception
#     theorems are in the build.
if grep -q "proved, end-to-end" VULN-COVERAGE.md; then
  for pair in "theorem releases_seq:conf-typing/ConfTyping/Compose.lean" \
              "theorem broken_seam:conf-typing/ConfTyping/Compose.lean" \
              "theorem comp_reconstructs_seq_release:conf-typing/ConfTyping/FlowBridge.lean"; do
    thm="${pair%%:*}"; file="${pair##*:}"
    if ! grep -q "$thm" "$file" 2>/dev/null; then
      echo "DRIFT: VULN-COVERAGE row 12 is end-to-end [proved] but '$thm' is missing from $file"; fail=1
    fi
  done
  for mod in "import ConfTyping.Compose" "import ConfTyping.FlowBridge"; do
    if ! grep -q "$mod" conf-typing/ConfTyping.lean 2>/dev/null; then
      echo "DRIFT: row 12 module not imported by the ConfTyping root: $mod"; fail=1
    fi
  done
fi

# 1f. The (generated) verdicts and row 7's [proved] rest on the checker and the
#     pipeline theorem being in the build.
if grep -q "IN (generated)" VULN-COVERAGE.md; then
  for pair in "theorem boundaryNI_of_check:conf-typing/ConfTyping/SecTy.lean" \
              "theorem checker_rederives_pleak_bound:conf-typing/ConfTyping/SecTyD.lean" \
              "theorem multiplex_isolates_B:conf-typing/ConfTyping/Pipeline.lean" \
              "theorem certified_pipeline:conf-typing/ConfTyping/Pipeline.lean"; do
    thm="${pair%%:*}"; file="${pair##*:}"
    if ! grep -q "$thm" "$file" 2>/dev/null; then
      echo "DRIFT: VULN-COVERAGE marks (generated) but '$thm' is missing from $file"; fail=1
    fi
  done
  for mod in "import ConfTyping.SecTy" "import ConfTyping.SecTyD" "import ConfTyping.Pipeline"; do
    if ! grep -q "$mod" conf-typing/ConfTyping.lean 2>/dev/null; then
      echo "DRIFT: checker module not imported by the ConfTyping root: $mod"; fail=1
    fi
  done
fi

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
