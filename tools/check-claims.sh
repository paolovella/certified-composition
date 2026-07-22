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
            certified_pipeline_reconstruction \
            CondBoundary condBoundary_seq condBoundary_discharge \
            ledger_no_silent_discharge ledgerGA ledgerBridge_comp_ledger \
            ledger_supply_chain_ledger condBoundary_of_check_assuming \
            supply_chain_ledger biz_needs_assumption \
            secTyT_sound secCheckT outNI_of_checkT secCheckT_imp_secCheck \
            ptime_rejected_T \
            secTyTD_sound secCheckTD releasesAtMost_of_checkTD \
            ptime_timing_released ptime_wall_of_bit ptime_rejected_TD \
            wsecTy_sound wcheck wleak_leaks wleak_rejected wexec_embed_eq \
            wexec_mono \
            WOutNI WOutNI_seq WOutNI_of_wcheck wok_pipeline_certified \
            wleak_poisons_seam \
            WCondBoundary WCondBoundary_seq wledger_no_silent_discharge \
            wcx_not_unconditional \
            haltQ wbridge_iff_sound wOutNI_contracts ofWComponent_comp_map \
            mcheck_safe msafe_of_check mwild_store_errors mwild_rejected \
            fcheck_safe uaf_errors uaf_rejected double_free_errors; do
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

# 1g. Row 11's [proved] LEDGER verdict rests on the brick-4 ledger theorems.
if grep -q "LEDGER (mechanized)" VULN-COVERAGE.md; then
  for pair in "theorem ledger_no_silent_discharge:conf-typing/ConfTyping/Ledger.lean" \
              "theorem ledgerBridge_comp_ledger:conf-typing/ConfTyping/LedgerBridge.lean" \
              "theorem condBoundary_of_check_assuming:conf-typing/ConfTyping/SupplyChain.lean"; do
    thm="${pair%%:*}"; file="${pair##*:}"
    if ! grep -q "$thm" "$file" 2>/dev/null; then
      echo "DRIFT: VULN-COVERAGE row 11 is [proved] but '$thm' is missing from $file"; fail=1
    fi
  done
  for mod in "import ConfTyping.Ledger" "import ConfTyping.LedgerBridge" "import ConfTyping.SupplyChain"; do
    if ! grep -q "$mod" conf-typing/ConfTyping.lean 2>/dev/null; then
      echo "DRIFT: ledger module not imported by the ConfTyping root: $mod"; fail=1
    fi
  done
fi

# 1h. Row 2's (generated) verdict rests on the timing-sensitive checker.
if grep -q "IN-WITH-MODEL (generated)" VULN-COVERAGE.md; then
  for thm in "theorem secTyT_sound" "theorem ptime_rejected_T" "theorem outNI_of_checkT"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/SecTyT.lean 2>/dev/null; then
      echo "DRIFT: VULN-COVERAGE row 2 is (generated) but '$thm' is missing from SecTyT.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.SecTyT" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: SecTyT.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1i. Row 13 (termination leaks) rests on the brick-7 while development.
if grep -q "termination / progress leaks" VULN-COVERAGE.md; then
  for thm in "theorem wsecTy_sound" "theorem wleak_leaks" "theorem wexec_embed_eq"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/WhileImp.lean 2>/dev/null; then
      echo "DRIFT: VULN-COVERAGE row 13 present but '$thm' is missing from WhileImp.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.WhileImp" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: WhileImp.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1j. The seam-over-loops (brick 8) theorems must be in the build.
if grep -q "WhileCompose.lean" VULN-COVERAGE.md; then
  for thm in "theorem WOutNI_seq" "theorem wleak_poisons_seam"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/WhileCompose.lean 2>/dev/null; then
      echo "DRIFT: brick-8 seam cited but '$thm' is missing from WhileCompose.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.WhileCompose" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: WhileCompose.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1k. The ledger-over-loops (brick 9) theorems must be in the build.
if grep -q "WhileLedger.lean" VULN-COVERAGE.md; then
  for thm in "theorem WCondBoundary_seq" "theorem wledger_no_silent_discharge"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/WhileLedger.lean 2>/dev/null; then
      echo "DRIFT: brick-9 ledger cited but '$thm' is missing from WhileLedger.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.WhileLedger" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: WhileLedger.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1l. The Bridge-reception-over-loops (brick 10) theorems must be in the build.
if grep -q "WhileBridge.lean" VULN-COVERAGE.md; then
  for thm in "theorem wbridge_iff_sound" "def Bridge.ofWComponent" "def haltQ"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/WhileBridge.lean 2>/dev/null; then
      echo "DRIFT: brick-10 reception cited but '$thm' is missing from WhileBridge.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.WhileBridge" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: WhileBridge.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1m. The memory-safety (brick 11) theorems must be in the build.
if grep -q "MemSafe.lean" VULN-COVERAGE.md; then
  for thm in "theorem mcheck_safe" "theorem mwild_store_errors" "theorem mwild_rejected"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/MemSafe.lean 2>/dev/null; then
      echo "DRIFT: memory-safety cited but '$thm' is missing from MemSafe.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.MemSafe" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: MemSafe.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1n. The use-after-free (brick 12) theorems must be in the build.
if grep -q "MemFree.lean" VULN-COVERAGE.md; then
  for thm in "theorem fcheck_safe" "theorem uaf_errors" "theorem double_free_errors"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/MemFree.lean 2>/dev/null; then
      echo "DRIFT: use-after-free cited but '$thm' is missing from MemFree.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.MemFree" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: MemFree.lean not imported by the ConfTyping root"; fail=1
  fi
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
