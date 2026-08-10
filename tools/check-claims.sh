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

# 1b′. Set-theory results cited in the notes/problem statement that are machine-checked
#      must still exist in the Lean sources — the rigor grades depend on it.
for name in omega1_finiteToOne_not_trivial omega1_finiteToOne_no_reps \
            countable_of_segments_finite bounded_of_countable \
            omega1_downDip_trivial omega1_downDip_iff_trivial; do
  if ! grep -q "$name" transport-kernel/TransportKernel/OmegaOneCoherent.lean 2>/dev/null; then
    echo "DRIFT: $name cited as machine-checked but missing from OmegaOneCoherent.lean"; fail=1
  fi
  if ! grep -qr "$name" transport-calculus/PROBLEM-dip-schedulability.md \
         transport-calculus/NOTES-coherent-escapee.md transport-kernel/README.md 2>/dev/null; then
    echo "DRIFT: $name proved in Lean but cited nowhere in the set-theory write-up"; fail=1
  fi
done

# 1b''. The READMEs must keep pace with the research notes. Both the top-level README
#      and the transport-calculus README must reference the highest-numbered notes
#      section — this is the drift that a full audit found: the sub-README summarised the
#      set-theory line as of section 52 while the notes had reached 57, still presenting a
#      claim that a later section had refuted.
maxsec=$(grep -oE '^## [0-9]+\.' transport-calculus/NOTES-coherent-escapee.md \
         | grep -oE '[0-9]+' | sort -n | tail -1)
if [ -n "$maxsec" ]; then
  for f in README.md transport-calculus/README.md; do
    if ! grep -q "§$maxsec" "$f"; then
      echo "DRIFT: $f does not reference notes §$maxsec (the latest section)"; fail=1
    fi
  done
fi

# 1b4. The class count in the standing-state heading must equal the documented convention
#      (VULN-COVERAGE §2½): one per numbered row of the §3 map, plus one per CLASS-EXTRA.
#      The full audit flagged this number as unverifiable because the convention was
#      undocumented; it is documented now, so it is checkable now.
rows=$(awk '/^\| # \| class/,/^$/' VULN-COVERAGE.md | grep -c '^| [0-9]')
extras=$(grep -c '^- CLASS-EXTRA:' VULN-COVERAGE.md)
total=$((rows + extras))
numeral=""
case $total in
  12) numeral=twelve;;
  13) numeral=thirteen;;
  14) numeral=fourteen;;
  15) numeral=fifteen;;
  16) numeral=sixteen;;
  17) numeral=seventeen;;
  18) numeral=eighteen;;
  19) numeral=nineteen;;
  20) numeral=twenty;;
esac
if [ -z "$numeral" ]; then
  echo "DRIFT: class count $total (rows=$rows extras=$extras) is outside this guard's numeral table"; fail=1
elif ! grep -q "bricks, $numeral classes)" VULN-COVERAGE.md; then
  echo "DRIFT: the §2½ convention gives $total classes (rows=$rows + extras=$extras) but the standing-state heading does not say '$numeral classes'"; fail=1
fi

# 1aa. No two top-level declarations in the flat `ConfTyping` namespace may share a
#     name. The build does catch this — but only at root-import time, with a cryptic
#     "environment already contains ..." after a per-module build has already
#     succeeded. Catching it here names both sites.
dups=$(grep -hoE '^(theorem|lemma|def|abbrev|structure|inductive) [A-Za-z_][^ :({[]*' \
         conf-typing/ConfTyping/*.lean 2>/dev/null \
       | awk '{print $2}' | sort | uniq -d)
if [ -n "$dups" ]; then
  for d in $dups; do
    where=$(grep -lE "^(theorem|lemma|def|abbrev|structure|inductive) $d\b" \
              conf-typing/ConfTyping/*.lean | tr '\n' ' ')
    echo "DRIFT: duplicate top-level name '$d' in the flat ConfTyping namespace: $where"; fail=1
  done
fi

# 1ab. The bundle layer of the interface must exist and stay cited: it is the
#       foundation the composable-core work builds on.
for name in "GradedAction.prod" "Bridge.pair" "Bridge.pair_comp_cert" \
            "bundle_accumulates_componentwise"; do
  if ! grep -q "$name" transport-calculus/TransportCalculus.lean 2>/dev/null; then
    echo "DRIFT: $name missing from TransportCalculus.lean"; fail=1
  fi
done
for name in "GradedAction.prod" "Bridge.pair_comp_cert"; do
  if ! grep -q "$name" transport-calculus/README.md README.md 2>/dev/null; then
    echo "DRIFT: $name proved but cited in neither README"; fail=1
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
            fcheck_safe uaf_errors uaf_rejected double_free_errors \
            hsecTy_ni hconfine hcheck heap_leak leak_rejected \
            concat_injectable param_immune param_correct param_noninterference \
            qcheck_ni injection_free_of_check unsafe_rejected unsafe_leaks \
            dbcheck_ni naive_accepts_stored sound_rejects_stored stored_injection_leaks \
            traversal_escapes flat_contained openLeaf_contained pathCheck_sound \
            latSecTy_ni latConfine dmdLat crosscompartment_untypable crosscompartment_leaks \
            acheck_safe alias_uaf_errors alias_uaf_rejected alias_ok_accepted \
            hlcheck_safe loopalloc_safe loop_wild_errors loop_wild_rejected \
            parse_print scheck_ni source_injection_free unsafe_src_rejected \
            lex_print source_string_injection_free unsafe_chars_parse unsafe_chars_rejected \
            flsafe allocfree_loop_safe usefree_loop_rejected doublefree_loop_rejected \
            alsafe alias_free_loop_safe alias_uaf_loop_rejected doublefree_aliasloop_rejected \
            lexR_printReal rich_source_injection_free param_correct_N concat_injectable_N \
            argv_correct cmd_concat_injectable \
            ofDigits_toDigits lexD_printD decimal_source_injection_free unsafe_decimal_rejected \
            field_correct log_concat_injectable log_concat_leaks \
            ALInv_coarsen loopFix_correct coarsen_loop_safe alias_maintain_loop_safe brick24_rejects \
            loopFix_terminates findMerge_mergeOne_length \
            Coarsens_collapse coarsen_loop_complete loopSearch_complete loopSearch_correct \
            alsafe2 prog_safe prog_checks loopFix2_correct alcheck2_loop_correct nested_prog_safe \
            findMerge2_mem weak_accepted weak_prog_safe; do
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

# 1o. The heap-information-flow (brick 13) theorems must be in the build.
if grep -q "HeapFlow.lean" VULN-COVERAGE.md; then
  for thm in "theorem hsecTy_ni" "theorem heap_leak" "theorem leak_rejected"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/HeapFlow.lean 2>/dev/null; then
      echo "DRIFT: heap information flow cited but '$thm' is missing from HeapFlow.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.HeapFlow" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: HeapFlow.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1p. The real-injection (brick 14) theorems must be in the build.
if grep -q "InjectionReal.lean" VULN-COVERAGE.md; then
  for thm in "theorem concat_injectable" "theorem param_immune" "theorem param_correct"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/InjectionReal.lean 2>/dev/null; then
      echo "DRIFT: real injection cited but '$thm' is missing from InjectionReal.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.InjectionReal" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: InjectionReal.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1q. The taint-flow-linter (brick 15) theorems must be in the build.
if grep -q "QueryProgram.lean" VULN-COVERAGE.md; then
  for thm in "theorem qcheck_ni" "theorem unsafe_rejected" "theorem unsafe_leaks"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/QueryProgram.lean 2>/dev/null; then
      echo "DRIFT: taint-flow linter cited but '$thm' is missing from QueryProgram.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.QueryProgram" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: QueryProgram.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1r. The stored-injection (brick 16) theorems must be in the build.
if grep -q "DbInjection.lean" VULN-COVERAGE.md; then
  for thm in "theorem dbcheck_ni" "theorem naive_accepts_stored" "theorem sound_rejects_stored"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/DbInjection.lean 2>/dev/null; then
      echo "DRIFT: stored injection cited but '$thm' is missing from DbInjection.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.DbInjection" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: DbInjection.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1s. The path-traversal (brick 17) theorems must be in the build.
if grep -q "PathTraversal.lean" VULN-COVERAGE.md; then
  for thm in "theorem traversal_escapes" "theorem flat_contained" "theorem pathCheck_sound"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/PathTraversal.lean 2>/dev/null; then
      echo "DRIFT: path traversal cited but '$thm' is missing from PathTraversal.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.PathTraversal" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: PathTraversal.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1t. The label-lattice (brick 18) theorems must be in the build.
if grep -q "LatticeFlow.lean" VULN-COVERAGE.md; then
  for thm in "theorem latSecTy_ni" "theorem crosscompartment_leaks" "theorem crosscompartment_untypable"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/LatticeFlow.lean 2>/dev/null; then
      echo "DRIFT: label lattice cited but '$thm' is missing from LatticeFlow.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.LatticeFlow" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: LatticeFlow.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1u. The pointer-aliasing (brick 19) theorems must be in the build.
if grep -q "AliasSafe.lean" VULN-COVERAGE.md; then
  for thm in "theorem acheck_safe" "theorem alias_uaf_errors" "theorem alias_uaf_rejected"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/AliasSafe.lean 2>/dev/null; then
      echo "DRIFT: pointer aliasing cited but '$thm' is missing from AliasSafe.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.AliasSafe" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: AliasSafe.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1v. The heap-loop (brick 20) theorems must be in the build.
if grep -q "HeapLoop.lean" VULN-COVERAGE.md; then
  for thm in "theorem hlcheck_safe" "theorem loop_wild_errors" "theorem loop_wild_rejected"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/HeapLoop.lean 2>/dev/null; then
      echo "DRIFT: heap loops cited but '$thm' is missing from HeapLoop.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.HeapLoop" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: HeapLoop.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1w. The parser (brick 21) theorems must be in the build.
if grep -q "ParseSource.lean" VULN-COVERAGE.md; then
  for thm in "theorem parse_print" "theorem source_injection_free" "theorem unsafe_parses"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/ParseSource.lean 2>/dev/null; then
      echo "DRIFT: parser cited but '$thm' is missing from ParseSource.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.ParseSource" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: ParseSource.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1x. The lexer (brick 22) theorems must be in the build.
if grep -q "LexSource.lean" VULN-COVERAGE.md; then
  for thm in "theorem lex_print" "theorem source_string_injection_free" "theorem unsafe_chars_parse"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/LexSource.lean 2>/dev/null; then
      echo "DRIFT: lexer cited but '$thm' is missing from LexSource.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.LexSource" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: LexSource.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1y. The free-under-loops (brick 23) theorems must be in the build.
if grep -q "FreeLoop.lean" VULN-COVERAGE.md; then
  for thm in "theorem flsafe" "theorem usefree_loop_rejected" "theorem doublefree_loop_rejected"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/FreeLoop.lean 2>/dev/null; then
      echo "DRIFT: free-under-loops cited but '$thm' is missing from FreeLoop.lean"; fail=1
    fi
  done
  if ! grep -q "import ConfTyping.FreeLoop" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: FreeLoop.lean not imported by the ConfTyping root"; fail=1
  fi
fi

# 1z. The four "what's left" depth bricks (24-27) must be in the build.
if grep -q "AliasLoop.lean" VULN-COVERAGE.md; then
  for thm in "theorem alsafe" "theorem alias_free_loop_safe" "theorem doublefree_aliasloop_rejected"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/AliasLoop.lean 2>/dev/null; then
      echo "DRIFT: may-alias-under-loops cited but '$thm' is missing from AliasLoop.lean"; fail=1
    fi
  done
fi
if grep -q "DecimalId.lean" VULN-COVERAGE.md; then
  for thm in "theorem ofDigits_toDigits" "theorem lexD_printD" "theorem decimal_source_injection_free"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/DecimalId.lean 2>/dev/null; then
      echo "DRIFT: decimal identifiers cited but '$thm' is missing from DecimalId.lean"; fail=1
    fi
  done
fi
if grep -q "AliasFix.lean" VULN-COVERAGE.md; then
  for thm in "theorem ALInv_coarsen" "theorem loopFix_correct" "theorem coarsen_loop_safe" "theorem alias_maintain_loop_safe"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/AliasFix.lean 2>/dev/null; then
      echo "DRIFT: fixpoint may-alias cited but '$thm' is missing from AliasFix.lean"; fail=1
    fi
  done
fi
if grep -q "QueryEscape.lean" VULN-COVERAGE.md; then
  for thm in "theorem skeletonE_eq_skeleton" "theorem segsE_buildEsc" "theorem escBad_injectable" \
             "theorem esc_mismatch_injectable" "theorem escaping_no_silent_discharge" \
             "theorem escaping_reducible_parameterization_in"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/QueryEscape.lean 2>/dev/null; then
      echo "DRIFT: query escaping cited but '$thm' is missing from QueryEscape.lean"; fail=1
    fi
  done
fi
if grep -q "Race.lean" VULN-COVERAGE.md; then
  for thm in "theorem toctou_interleaving_unsafe" "theorem sequential_model_misses_races" \
             "theorem atomic_all_schedules_safe" "theorem racefree_all_schedules" \
             "theorem bad_atom_not_preserving"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/Race.lean 2>/dev/null; then
      echo "DRIFT: races/TOCTOU cited but '$thm' is missing from Race.lean"; fail=1
    fi
  done
fi
# composable core stage 1i: free, and the obstruction that explains stage 1h's gap.
for thm in "theorem slcheck_sound" "theorem slcheck_no_fault" \
           "theorem memInv_not_preserved_by_free" "theorem use_after_free_faults" \
           "theorem slcheck_extends_umcheck"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/MemLinear.lean 2>/dev/null; then
    echo "DRIFT: the separating certificate is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1h: the heap, and the two limits recorded as theorems.
for thm in "theorem umcheck_sound" "theorem umcheck_no_fault" "theorem wild_deref_faults" \
           "theorem free_has_no_rule" "theorem clobbered_pointer_rejected"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/MemCert.lean 2>/dev/null; then
    echo "DRIFT: the heap certificate is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1g: the coverage claim must stay projected out as theorems.
for thm in "theorem bundle_covers_timing" "theorem bundle_covers_termination" \
           "theorem bundle_covers_seam" "theorem handler_covers_six_rows"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/BundleCoverage.lean 2>/dev/null; then
    echo "DRIFT: the six-row coverage is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1f: what an aborted run does, and loops in the bundle.
for thm in "theorem uexec_dead_unchanged" "theorem uexec_dead_loop_diverges" \
           "theorem uexec_dead_cost" "theorem UCert.ofEmbedded" \
           "theorem handlerBounded_numbers"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/BundleLoop.lean 2>/dev/null; then
    echo "DRIFT: bounded loops are cited but '$thm' is missing from BundleLoop.lean"; fail=1
  fi
done

# composable core stage 1e: the fourth accumulation law and the typed CARRIED half.
for thm in "theorem UCertL.seq" "theorem handler_intended_reads" \
           "theorem handler_needs_the_policy_assumption" \
           "theorem row7_carried_is_a_ledger_entry" "theorem four_laws_one_composition"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/BundleLedger.lean 2>/dev/null; then
    echo "DRIFT: the ledger bundle is cited but '$thm' is missing from BundleLedger.lean"; fail=1
  fi
done

# composable core stage 1d: the third certificate and the price recorded with it.
for thm in "theorem usecTy_sound" "theorem handler_three_certificates" \
           "theorem access_is_static_by_design" "theorem Psec_rejects_leaks"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/UnifiedNI.lean 2>/dev/null; then
    echo "DRIFT: the third certificate is cited but '$thm' is missing from UnifiedNI.lean"; fail=1
  fi
done

# composable core stage 1c: the bundle must exist and its artifact stay proved.
for thm in "theorem ucheck_sound" "theorem UCert.seq" "theorem handler_bundle_end_to_end" \
           "theorem handler_partial_policy"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/Bundle.lean 2>/dev/null; then
    echo "DRIFT: the bundle is cited but '$thm' is missing from Bundle.lean"; fail=1
  fi
done

# composable core: the embedding theorem is what makes brick results transfer.
for thm in "theorem uexec_embed_eq" "theorem ucost_of_cost" "theorem uembed_mediated"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/Unified.lean 2>/dev/null; then
    echo "DRIFT: composable core cited but '$thm' is missing from Unified.lean"; fail=1
  fi
done
if ! grep -q "Unified.lean" conf-typing/README.md; then
  echo "DRIFT: Unified.lean not described in conf-typing/README.md"; fail=1
fi

if grep -q "Mediation.lean" VULN-COVERAGE.md; then
  for thm in "theorem medCheck_sound" "theorem victim_not_mediated" \
             "theorem fixed_mediated" "theorem policy_correctness_not_witnessed" \
             "theorem mediation_generated_policy_carried"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/Mediation.lean 2>/dev/null; then
      echo "DRIFT: complete mediation cited but '$thm' is missing from Mediation.lean"; fail=1
    fi
  done
fi
if grep -q "CostBound.lean" VULN-COVERAGE.md; then
  for thm in "theorem cost_seq" "theorem cost_seq_is_mul" "theorem costCheck_sound" \
             "theorem countdown_cost" "theorem dos_unbounded" "theorem budget_cost"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/CostBound.lean 2>/dev/null; then
      echo "DRIFT: resource exhaustion cited but '$thm' is missing from CostBound.lean"; fail=1
    fi
  done
fi
if grep -q "Speculate.lean" VULN-COVERAGE.md; then
  for thm in "theorem spectre_leaks" "theorem arch_indistinguishable" \
             "theorem speculative_model_misses_it" "theorem specCheck_sound" \
             "theorem spec_inert" "theorem arch_ni_transfers" \
             "theorem benign_transient_is_constant"; do
    if ! grep -q "$thm" conf-typing/ConfTyping/Speculate.lean 2>/dev/null; then
      echo "DRIFT: speculative execution cited but '$thm' is missing from Speculate.lean"; fail=1
    fi
  done
fi
for mod in AliasLoop LexReal QueryGrammar CmdInjection DecimalId LogInjection AliasFix QueryEscape Race Speculate CostBound Mediation Unified Bundle UnifiedNI BundleLedger BundleLoop BundleCoverage MemCert MemLinear; do
  if grep -q "$mod.lean" VULN-COVERAGE.md && \
     ! grep -q "import ConfTyping.$mod" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: $mod.lean cited in VULN-COVERAGE but not imported by the ConfTyping root"; fail=1
  fi
done

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
