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
#     Stage 3a added the first NESTED namespace (`Src`), so the name a declaration
#     actually occupies is its namespace path, not its bare identifier: `Src.parse` and
#     `parse` are different declarations and the root build accepts both. The guard tracks
#     the namespace stack rather than being relaxed, so a clash *inside* `Src` still fires.
qualify() {
  awk '
    /^namespace [A-Za-z_]/ { stack[++depth] = $2; next }
    /^end [A-Za-z_]/       { if (depth > 0 && stack[depth] == $2) depth--; next }
    /^(theorem|lemma|def|abbrev|structure|inductive) [A-Za-z_]/ {
      name = $2; sub(/[ :({[].*/, "", name)
      path = ""
      for (i = 1; i <= depth; i++) path = path stack[i] "."
      print path name
    }' "$1"
}
#     A declaration at depth 0 is in the ROOT namespace, not `ConfTyping` — which is what
#     an edit appended past the closing `end` looks like. Lean accepts it silently (it does
#     not clash with the namespaced name), so nothing else would catch it.
outside=$(for f in conf-typing/ConfTyping/*.lean; do
            qualify "$f" | grep -v '\.' | sed "s#^#$f: #"
          done)
if [ -n "$outside" ]; then
  echo "$outside" | while read -r line; do
    echo "DRIFT: declaration outside the ConfTyping namespace: $line"
  done
  fail=1
fi
dups=$(for f in conf-typing/ConfTyping/*.lean; do qualify "$f"; done | sort | uniq -d)
if [ -n "$dups" ]; then
  for d in $dups; do
    bare=${d##*.}
    where=$(grep -lE "^(theorem|lemma|def|abbrev|structure|inductive) $bare\b" \
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
# CI must run the same script a working session runs, or the two drift and the badge
# stops meaning anything. The workflow may call tools/ci.sh and nothing else, and
# tools/ci.sh must cover every gate.
if [ ! -f .github/workflows/ci.yml ]; then
  echo "DRIFT: no CI workflow"; fail=1
elif ! grep -q "bash tools/ci.sh" .github/workflows/ci.yml; then
  # the invocation, not a mention in a step name
  echo "DRIFT: the CI workflow does not invoke tools/ci.sh"; fail=1
fi
for gate in "conf-typing" "transport-calculus" "transport-kernel" \
            "check-claims.sh" "guard-selftest.sh" "walk-check.py" "sorry"; do
  if ! grep -q "$gate" tools/ci.sh 2>/dev/null; then
    echo "DRIFT: tools/ci.sh does not gate on '$gate'"; fail=1
  fi
done

# stage 3a: source text, and a tool.
for thm in "theorem source_certified" "theorem parseE_toksE" "def parseSource" \
           "def okName" "def toks " "def lex " "def parse " "def classify"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/Surface.lean 2>/dev/null; then
    echo "DRIFT: the source-text stage is cited but '$thm' is missing"; fail=1
  fi
done
# the tool must exist and be wired up: the README tells people to run it.
if ! grep -q 'name = "certcheck"' conf-typing/lakefile.toml 2>/dev/null; then
  echo "DRIFT: certcheck is documented but conf-typing/lakefile.toml declares no such exe"; fail=1
fi
if [ ! -f conf-typing/Main.lean ]; then
  echo "DRIFT: certcheck is documented but conf-typing/Main.lean is gone"; fail=1
fi
# the accepted example must stay the program the Lean side pins at budget 40.
if [ ! -f conf-typing/examples/handler.uc ]; then
  echo "DRIFT: examples/handler.uc is cited but missing"; fail=1
fi
for ex in unmediated use-after-free injection unbounded-loop secret-leak secret-branch; do
  if [ ! -f "conf-typing/examples/rejected/$ex.uc" ]; then
    echo "DRIFT: the rejected-example set is cited but $ex.uc is missing"; fail=1
  fi
done
# the parser's residue is stated in two places; if the statement layer ever gets proved,
# both must stop saying it is open.
if ! grep -q "statement layer is not proved" conf-typing/README.md 2>/dev/null; then
  echo "DRIFT: the parser's unproved statement layer is no longer stated in the README"; fail=1
fi

# the external corpus: transcribed, not authored here. Its value is that it was not
# written to the rules, so editing it destroys the only unbiased measurement we have.
n=$(ls conf-typing/corpus/ext/*.uc 2>/dev/null | wc -l)
if [ "$n" -ne 12 ]; then
  echo "DRIFT: the external corpus is cited as 12 programs but holds $n"; fail=1
fi
for f in conf-typing/corpus/ext/SOURCES.md conf-typing/corpus/ext/RESULTS.md; do
  if [ ! -f "$f" ]; then echo "DRIFT: the external corpus cites $f but it is missing"; fail=1; fi
done
# the leak gap must stay stated in the coverage map, since nothing else states it.
if ! grep -q "Leaks (CWE-401) are NOT detected" VULN-COVERAGE.md 2>/dev/null; then
  echo "DRIFT: the leak scope-hole found by the external corpus is no longer stated in VULN-COVERAGE"
  fail=1
fi

# stage B: the CN reception. This is the first certificate in the repo produced by a
# tool that is not this repo, so the guards here are mostly about NOT OVERCLAIMING it.
for thm in "theorem cn_comp_ledger" "theorem cn_comp_footprint" "theorem modifiesOnly_comp" \
           "theorem cn_untouched_outside" "theorem cn_base_strictly_smaller" \
           "theorem cn_comp_base_strictly_smaller" "theorem cn_false_footprint_unreceivable" \
           "theorem cn_frame_rule" "def cnGA" "def Bridge.ofCN"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/CNReceive.lean 2>/dev/null; then
    echo "DRIFT: the CN reception is cited but '$thm' is missing from CNReceive.lean"; fail=1
  fi
done
if [ ! -f conf-typing/corpus/cn/SOURCES.md ]; then
  echo "DRIFT: the CN reception cites conf-typing/corpus/cn/SOURCES.md but it is missing"; fail=1
fi
# The reception is by hand and is NOT checked against CN. If that sentence ever leaves the
# module, the stage starts reading as "we verified C", which it is not.
if ! grep -q "not checked against CN's implementation" conf-typing/ConfTyping/CNReceive.lean 2>/dev/null; then
  echo "DRIFT: CNReceive no longer states that the encoding is unchecked against CN"; fail=1
fi
# Bridge.ofCN must keep DEMANDING the modifies clause. If the hypothesis is ever dropped,
# every downstream theorem still compiles and all of them become vacuous.
if ! grep -q "(h : ModifiesOnly f F)" conf-typing/ConfTyping/CNReceive.lean 2>/dev/null; then
  echo "DRIFT: Bridge.ofCN no longer demands ModifiesOnly - the reception would be free"; fail=1
fi
# CN's resource keyword is RW<T>; the older Owned<T> spelling would mean the transcription
# was recalled rather than read.
if ! grep -q "RW<unsigned int>" conf-typing/corpus/cn/SOURCES.md 2>/dev/null; then
  echo "DRIFT: the CN transcription no longer shows the RW<T> ownership syntax"; fail=1
fi

# stage C: heterogeneous composition. The finding is that the interaction term lives in
# Bridge.pair's hmap, and it rests on a counterexample plus a sufficient condition. If
# either half goes, the stage's conclusion is unsupported.
for thm in "theorem arch_reconciliation_insufficient" "theorem touchesOnly_of_inert" \
           "theorem bcb_not_touches" "theorem bcb_arch_touches" \
           "theorem bcb_reconciles" "theorem bcb_not_trace_inert" \
           "theorem hetero_bundle_componentwise" "theorem hetero_bundle_laws" \
           "theorem cn_unions_sct_intersects" "theorem cn_reception_transfers" "def sctGA"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeteroCompose.lean 2>/dev/null; then
    echo "DRIFT: stage C is cited but '$thm' is missing from HeteroCompose.lean"; fail=1
  fi
done
# The two halves of the bundle must accumulate by DIFFERENT monoids. If sctGA's mul ever
# becomes a union, the bundle stops being heterogeneous and hetero_bundle_laws still
# proves - it just stops meaning anything.
if ! grep -q "exact propext and_assoc" conf-typing/ConfTyping/HeteroCompose.lean 2>/dev/null; then
  echo "DRIFT: sctGA no longer accumulates by intersection - the bundle is not heterogeneous"; fail=1
fi
# Stage C's second producer is modelled, not transcribed. Saying otherwise would claim a
# Jasmin reception this repo has not done.
if ! grep -q "modelled, not transcribed" conf-typing/ConfTyping/HeteroCompose.lean 2>/dev/null; then
  echo "DRIFT: HeteroCompose no longer states that the SCT certificate is modelled, not transcribed"
  fail=1
fi

# stage C second pass: Jasmin's level lattice, transcribed. The finding is that a CN
# certificate carried into a speculative world sits at `transient`, which only means
# anything while the level stays a PAIR and transient stays distinct from public.
for thm in "theorem bcb_footprint_is_transient" "theorem protected_footprint_is_public" \
           "theorem touchesOnly_imp_arch" "theorem bcbProtected_trace_inert" \
           "theorem cn_unions_jasmin_joins" "theorem slvl_transient_ne_public" \
           "def sctLvlGA" "def footprintLevel"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/JasminSCT.lean 2>/dev/null; then
    echo "DRIFT: the Jasmin reception is cited but '$thm' is missing from JasminSCT.lean"; fail=1
  fi
done
if [ ! -f conf-typing/corpus/jasmin/SOURCES.md ]; then
  echo "DRIFT: the Jasmin reception cites conf-typing/corpus/jasmin/SOURCES.md but it is missing"
  fail=1
fi
# The level must stay a PAIR. Collapse it to a single level and every theorem here still
# compiles while the finding - that transient is not public - silently evaporates.
if ! grep -q "structure SLvl where" conf-typing/ConfTyping/JasminSCT.lean 2>/dev/null || \
   ! grep -q "  spec   : Lvl" conf-typing/ConfTyping/JasminSCT.lean 2>/dev/null; then
  echo "DRIFT: SLvl is no longer a normal/speculative pair - the stage C finding is not statable"
  fail=1
fi
# As with CN, the reception is by hand. Saying otherwise would claim a Jasmin integration.
if ! grep -q "unchecked against the Jasmin checker" conf-typing/ConfTyping/JasminSCT.lean 2>/dev/null; then
  echo "DRIFT: JasminSCT no longer states that the encoding is unchecked against Jasmin"; fail=1
fi
# The transcription must keep the paper's own annotation, or it was recalled not read.
if ! grep -q "ptr: transient, val: transient" conf-typing/corpus/jasmin/SOURCES.md 2>/dev/null; then
  echo "DRIFT: the Jasmin transcription no longer shows fig3a's sct annotation"; fail=1
fi

# stage D: consuming an emitted certificate. The corpus file is REAL TOOL OUTPUT copied
# verbatim; editing it would make the parser tests meaningless in the same way editing the
# program corpus would.
for thm in "theorem compose_lvl_is_sctLvlGA" "theorem compose_ledger" "theorem compose_modmsf" \
           "theorem jasmin_base_strictly_smaller" "theorem baseLabels_length" \
           "def parseEmission" "def scanCerts"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/JasminCert.lean 2>/dev/null; then
    echo "DRIFT: the stage D combinator is cited but '$thm' is missing from JasminCert.lean"; fail=1
  fi
done
for f in conf-typing/corpus/jasmin/accept.expected conf-typing/corpus/jasmin/EMISSION.md; do
  if [ ! -f "$f" ]; then echo "DRIFT: stage D cites $f but it is missing"; fail=1; fi
done
n=$(grep -c "^\(no\)\?modmsf " conf-typing/corpus/jasmin/accept.expected 2>/dev/null || echo 0)
if [ "$n" -ne 57 ]; then
  echo "DRIFT: the Jasmin emission is cited as 57 certificates but holds $n"; fail=1
fi
# The measured coverage. If the parser or the corpus changes this silently, the 35% figure
# in EMISSION.md and the README stops being true.
if [ -x conf-typing/.lake/build/bin/certcompose ]; then
  r=$(conf-typing/.lake/build/bin/certcompose conf-typing/corpus/jasmin/accept.expected 2>/dev/null \
      | head -1 | grep -oE "[0-9]+ with a receivable" | grep -oE "^[0-9]+")
  if [ -n "$r" ] && [ "$r" -ne 20 ]; then
    echo "DRIFT: receivable-certificate count is $r, but 20 is the published figure"; fail=1
  fi
fi
# This repo does not use native_decide anywhere: it would add Lean.ofReduceBool to the
# axiom set of every parser test. The whole List Char design exists to avoid it.
# Matches the TACTIC position only - JasminCert's header discusses native_decide by name,
# and a guard that cannot tell prose from use fires on its own documentation.
if grep -rqE "by native_decide|^[[:space:]]*native_decide[[:space:]]*$" \
     --include=*.lean conf-typing/ConfTyping transport-calculus 2>/dev/null; then
  echo "DRIFT: native_decide has appeared - parser tests would rest on Lean.ofReduceBool"; fail=1
fi
# CN emits no certificate; saying otherwise would misdescribe the stage D verdict.
if ! grep -q "CN — no" conf-typing/corpus/jasmin/EMISSION.md 2>/dev/null; then
  echo "DRIFT: EMISSION.md no longer records that CN emits no consumable certificate"; fail=1
fi

# The bulletproof claim template is the goal-facing artifact. Its gap list is the whole
# honesty of the claim: a gap that quietly leaves the list turns the template into the
# slogan it exists to replace.
if ! grep -q "four irreducible gaps" VULN-COVERAGE.md 2>/dev/null; then
  echo "DRIFT: the claim template no longer says four irreducible gaps"; fail=1
fi
if ! grep -q "Bound gap" VULN-COVERAGE.md 2>/dev/null; then
  echo "DRIFT: the bound gap has left the claim template - 'survives composition' overclaims again"
  fail=1
fi
for thm in "ConfTyping.min_unsound" "ConfTyping.bounded_grade_does_not_factor"; do
  if ! grep -q "$thm" VULN-COVERAGE.md 2>/dev/null; then
    echo "DRIFT: the bound gap is stated but no longer cites '$thm'"; fail=1
  fi
done

# stage F: bounded guarantees as grades. The stage's content is a NEGATIVE result (min is
# unsound) and a non-factorization, and both are the kind of claim that dies quietly.
for thm in "theorem min_unsound" "theorem bounded_comp_sound" "theorem bmul_assoc" \
           "theorem bounded_grade_does_not_factor" "theorem bounded_comp_tight" \
           "theorem min_sound_when_nongrowing" "theorem bounded_phantom_not_inert" \
           "def BSafe" "def GrowsBy" "def bmul"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/BoundedCert.lean 2>/dev/null; then
    echo "DRIFT: stage F is cited but '$thm' is missing from BoundedCert.lean"; fail=1
  fi
done
# bmul MUST subtract the inner certificate's growth. Without that term it degenerates to
# exactly the min rule min_unsound refutes.
if ! grep -q "min i.bound (o.bound - i.growth)" conf-typing/ConfTyping/BoundedCert.lean 2>/dev/null; then
  echo "DRIFT: bmul no longer subtracts the inner growth - it has become the unsound min rule"
  fail=1
fi
# BSafe must stay STRICT. With `<=` the vacuous certificate is unrepresentable, truncated
# subtraction stops landing on it, and the no-side-condition soundness proof is wrong.
if ! grep -q "size x < b" conf-typing/ConfTyping/BoundedCert.lean 2>/dev/null; then
  echo "DRIFT: BSafe is no longer strict - the vacuous bound is no longer representable"; fail=1
fi

# stage 2k + corpus: the first measured rule. The corpus is the baseline; if it is
# edited, every improvement claim measured against it becomes meaningless.
for f in conf-typing/corpus/TASKS.md conf-typing/corpus/RESULTS.md; do
  if [ ! -f "$f" ]; then echo "DRIFT: the measured baseline cites $f but it is missing"; fail=1; fi
done
n=$(ls conf-typing/corpus/p/*.uc 2>/dev/null | wc -l)
if [ "$n" -ne 25 ]; then
  echo "DRIFT: the corpus is cited as 25 programs but holds $n - the baseline no longer compares"
  fail=1
fi
for thm in "theorem UMedInv.mono" "def subStr" "theorem subStr_mem"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/CountedLoop.lean 2>/dev/null; then
    echo "DRIFT: the stage-2k widening is cited but '$thm' is missing"; fail=1
  fi
done
# the widening must stay a widening: an equality test here would silently restore 2j.
if grep -q 'if A₂ == A && V₂ == dropStr i V then' conf-typing/ConfTyping/CountedLoop.lean 2>/dev/null; then
  echo "DRIFT: bcheck is back to demanding the mediation set be unchanged (stage 2k reverted)"; fail=1
fi

# stage 2j: the counted loop, natively.
for thm in "theorem noWrite_preserves" "theorem countU_turn" "theorem countU_cost" \
           "theorem countU_auth" "theorem UCert.forU" "theorem JSecTy.forU" \
           "theorem asFor_eq" "theorem bcheck_sound" "theorem loopHandler_five" \
           "theorem loopHandler_trace_is_low" "theorem allcheck_refuses_loopHandler" \
           "theorem unbounded_countdown_still_refused" \
           "theorem a_dead_counted_loop_does_not_halt"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/CountedLoop.lean 2>/dev/null; then
    echo "DRIFT: the counted-loop stage is cited but '$thm' is missing"; fail=1
  fi
done
# the stage's whole claim is that the OLD checker refuses this program and the new one
# does not. If either measurement moves, the claim is about a different program.
if ! grep -q 'bcheck Psec \[\] \[\] loopHandler = some (\["db"\], \[\], 40)' \
     conf-typing/ConfTyping/CountedLoop.lean 2>/dev/null; then
  echo "DRIFT: loopHandler is cited as checking at budget 40 but the stated result changed"; fail=1
fi
if ! grep -q 'allcheck Psec \[\] \[\] loopHandler = none' \
     conf-typing/ConfTyping/CountedLoop.lean 2>/dev/null; then
  echo "DRIFT: the contrast with allcheck is cited but the theorem is gone"; fail=1
fi
# brick 34's boundary must stay where it is: no rule for a general loop.
if ! grep -q "theorem only_the_budget_lacks_a_loop_rule" conf-typing/ConfTyping/FullCert.lean 2>/dev/null; then
  echo "DRIFT: stage 2j cites the standing record but it is gone"; fail=1
fi

# stage 2i: the fused induction, and the trace theorem.
for thm in "theorem jcheck_ptrLow" "theorem transRun_agrees" "theorem jcheck_strace" \
           "theorem allcheck_jcheck" "theorem certified_trace_is_low" \
           "theorem bigHandler_trace_is_low" "theorem brWitness_trace_is_low" \
           "theorem the_hypothesis_is_load_bearing" "theorem jcheck_flatten" \
           "theorem uexecS_uexec" "theorem brWitness_window_grows"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/SpecFused.lean 2>/dev/null; then
    echo "DRIFT: the trace-theorem stage is cited but '$thm' is missing"; fail=1
  fi
done
# the whole stage turns on the fused invariant carrying BOTH memory-safety fields, which
# is what stage 2g's traceEq_is_not_inductive says is required. If either is dropped the
# theorem may still be true, but it is no longer the theorem 2g asked for.
for fld in "  sep  : SepInv" "  lab  : LabInv" "  low  : uLowEqA" "  ptr  : PtrLow"; do
  if ! grep -q "$fld" conf-typing/ConfTyping/SpecFused.lean 2>/dev/null; then
    echo "DRIFT: FusedInv is cited as carrying SepInv/LabInv/uLowEqA/PtrLow but '$fld' is gone"
    fail=1
  fi
done
# the headline measurements. The trace theorem is only worth stating because these two
# say the traces it equates are non-empty and window-dependent.
if ! grep -q 'straceU 60 0 bigHandler (fun _ => true) (initU σlo) = some \[0, 0, 1, 1, 0, 1\]' \
     conf-typing/ConfTyping/SpecFused.lean 2>/dev/null; then
  echo "DRIFT: bigHandler's six-address trace is cited but the stated measurement changed"; fail=1
fi
if ! grep -q 'straceU 20 1 brWitness (fun _ => true) (initU σlo) = some \[0, 1\]' \
     conf-typing/ConfTyping/SpecFused.lean 2>/dev/null; then
  echo "DRIFT: the transient window is cited as lengthening brWitness's trace but the measurement changed"
  fail=1
fi

# stage 2h: the worked program at size.
for thm in "theorem bigHandler_checks" "theorem bigHandler_five" \
           "theorem bigHandler_runs_clean" "theorem bigHandler_releases_everything" \
           "theorem the_secret_address_is_retired" "theorem bigHandler_emits_one_clean_query" \
           "theorem bigHandler_trusted_base" "theorem bigHandler_owes_the_filesystem_nothing" \
           "theorem bigHandler_is_not_inert" "theorem bigHandler_speculative_cost" \
           "theorem bigHandler_cost_under_every_window" \
           "theorem bigHandler_trace_happens_not_to_grow"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/BigHandler.lean 2>/dev/null; then
    echo "DRIFT: the worked-program stage is cited but '$thm' is missing"; fail=1
  fi
done
# the headline numbers. If the program or the checker changes these move, and the prose
# in four files quotes them.
if ! grep -q '\[("q", 2)\], \["fs", "db"\], \[\], 24, \[2\]' conf-typing/ConfTyping/BigHandler.lean 2>/dev/null; then
  echo "DRIFT: bigHandler is cited as checking at budget 24 but the stated result changed"; fail=1
fi
if ! grep -q "rcostU 60 2 bigHandler" conf-typing/ConfTyping/BigHandler.lean 2>/dev/null; then
  echo "DRIFT: the real-vs-certified speculative cost measurement is cited but gone"; fail=1
fi

# stage 2g: the trace does not factor either.
for thm in "theorem secretCell_traceEq" "theorem the_load_is_certified" \
           "theorem traceEq_is_not_inductive" "theorem labInv_is_the_missing_hypothesis" \
           "theorem publicCell_labInv" "theorem traced_step_agrees"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/SpecFactor.lean 2>/dev/null; then
    echo "DRIFT: the trace-factoring stage is cited but '$thm' is missing"; fail=1
  fi
done
# the stage turns on TraceEq deliberately OMITTING SepInv and LabInv. If either is ever
# added to the structure the negative result becomes a statement about something else.
if grep -qE "^  (labInv|sepInv)" conf-typing/ConfTyping/SpecFactor.lean 2>/dev/null; then
  echo "DRIFT: TraceEq is cited as omitting SepInv/LabInv but now carries one"; fail=1
fi
if ! grep -q "structure TraceEq" conf-typing/ConfTyping/SpecFactor.lean 2>/dev/null; then
  echo "DRIFT: TraceEq is cited but no longer defined"; fail=1
fi

# stage 2f: attacking the trace conjecture.
for thm in "theorem deadS_is_certified" "theorem halted_machine_leaks_in_the_raw_model" \
           "theorem the_fix_closes_it" "theorem the_live_run_was_always_fine" \
           "theorem ptrLow_initial" "theorem ptrLow_is_not_implied_by_uLowEqA" \
           "theorem allocS_wants_a_secret_name" "theorem touched_agrees" \
           "theorem uexec_keeps_dead" "theorem ptrLow_step"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/SpecTrace.lean 2>/dev/null; then
    echo "DRIFT: the trace-conjecture stage is cited but '$thm' is missing"; fail=1
  fi
done
# the correction is the point of the stage: `touched` must stay conditioned on `dead`,
# and `touchedRaw` must survive so the retracted definition can still be pointed at.
if ! grep -q "if s.dead then \[\] else touchedRaw c s" conf-typing/ConfTyping/SpecUnified.lean 2>/dev/null; then
  echo "DRIFT: touched is cited as conditioned on dead but no longer is"; fail=1
fi
if ! grep -q "def touchedRaw" conf-typing/ConfTyping/SpecUnified.lean 2>/dev/null; then
  echo "DRIFT: the retracted touchedRaw is cited but has been deleted"; fail=1
fi

# stage 2e: what speculation costs, and what it cannot touch.
for thm in "theorem rollback_is_complete" "theorem archcost_window_free" \
           "theorem four_of_five_are_immune" "theorem ni_transfers_to_speculation" \
           "theorem spec_cost_bound" "theorem certified_cost_under_speculation" \
           "theorem fiveProg_costs_six_even_speculating" "theorem the_bound_is_not_vacuous"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/SpecBudget.lean 2>/dev/null; then
    echo "DRIFT: the speculation-cost stage is cited but '$thm' is missing"; fail=1
  fi
done
# the headline constant. If the bound is ever weakened the prose must move with it.
if ! grep -q "r.2.2.1 ≤ r.2.1 \* (1 + w)" conf-typing/ConfTyping/SpecBudget.lean 2>/dev/null; then
  echo "DRIFT: the k*(1+w) speculation cost bound is cited but not stated"; fail=1
fi
# stage 2d's faithfulness lemma was GENERALISED to every window in stage 2e, and both
# stages' prose now says so. Pin the general form so it cannot silently narrow again.
if ! grep -q "theorem spec_is_uexec_extended : ∀ (n w : Nat)" conf-typing/ConfTyping/SpecUnified.lean 2>/dev/null; then
  echo "DRIFT: spec_is_uexec_extended is cited as holding at every window but no longer quantifies over w"; fail=1
fi
# and the machine must still carry both costs, or the budget finding is unstateable.
if ! grep -q "def rcostU" conf-typing/ConfTyping/SpecUnified.lean 2>/dev/null || \
   ! grep -q "def acostU" conf-typing/ConfTyping/SpecUnified.lean 2>/dev/null; then
  echo "DRIFT: the architectural/real cost split is cited but one of acostU/rcostU is gone"; fail=1
fi

# stage 2d: speculation on the unified machine.
for thm in "theorem spec_is_uexec_extended" "theorem victimU_leaks" "theorem transSteps_le" \
           "theorem architecturally_indistinguishable_U" "theorem leak_needs_window_two_U" \
           "theorem gadget_rejected_by_memory_safety" "theorem secret_guard_rejected" \
           "theorem no_pointer_arithmetic_here" "theorem transient_work_is_off_the_budget" \
           "theorem branch_free_is_inert" "theorem fiveProg_is_speculatively_inert"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/SpecUnified.lean 2>/dev/null; then
    echo "DRIFT: the speculation-on-UCmd stage is cited but '$thm' is missing"; fail=1
  fi
done
# the stage's headline is a NEGATIVE result: the certified core rejects the gadget.
# If that ever flips to an acceptance the prose becomes false, so pin both halves.
if ! grep -q 'slcheck \["p"\] gadgetU = none' conf-typing/ConfTyping/SpecUnified.lean 2>/dev/null; then
  echo "DRIFT: 'the gadget is not certifiable' is cited but not stated"; fail=1
fi
if ! grep -q 'the conjecture worth trying next\|The conjecture worth trying next' conf-typing/ConfTyping/SpecUnified.lean 2>/dev/null; then
  echo "DRIFT: the open conjecture is cited but no longer recorded in SpecUnified.lean"; fail=1
fi

# stage 2c: the trusted base, computed from the program.
for thm in "theorem no_access_no_reads" "theorem unwritten_sink_untouched" \
           "theorem pureProg_needs_nothing" "theorem fiveProg_needs" \
           "theorem fiveProg_owes_the_filesystem_nothing" "theorem needs_is_syntactic" \
           "theorem an_fs_writer_is_charged" "theorem access_really_reads" \
           "theorem discharged_covers_needs" "theorem fiveProg_ledger" \
           "theorem pureProg_deployed_with_nothing" "theorem fiveProg_deployed_with_two"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/Assumptions.lean 2>/dev/null; then
    echo "DRIFT: the computed-trusted-base stage is cited but '$thm' is missing"; fail=1
  fi
done
# and the reduction it advertises: fiveProg pays two entries, not three.
if ! grep -q 'needsLedger D \[2\] "fs" fiveProg' conf-typing/ConfTyping/Assumptions.lean 2>/dev/null; then
  echo "DRIFT: the two-entry ledger for fiveProg is cited but not stated"; fail=1
fi

# stage 2b: the ownership invariant.
for thm in "theorem separation_is_not_conjunctive" "theorem union_gives_both" \
           "theorem alloc_frames_over_a_disjoint_set" "theorem free_is_the_obstruction" \
           "theorem free_frames_when_owned"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/Ownership.lean 2>/dev/null; then
    echo "DRIFT: the ownership stage is cited but '$thm' is missing"; fail=1
  fi
done

# stage 2a: two threads, and the obstruction.
for thm in "theorem interleaving_breaks_memory_safety" "theorem both_threads_are_certified" \
           "theorem budget_composes_across_threads" "theorem disjoint_threads_are_safe" \
           "theorem addresses_depend_on_the_schedule"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/Interleave.lean 2>/dev/null; then
    echo "DRIFT: the interleaving stage is cited but '$thm' is missing"; fail=1
  fi
done

# stage 1z: retiring secret addresses.
for thm in "theorem secretLifecycle_checks" "theorem free_has_no_level_condition" \
           "theorem public_is_recycled_secret_is_retired" \
           "theorem the_rule_is_no_longer_needed"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeapRetire.lean 2>/dev/null; then
    echo "DRIFT: address retirement is cited but '$thm' is missing"; fail=1
  fi
done

# stage 1y: attacking the labelled heap.
for thm in "theorem secret_write_is_not_vacuous" "theorem secret_cells_can_now_be_freed" \
           "theorem memory_safety_always_allowed_it" "theorem both_rules_are_load_bearing"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeapAttack.lean 2>/dev/null; then
    echo "DRIFT: the heap attack is cited but '$thm' is missing"; fail=1
  fi
done

# stage 1x: the invariant spent, and the heap becoming two-level.
for thm in "theorem secret_through_a_secret_pointer" "theorem the_heap_is_two_level" \
           "theorem public_pointer_still_cannot_carry_a_secret" \
           "theorem secret_cell_cannot_be_read_into_a_public_variable" \
           "theorem no_relabelling_operation_exists"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeapSecret.lean 2>/dev/null; then
    echo "DRIFT: the two-level heap is cited but '$thm' is missing"; fail=1
  fi
done

# stage 1w: per-address labels, the invariant half. The invariant itself lives in
# HeapJoint (it has to precede jsecTy_sound); the witnesses live in HeapLabel.
for thm in "theorem JSecTy.toLabInv" "theorem labInv_alloc"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeapJoint.lean 2>/dev/null; then
    echo "DRIFT: the label invariant is cited but '$thm' is missing"; fail=1
  fi
done
for thm in "theorem allocation_zeroes" "theorem allocation_site_must_match_the_level" \
           "theorem public_pointer_cannot_carry_a_secret"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeapLabel.lean 2>/dev/null; then
    echo "DRIFT: heap labels are cited but '$thm' is missing"; fail=1
  fi
done

# stage 1v: heap values, and the heap becoming public.
for thm in "theorem the_heap_is_live" "theorem wild_store_faults" \
           "theorem storing_a_secret_is_refused" \
           "theorem secret_pointer_needs_a_secret_destination" \
           "theorem memory_safety_extended_for_free"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeapValue.lean 2>/dev/null; then
    echo "DRIFT: heap values are cited but '$thm' is missing"; fail=1
  fi
done

# stage 1u: the reusing allocator and the channel it opened.
for thm in "theorem the_allocator_reuses" "theorem stale_pointer_refused_after_reuse" \
           "theorem freeing_a_secret_pointer_leaks" "theorem free_needs_no_level_condition" \
           "theorem freed_and_live_are_disjoint"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/Reuse.lean 2>/dev/null; then
    echo "DRIFT: the reusing allocator is cited but '$thm' is missing"; fail=1
  fi
done

# stage 1t: the attack record, and the three findings it produced.
for thm in "theorem twelve_attacks_refused" "theorem allcheck_NI_general" \
           "theorem secretTouching_NI_is_real" "theorem fresh_counter_is_monotone" "theorem initU_hides_string_inputs"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/Attack.lean 2>/dev/null; then
    echo "DRIFT: the attack record is cited but '$thm' is missing"; fail=1
  fi
done
# the vacuity correction must stay beside the claim it corrects
if ! grep -q "allcheck_NI_general" conf-typing/ConfTyping/AllFive.lean; then
  echo "DRIFT: AllFive states the initU-only NI guarantee without stage 1t's correction"; fail=1
fi

# composable core stage 1s: the deployment ledger.
for thm in "theorem sat_toLedger" "theorem deployment_reading" \
           "theorem machine_guarantees_need_no_deployment" \
           "theorem sink_assumption_is_load_bearing" "structure Discharged"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/Deploy.lean 2>/dev/null; then
    echo "DRIFT: the deployment ledger is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1r: loop rules for the string certificates.
for thm in "theorem TaintCert.loop" "theorem PathCert.loop" "theorem narrowEnv_spec" \
           "theorem tcheckW_sound" "theorem pcheckW_sound" \
           "theorem five_of_six_compose_over_loops"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/StringLoop.lean 2>/dev/null; then
    echo "DRIFT: the string loop rules are cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1q: path traversal.
for thm in "theorem pcheck_sound" "theorem pcheck_no_escape" "theorem path_escape_is_real" \
           "theorem path_escape_rejected" "theorem path_needs_the_taint_environment" \
           "theorem counting_cannot_decide_traversal"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/PathCert.lean 2>/dev/null; then
    echo "DRIFT: the traversal row is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1p: the observable sink and the five-way bundle.
for thm in "theorem xcheck_gives_five" "theorem emit_of_secret_rejected" \
           "theorem sanitising_does_not_declassify" "theorem factoring_holds_here" \
           "theorem fiveProg_five" "theorem fiveProg_runs"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/AllFive.lean 2>/dev/null; then
    echo "DRIFT: the five-certificate bundle is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1o: strings and the injection row.
for thm in "theorem tcheck_sound" "theorem tcheck_no_injection" \
           "theorem injection_is_real" "theorem injection_rejected" \
           "theorem sanitised_query_holds_under_every_input" "theorem injection_row"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/TaintCert.lean 2>/dev/null; then
    echo "DRIFT: the injection row is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1n: the merged checker and the loop asymmetry.
for thm in "theorem UCert.memop" "theorem allcheck_sound" "theorem allcheck_gives_four" \
           "theorem fullProg_four" "theorem only_the_budget_lacks_a_loop_rule" \
           "theorem loops_carry_three_of_four"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/FullCert.lean 2>/dev/null; then
    echo "DRIFT: the merged checker is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1m: allocator synchronisation, and what it rests on.
for thm in "theorem low_alloc_now_typable" "theorem allocation_sync_is_load_bearing" \
           "theorem high_branch_desynchronises_the_allocator" \
           "theorem highBranch_is_untypable" "theorem alloc_rule_rests_on_low_guards"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeapAlloc.lean 2>/dev/null; then
    echo "DRIFT: allocator synchronisation is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1l: widening for the tracked set.
for thm in "theorem narrowFix_spec" "theorem jcheckW_sound" "theorem jcheckW_out_of_fuel" \
           "theorem widening_beats_the_exact_rule" "theorem narrowing_budget_is_computed"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeapWiden.lean 2>/dev/null; then
    echo "DRIFT: the widening step is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1k: the joint indexed judgment.
for thm in "theorem jsecTy_sound" "theorem jcheck_sound" "theorem jcheck_gives_both" \
           "theorem indexed_beats_the_conjunction" "theorem allocating_loop_rejected" \
           "theorem SepCert.loop"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeapJoint.lean 2>/dev/null; then
    echo "DRIFT: the joint judgment is cited but '$thm' is missing"; fail=1
  fi
done

# composable core stage 1j: heap NI, and the non-factoring finding.
for thm in "theorem deref_leaks_through_dead" "theorem deref_NI_given_safety" \
           "theorem ni_and_memory_do_not_factor" "theorem allocL_would_be_unsound" \
           "theorem heapProg_two_certificates"; do
  if ! grep -q "$thm" conf-typing/ConfTyping/HeapNI.lean 2>/dev/null; then
    echo "DRIFT: the heap-NI finding is cited but '$thm' is missing"; fail=1
  fi
done
# and the independence claim must stay qualified at both sites that make it
for f in transport-calculus/TransportCalculus.lean conf-typing/ConfTyping/BundleLedger.lean; do
  if ! grep -q "ni_and_memory_do_not_factor" "$f"; then
    echo "DRIFT: $f states the no-interaction claim without stage 1j's qualification"; fail=1
  fi
done

# required README headings: a splice that consumes its own anchor is a real failure
# mode (it happened in stage 1i), and nothing else here would notice.
while IFS='|' read -r f h; do
  if ! grep -qF "$h" "$f"; then
    echo "DRIFT: $f lost the heading '$h' - an edit probably consumed its anchor"; fail=1
  fi
done <<'HEADINGS'
conf-typing/README.md|## §11 pre-mechanization checklist (framework doc)
conf-typing/README.md|## Not yet mechanized (the honest residue)
VULN-COVERAGE.md|## 2½. How classes are counted
README.md|## What each sub-project actually proves
README.md|## Scope — what is *not* claimed
HEADINGS

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
for mod in AliasLoop LexReal QueryGrammar CmdInjection DecimalId LogInjection AliasFix QueryEscape Race Speculate CostBound Mediation Unified Bundle UnifiedNI BundleLedger BundleLoop BundleCoverage MemCert MemLinear HeapNI HeapJoint HeapWiden HeapAlloc FullCert TaintCert AllFive PathCert StringLoop Deploy Attack Reuse HeapValue HeapLabel HeapSecret HeapAttack HeapRetire Interleave Ownership Assumptions SpecUnified SpecBudget SpecTrace SpecFactor BigHandler SpecFused CountedLoop; do
  if grep -q "$mod.lean" VULN-COVERAGE.md && \
     ! grep -q "import ConfTyping.$mod" conf-typing/ConfTyping.lean 2>/dev/null; then
    echo "DRIFT: $mod.lean cited in VULN-COVERAGE but not imported by the ConfTyping root"; fail=1
  fi
done

# 1b. No stray Lean files at the repo root. Running `printf >> ConfTyping.lean` from the
# wrong directory has created one four times; the module-import guard catches the missing
# import but not the debris, so catch the debris here.
for f in *.lean; do
  [ -e "$f" ] || continue
  echo "DRIFT: stray Lean file at the repo root: $f (a package root belongs in its subdir)"; fail=1
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
