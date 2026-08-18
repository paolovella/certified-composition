/-
  The duplication is fixable for exactly one of the four bases, and that one is ours.

  `jcomp_every_entry_inert` showed composition destroying minimality: two components
  verified under the same assumptions compose to a ledger carrying both copies, and every
  entry becomes redundant. The obstruction recorded there was that `List Prop` cannot be
  deduplicated computably — `Classical.decEq` exists but does not run, and a ledger that
  cannot be emitted is not an SBOM.

  That was right about `List Prop` and wrong about this repo, which is worth having
  found. **A base built by mapping an *index* into `Prop` can be deduplicated at the
  index.** Surveying the four bases:

  | base | index | `DecidableEq` | dedupable |
  |---|---|---|---|
  | `needsLedger` (ours) | **`Assume`** | **derived** | **yes** |
  | `JasminTrust.needs` | none — `List Prop` built directly | — | no |
  | `CNTrust.needs` | none | — | no |
  | `toLedger` (Deploy) | none | — | no |

  `Assume` derives `Repr, DecidableEq`, and `needsLedger D Ks fs c = (needs c).map
  (entryProp D Ks fs)`. The propositions are the *image*; the index is a finite datatype
  with an equality that runs. Jasmin's `baseLabels` is the nearest thing elsewhere and it
  is a **parallel list tied only by length** (`baseLabels_length`) — you cannot recover
  which proposition a label names, so it cannot drive a deduplication.

  ── The measurement that prompted this ──
  `needs_seq_duplicates`: composing `fiveProg` with itself gives
  `[policyIntended, sinkHonest "db", sinkHonest "db"]`. **The policy entry is already
  deduplicated by construction** — `hasAccess (seq c₁ c₂)` is an `||`, so it contributes
  one entry however many reads there are — while `sinksOf` appends and duplicates. So
  `needs` was half-right by accident of how the two clauses were written, and nobody had
  noticed either half.

  ── What is proved ──
  * `sat_map_eraseDups` — deduplicating the index does not change what is assumed. The
    conditional certificate is untouched, so this is a change to the *accounting* only.
  * `seq_third_entry_inert` — the duplicated entry does no work, for any goal the
    two-entry base already forces.
  * `needsLedgerD_of_seq_is_fiveBase` — the deduplicated base of `fiveProg ; fiveProg` is
    exactly `fiveProg`'s own, so `fiveProg_base_is_load_bearing` transfers and the
    composite base is minimal after the fix.
-/
import ConfTyping.LoadBearing

namespace ConfTyping

/-! ## `Sat` sees a ledger as a set -/

/-- Satisfaction is membership-determined: a ledger is satisfied exactly when each of
    its entries holds. This is what makes duplication invisible to the guarantee and
    visible only to the accounting. -/
theorem sat_iff_forall_mem : ∀ (Γ : Ledger), Sat Γ ↔ ∀ p ∈ Γ, p
  | []      => by simp [Sat]
  | q :: qs => by
      simp only [Sat, List.mem_cons]
      constructor
      · rintro ⟨hq, hqs⟩ r (rfl | hr)
        · exact hq
        · exact (sat_iff_forall_mem qs).mp hqs r hr
      · intro h
        exact ⟨h q (Or.inl rfl),
               (sat_iff_forall_mem qs).mpr fun r hr => h r (Or.inr hr)⟩

/-- A ledger whose entries all occur in a satisfied one is satisfied. -/
theorem sat_of_subset {Γ Δ : Ledger} (h : ∀ p ∈ Γ, p ∈ Δ) (hd : Sat Δ) : Sat Γ :=
  (sat_iff_forall_mem Γ).mpr fun p hp => (sat_iff_forall_mem Δ).mp hd p (h p hp)

/-! ## Deduplicating the index is invisible to the guarantee -/

/-- **The lemma that makes the fix safe.** Deduplicating at the index and then
    interpreting gives the same assumption content as interpreting the raw list. So a
    deduplicated base assumes neither more nor less — only the accounting changes, which
    is exactly what `Minimal` measures and `Sat` does not. -/
theorem sat_map_eraseDups {ι : Type} [DecidableEq ι] (f : ι → Prop) (l : List ι) :
    Sat ((l.eraseDups).map f) ↔ Sat (l.map f) := by
  constructor
  · refine fun h => sat_of_subset (fun p hp => ?_) h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact List.mem_map.mpr ⟨a, List.mem_eraseDups.mpr ha, rfl⟩
  · refine fun h => sat_of_subset (fun p hp => ?_) h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact List.mem_map.mpr ⟨a, List.mem_eraseDups.mp ha, rfl⟩

/-! ## The measurement -/

/-- **`needs` is half-deduplicated, by accident of how its two clauses are written.**
    The policy entry comes from `if hasAccess c` and `hasAccess` on a `seq` is an `||`,
    so it contributes one entry however many mediated reads the program makes. `sinksOf`
    appends, so emitting to the same sink twice is charged twice. -/
theorem needs_seq_duplicates :
    needs (UCmd.seq fiveProg fiveProg)
      = [Assume.policyIntended, Assume.sinkHonest "db", Assume.sinkHonest "db"] := by
  decide

/-- The half that was already right, isolated: two mediated reads, one policy entry. -/
theorem policy_entry_not_duplicated :
    needs (UCmd.seq (.access "db") (.access "db")) = [Assume.policyIntended] := by decide

/-! ## The fix -/

/-- The deduplicated index. `Assume`'s derived `DecidableEq` is what makes this compute. -/
def needsD (c : UCmd) : List Assume := (needs c).eraseDups

/-- The deduplicated ledger — `needsLedger` with the duplication removed before the
    propositions are formed. -/
def needsLedgerD (D : Deployment) (Ks : List Nat) (fs : String) (c : UCmd) : Ledger :=
  (needsD c).map (entryProp D Ks fs)

/-- **Nothing about what is assumed changes.** So every conditional certificate stated
    against `needsLedger` holds against `needsLedgerD` and back, and this is a change to
    the bill rather than to the trust. -/
theorem sat_needsLedgerD_iff (D : Deployment) (Ks : List Nat) (fs : String) (c : UCmd) :
    Sat (needsLedgerD D Ks fs c) ↔ Sat (needsLedger D Ks fs c) :=
  sat_map_eraseDups (entryProp D Ks fs) (needs c)

/-- And on the composite it really does shrink: three entries to two. -/
theorem needsD_seq : needsD (UCmd.seq fiveProg fiveProg)
    = [Assume.policyIntended, Assume.sinkHonest "db"] := by decide

/-! ## The payoff: minimality restored -/

/-- The undeduplicated base of `fiveProg ; fiveProg`. -/
def seqBase (D : Deployment) : Ledger := needsLedger D [2] "fs" (UCmd.seq fiveProg fiveProg)

/-- The deduplicated one. -/
def seqBaseD (D : Deployment) : Ledger := needsLedgerD D [2] "fs" (UCmd.seq fiveProg fiveProg)

theorem seqBase_size : LedgerSize seqBase 3 := fun _ => rfl
theorem seqBaseD_size : LedgerSize seqBaseD 2 := fun _ => rfl

/-- **The deduplicated base is `fiveProg`'s own base.** Composing a program with itself
    adds nothing to the bill once duplication is removed — which is the statement the
    unfixed accounting could not make. -/
theorem seqBaseD_eq_fiveBase (D : Deployment) : seqBaseD D = fiveBase D := by
  show (needsD (UCmd.seq fiveProg fiveProg)).map (entryProp D [2] "fs") = _
  rw [needsD_seq]
  show _ = (needs fiveProg).map (entryProp D [2] "fs")
  rw [fiveProg_needs]

/-- **The duplicated entry does no work** — for any goal the two-entry base already
    forces, and `fiveProg_deployed_with_two` supplies one. Erasing index 2 leaves exactly
    `fiveProg`'s base. -/
theorem seq_third_entry_inert {goal : Deployment → Prop}
    (h : ∀ D, Sat (fiveBase D) → goal D) : ¬ LoadBearingAt seqBase goal 2 :=
  not_loadBearingAt_of_suffices h

/-- So the undeduplicated composite base is **not minimal**, instantiated at the goal
    `fiveProg` already carries. -/
theorem seqBase_not_minimal : ¬ Minimal seqBase fiveGoal 3 := fun hm =>
  seq_third_entry_inert
    (fun D hsat => ⟨(fiveProg_deployed_with_two D hsat).1,
                    (fiveProg_deployed_with_two D hsat).2.1⟩)
    (hm.2 2 (by omega))

/-- **And the deduplicated one is**, by transport from `fiveProg`'s own result — the fix
    delivers, rather than merely being shorter. -/
theorem seqBaseD_minimal : Minimal seqBaseD fiveGoal 2 := by
  refine ⟨seqBaseD_size, fun i hi => ?_⟩
  have hEq : seqBaseD = fiveBase := funext seqBaseD_eq_fiveBase
  rw [hEq]
  exact fiveProg_base_is_load_bearing i hi

/-! ## What this settles, and what it leaves

    **Settles.** The duplication `jcomp_every_entry_inert` exposed is a defect of the
    *representation*, not of the composition law, and for our own base it is repairable
    with an equality that runs. `sat_map_eraseDups` proves the repair is invisible to
    every conditional certificate, so it can be adopted without restating anything.

    **Leaves.** Three of the four bases still build `List Prop` directly and cannot be
    repaired this way — not for want of a lemma but for want of an index. The general
    shape is the one `Assumptions.lean` already found: a finite datatype of obligations
    with `DecidableEq`, plus an interpretation into `Prop`. `CNTrust` and `JasminTrust`
    would each need theirs, and Jasmin's `baseLabels` is a hint that the entries already
    have names — they are just carried beside the ledger rather than indexing it.

    **Not retrofitted.** `needsLedger` is unchanged and every existing theorem still
    speaks about it. `needsLedgerD` is offered beside it with the equivalence proved;
    switching the repo over is a separate decision, and making it silently would hide
    that the accounting was wrong for as long as it was. -/

end ConfTyping
