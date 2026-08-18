/-
  Giving the other bases the index ours already had — and closing the junk composite.

  `LedgerDedup` found that a base can be deduplicated exactly when it is built by mapping
  an *index* into `Prop`, and that only `needsLedger` was. The other three build
  `List Prop` directly, so `jcomp_every_entry_inert` — two Jasmin certificates composing
  to four entries, none of which does any work — had no repair available.

  It does now. The index is three constructors, and the payoff is that the defect closes:
  `jcompD_minimal` proves the deduplicated composite base of two source-level Jasmin
  certificates is `jbase false` itself, hence minimal, hence the accumulation is finally
  saying something true about a supply chain of components verified by one tool.

  ── The pattern, stated once ──
  A base is *indexed* when it factors as `(idx : List ι).map (interp : ι → Prop)` with
  `DecidableEq ι`. Then:

  * `sat_map_eraseDups` says deduplicating the index changes nothing about what is
    assumed, so the repair is invisible to every conditional certificate;
  * the index is a finite datatype, so it is `Repr`-printable — the emitted bill and the
    ledger are the *same object* at two resolutions rather than two lists tied by length,
    which is what `baseLabels` failed to be.

  ── What this closes and what it does not ──
  **Jasmin**: the composite base becomes minimal (`jcompD_minimal`). This is the defect
  from `jcomp_every_entry_inert` repaired, not merely diagnosed.

  **CN**: dedupable and printable, but **no minimality follows** — `CNLedger` proved the
  unconditional reception can never have a minimal base, and an index does not change
  that. The asymmetry is the point: indexing is necessary for a truthful bill and is not
  sufficient for a minimal one.

  Neither `JasminTrust.needs` nor `CNTrust.needs` is modified. The indexed forms are
  proved *equal* to them (`jNeedsI_eq`, `cnNeedsI_eq`), so nothing downstream moves and
  the equality is checkable rather than asserted.
-/
import ConfTyping.JasminLedger
import ConfTyping.CNLedger
import ConfTyping.LedgerDedup

namespace ConfTyping

/-! ## Jasmin's index -/

/-- The three obligations behind a Jasmin SCT verdict, as a datatype rather than as three
    fields of `Prop`. `DecidableEq` is what the deduplication needs; `Repr` is what an
    emitted bill needs. -/
inductive JAssume where
  | typeSystem
  | specSem
  | preservation
  deriving Repr, DecidableEq

/-- The interpretation into `JasminTrust`'s fields. -/
def JasminTrust.interp (T : JasminTrust) : JAssume → Prop
  | .typeSystem   => T.typeSystem
  | .specSem      => T.specSem
  | .preservation => T.preservation

/-- The index `JasminTrust.needs` was computing all along, made explicit. Note it does
    not mention a `JasminTrust` at all: *which* obligations a claim incurs is independent
    of what they say. -/
def jNeedsIdx (aboutAssembly : Bool) : List JAssume :=
  [.typeSystem, .specSem] ++ (if aboutAssembly then [.preservation] else [])

def JasminTrust.needsI (T : JasminTrust) (b : Bool) : Ledger :=
  (jNeedsIdx b).map T.interp

/-- **The indexed base is the base.** Nothing downstream changes. -/
theorem jNeedsI_eq (T : JasminTrust) (b : Bool) : T.needsI b = T.needs b := by
  cases b <;> rfl

/-- **What deduplication actually needs**, and what `List Prop` cannot supply: the
    entries are distinguishable by an equality that *runs*. Stated as a `decide` rather
    than by pinning `repr`'s output, which would make the theorem hostage to the
    pretty-printer; printability is carried by `deriving Repr` on the datatype itself. -/
theorem jNeedsIdx_distinguishable :
    (jNeedsIdx true).length = 3
  ∧ (jNeedsIdx false).length = 2
  ∧ decide (JAssume.typeSystem = JAssume.specSem) = false := by decide

/-! ## The composite, deduplicated -/

/-- Composing two claims: append the indices, then remove duplicates — which is the step
    `List Prop` could not take. -/
def jCompIdx (asmA asmB : Bool) : List JAssume :=
  (jNeedsIdx asmA ++ jNeedsIdx asmB).eraseDups

/-- The deduplicated composite base of two source-level claims, over a world. -/
def jcompBaseD (w : JWorld) : Ledger := (jCompIdx false false).map w.trust.interp

/-- **Four entries become two**, and the two are exactly the component base. -/
theorem jcompBaseD_eq_jbase (w : JWorld) : jcompBaseD w = jbase false w := by
  show (jCompIdx false false).map w.trust.interp = _
  rw [show jCompIdx false false = [JAssume.typeSystem, JAssume.specSem] from by decide]
  rfl

theorem jcompBaseD_size : LedgerSize jcompBaseD 2 := by
  intro w; rw [jcompBaseD_eq_jbase]; rfl

/-- **Nothing about what is assumed changes.** The deduplicated composite assumes exactly
    what the appended one did, so this repairs the bill and not the trust. -/
theorem sat_jcompBaseD_iff (T : JasminTrust) :
    Sat ((jCompIdx false false).map T.interp)
      ↔ Sat (T.needs false ++ T.needs false) := by
  rw [show T.needs false ++ T.needs false
        = (jNeedsIdx false ++ jNeedsIdx false).map T.interp from by
        rw [List.map_append, ← JasminTrust.needsI, jNeedsI_eq]]
  exact sat_map_eraseDups T.interp (jNeedsIdx false ++ jNeedsIdx false)

/-- **The defect closes.** `jcomp_every_entry_inert` proved the appended composite base
    has four entries and no work in any of them. Deduplicated, it is the component base
    and it is minimal — so a supply chain of components verified by one tool is charged
    that tool's assumptions **once**, which is what the accumulation was always supposed
    to be saying. -/
theorem jcompD_minimal : Minimal jcompBaseD sourceGoal 2 := by
  refine ⟨jcompBaseD_size, fun i hi => ?_⟩
  have hEq : jcompBaseD = jbase false := funext jcompBaseD_eq_jbase
  rw [hEq]
  exact jasmin_src_base_is_minimal.2 i hi

/-- Stated against the defect it repairs, so the pair can be read in one place. -/
theorem dedup_repairs_the_composite (a b : JasminCert) :
    (¬ Minimal (jcompBase a b) sourceGoal 4) ∧ Minimal jcompBaseD sourceGoal 2 :=
  ⟨fun h => jcomp_every_entry_inert a b 0 (by omega) (h.2 0 (by omega)), jcompD_minimal⟩

/-! ## CN's index

Same construction, and deliberately without the payoff — `CNLedger` proved an
unconditional reception can never have a minimal base, and indexing does not change
that. What indexing buys here is a bill that can be printed and deduplicated, which is
worth having on its own and is all that is claimed. -/

/-- CN's obligations. The `trustedSpec` constructor carries the spec's name, so two
    references to one trusted spec are recognisably the same entry. -/
inductive CNAssume where
  | cerberus
  | vcgen
  | smt
  | trustedSpec : String → CNAssume
  deriving Repr, DecidableEq

def CNTrust.interp (T : CNTrust) : CNAssume → Prop
  | .cerberus       => T.cerberus
  | .vcgen          => T.vcgen
  | .smt            => T.smt
  | .trustedSpec s  => T.trusted s

/-- The index `CNTrust.needs` computes. -/
def cnNeedsIdx (pf : CNProof) : List CNAssume :=
  [.cerberus, .vcgen]
    ++ (if pf.usesArith then [CNAssume.smt] else [])
    ++ pf.trustedSpecs.map CNAssume.trustedSpec

def CNTrust.needsI (T : CNTrust) (pf : CNProof) : Ledger :=
  (cnNeedsIdx pf).map T.interp

/-- **The indexed base is the base**, for every proof record. -/
theorem cnNeedsI_eq (T : CNTrust) (pf : CNProof) : T.needsI pf = T.needs pf := by
  cases pf with
  | mk usesArith trustedSpecs =>
      cases usesArith <;>
        simp [CNTrust.needsI, cnNeedsIdx, CNTrust.needs, CNTrust.interp,
              List.map_map, Function.comp]

/-- And a CN composite deduplicates: two frame-only proofs share their whole base, and
    the deduplicated index is that base once. -/
theorem cn_frameOnly_compIdx :
    (cnNeedsIdx frameOnlyProof ++ cnNeedsIdx frameOnlyProof).eraseDups
      = [CNAssume.cerberus, CNAssume.vcgen] := by decide

/-- Stated with its limit attached, so the asymmetry with Jasmin is not lost: the CN
    composite is deduplicable and still admits no minimality result, because the
    reception it belongs to takes its hypothesis unconditionally. -/
theorem cn_dedup_without_minimality
    {f : CStore → CStore} {F : Footprint} (h : ModifiesOnly f F) :
    ((cnNeedsIdx frameOnlyProof ++ cnNeedsIdx frameOnlyProof).eraseDups).length = 2
  ∧ ∀ (mkΓ : CNTrust → Ledger) (i : Nat), ¬ LoadBearingAt mkΓ (fun _ => Frame f F) i :=
  ⟨by decide, fun mkΓ i => ofCN_ledger_inert_for_its_own_guarantee h mkΓ i⟩

/-! ## The invariant, now checkable

    Every base in the repo factors through an index with `DecidableEq`:
    `Assume` (ours), `JAssume`, `CNAssume`. `toLedger` is the remaining exception and it
    is a *fixed* base — three entries charged unconditionally — so it has nothing to
    deduplicate and `needsLedger` supersedes it for every program that has been measured.

    **What is claimed.** Indexing is necessary for a bill that can be printed and
    deduplicated, and for Jasmin it closes a proved defect. **What is not.** Indexing does
    not make a base minimal — CN is the witness, and the reason is a property of the
    reception rather than of the representation. -/

end ConfTyping
