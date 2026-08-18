/-
  The first computed base that is *minimal*, and it belongs to a foreign tool.

  `LoadBearing` has so far produced one positive result about our own programs
  (`fiveProg`, `emitProg`) and one negative about our plumbing
  (`ofCN_ledger_inert_for_its_own_guarantee`: a reception that takes its hypothesis
  unconditionally can never have a minimal base). Jasmin is the case where it can say
  something affirmative about somebody else's trusted base, and the reason is structural.

  `CNTrust.needs` keys on `usesArith`, a flag about how a proof was discharged — whether
  the solver was called. Nothing in this repo can say what the solver's soundness *does*,
  so its load-bearingness is CN's soundness theorem and not ours.

  `JasminTrust.needs` keys on `aboutAssembly`, which is a claim about **what the
  guarantee is about** — the Jasmin source, or the emitted assembly. That distinction is
  modellable without formalizing Jasmin's type system, because the whole content of the
  third assumption is that it *carries a source-level claim to the compiled artifact*.
  POPL 2025 is exactly an implication, and an implication can be a hypothesis with
  structure rather than an opaque `Prop`.

  ── What is proved ──
  * `needs true` is **minimal for the assembly claim**: all three entries bear weight.
  * `needs true` is **not minimal for the source claim**: `preservation` is inert, which
    is `jasmin_base_strictly_smaller` upgraded from "a smaller base is satisfiable" to
    "the larger base contains an entry that does no work".
  * `needs false` is **minimal for the source claim**: both entries bear.

  So `JasminTrust.needs` charges exactly the assumptions its claim depends on, in both
  directions, and the `aboutAssembly` switch is doing real work rather than bookkeeping.

  ── What this rests on, stated before the theorems ──
  `JasminReading` is **our model of what Jasmin's three assumptions mean**, supplied as a
  parameter in the same style as `CNTrust` and `JasminTrust` themselves — this module
  asserts none of them. Minimality is therefore relative to that reading: a weaker
  reading (one that did not route the assembly claim through the source claim) could make
  an entry inert. What is established is that **under the natural reading of the three
  assumptions, the computed base has no junk** — which is the first affirmative check of
  a computed base in this repo, and is a statement about the encoding rather than about
  Jasmin's implementation.
-/
import ConfTyping.JasminCert
import ConfTyping.LoadBearing

namespace ConfTyping

/-! ## What the assumptions are assumptions *about* -/

/-- The two claims a Jasmin SCT result can be: about the source, or about what the
    compiler emitted. -/
structure JasminClaim where
  /-- Speculative constant-time holds of the Jasmin source program. -/
  sourceSCT : Prop
  /-- It holds of the assembly the compiler emitted. -/
  asmSCT    : Prop

/-- **The natural reading of the three assumptions.** The type system plus the
    speculative semantics establish the source-level property; preservation carries it
    to the assembly. Both are implications, which is what makes the entries' work
    statable at all. Parameters, not axioms: nothing here asserts either. -/
structure JasminReading (T : JasminTrust) (C : JasminClaim) : Prop where
  /-- S&P 2023 plus a faithful speculative semantics give the source-level claim. -/
  source_of_typeSystem : T.typeSystem → T.specSem → C.sourceSCT
  /-- POPL 2025 carries it to the compiled artifact. -/
  asm_of_preservation  : C.sourceSCT → T.preservation → C.asmSCT

/-- A world: a trust setting, a claim, and the reading tying them together. -/
structure JWorld where
  trust   : JasminTrust
  claim   : JasminClaim
  reading : JasminReading trust claim

/-- The base Jasmin's own accounting charges, as a ledger-maker over worlds. -/
def jbase (aboutAssembly : Bool) (w : JWorld) : Ledger := w.trust.needs aboutAssembly

def sourceGoal (w : JWorld) : Prop := w.claim.sourceSCT
def asmGoal    (w : JWorld) : Prop := w.claim.asmSCT

/-! ## Worlds

Each names one assumption that fails; the reading makes the corresponding claim fail
with it. All are built from `True`/`False`, so the reading's obligations are discharged
vacuously and nothing is smuggled in. -/

/-- Everything holds — the non-vacuity witness. -/
def jAllTrue : JWorld where
  trust   := { typeSystem := True, specSem := True, preservation := True }
  claim   := { sourceSCT := True, asmSCT := True }
  reading := ⟨fun _ _ => trivial, fun _ _ => trivial⟩

/-- The type system is unsound: neither claim survives. -/
def jNoTypeSystem : JWorld where
  trust   := { typeSystem := False, specSem := True, preservation := True }
  claim   := { sourceSCT := False, asmSCT := False }
  reading := ⟨fun h _ => h, fun h _ => h⟩

/-- The speculative semantics is wrong: neither claim survives. -/
def jNoSpecSem : JWorld where
  trust   := { typeSystem := True, specSem := False, preservation := True }
  claim   := { sourceSCT := False, asmSCT := False }
  reading := ⟨fun _ h => h, fun h _ => h⟩

/-- **The interesting one.** The type system and the semantics are fine, so the source
    claim holds; preservation fails, so the assembly claim does not. This is the world
    `jasmin_base_strictly_smaller` gestures at, with the claims made explicit. -/
def jNoPreservation : JWorld where
  trust   := { typeSystem := True, specSem := True, preservation := False }
  claim   := { sourceSCT := True, asmSCT := False }
  reading := ⟨fun _ _ => trivial, fun _ h => h⟩

/-! ## `needs true` is minimal for the assembly claim -/

theorem jasmin_asm_entry0 : LoadBearingAt (jbase true) asmGoal 0 :=
  ⟨jNoTypeSystem, ⟨trivial, trivial, trivial⟩, id⟩

theorem jasmin_asm_entry1 : LoadBearingAt (jbase true) asmGoal 1 :=
  ⟨jNoSpecSem, ⟨trivial, trivial, trivial⟩, id⟩

theorem jasmin_asm_entry2 : LoadBearingAt (jbase true) asmGoal 2 :=
  ⟨jNoPreservation, ⟨trivial, trivial, trivial⟩, id⟩

theorem jbase_true_size : LedgerSize (jbase true) 3 := fun _ => rfl

/-- **The first computed base in this repo proved minimal.** All three entries of a
    Jasmin assembly-level claim's base bear weight: drop any one and there is a world
    satisfying the other two where the claim fails. -/
theorem jasmin_asm_base_is_minimal : Minimal (jbase true) asmGoal 3 :=
  ⟨jbase_true_size, fun i hi => by
    match i with
    | 0     => exact jasmin_asm_entry0
    | 1     => exact jasmin_asm_entry1
    | 2     => exact jasmin_asm_entry2
    | _ + 3 => exact absurd hi (by omega)⟩

/-! ## `needs false` is minimal for the source claim -/

theorem jasmin_src_entry0 : LoadBearingAt (jbase false) sourceGoal 0 :=
  ⟨jNoTypeSystem, ⟨trivial, trivial⟩, id⟩

theorem jasmin_src_entry1 : LoadBearingAt (jbase false) sourceGoal 1 :=
  ⟨jNoSpecSem, ⟨trivial, trivial⟩, id⟩

theorem jbase_false_size : LedgerSize (jbase false) 2 := fun _ => rfl

/-- And the source-level base is minimal too — so `needs` is not merely smaller in the
    source case, it is exactly right in both. -/
theorem jasmin_src_base_is_minimal : Minimal (jbase false) sourceGoal 2 :=
  ⟨jbase_false_size, fun i hi => by
    match i with
    | 0     => exact jasmin_src_entry0
    | 1     => exact jasmin_src_entry1
    | _ + 2 => exact absurd hi (by omega)⟩

/-! ## And charging the assembly base to a source claim is provably junk -/

/-- **`preservation` does no work for a source-level claim.** The first two entries
    already deliver it through the reading, so `not_loadBearingAt_of_suffices` applies.
    This is `jasmin_base_strictly_smaller` upgraded: that theorem says a smaller base is
    *satisfiable*; this says the larger base contains an entry that does *nothing*. -/
theorem preservation_inert_for_source : ¬ LoadBearingAt (jbase true) sourceGoal 2 :=
  not_loadBearingAt_of_suffices fun w hsat =>
    w.reading.source_of_typeSystem hsat.1 hsat.2.1

/-- So the fixed base is not minimal for a source-level claim, which is the whole point
    of `needs` keying on `aboutAssembly`. -/
theorem jasmin_fixed_base_not_minimal_for_source :
    ¬ Minimal (jbase true) sourceGoal 3 :=
  fun h => preservation_inert_for_source (h.2 2 (by omega))

/-! ## Non-vacuity

Both goals hold somewhere, so the witnesses above refute something real; and both fail
somewhere, so neither is trivially true. -/

theorem jasmin_goals_satisfiable : sourceGoal jAllTrue ∧ asmGoal jAllTrue :=
  ⟨trivial, trivial⟩

theorem jasmin_goals_refutable : ¬ sourceGoal jNoTypeSystem ∧ ¬ asmGoal jNoPreservation :=
  ⟨id, id⟩

/-- And the two goals are genuinely different: `jNoPreservation` separates them. A base
    minimal for one need not be minimal for the other, which is exactly what the two
    results above exhibit. -/
theorem source_and_asm_differ : sourceGoal jNoPreservation ∧ ¬ asmGoal jNoPreservation :=
  ⟨trivial, id⟩

/-! ## Tying the composite's ledger to the computed base

`JasminCert.compose` takes two ledgers as parameters, exactly as `Bridge.ofCN` did. The
same fix applies, and here it is cheap because `compose` is a data combinator rather
than a certified morphism — there is no guarantee for the ledger to be inert *for*, only
an accounting to get right. -/

/-- Compose two consumed certificates carrying **computed** bases: each side's base is
    read off whether its claim is about the assembly. -/
def composeComputed (T : JasminTrust) (asmA asmB : Bool) (a b : JasminCert) : Composite :=
  compose a b (T.needs asmA) (T.needs asmB)

/-- The composite's base is the append of two computed bases — `compose_ledger` with
    both sides now things the accounting derived rather than things a caller supplied. -/
theorem composeComputed_ledger (T : JasminTrust) (asmA asmB : Bool) (a b : JasminCert) :
    (composeComputed T asmA asmB a b).ledger = T.needs asmA ++ T.needs asmB := rfl

/-- And the guarantee half is untouched, so this is the same combinator with the
    accounting tied down. -/
theorem composeComputed_lvl (T : JasminTrust) (asmA asmB : Bool) (a b : JasminCert) :
    (composeComputed T asmA asmB a b).lvl = (compose a b [] []).lvl
  ∧ (composeComputed T asmA asmB a b).modmsf = (compose a b [] []).modmsf := ⟨rfl, rfl⟩

/-- **A source-level composite is charged four entries, not six.** Two certificates
    about Jasmin source share the shape of their bases and neither pays for the
    preservation theorem — the reduction surviving composition, which is what
    `cn_comp_base_strictly_smaller` checks for the other tool. -/
theorem composeComputed_source_avoids_preservation (T : JasminTrust) (a b : JasminCert) :
    (composeComputed T false false a b).ledger
      = [T.typeSystem, T.specSem, T.typeSystem, T.specSem] := rfl

/-! ## What this establishes, and what it does not

    **Establishes.** A computed trusted base belonging to a *foreign* tool is minimal for
    the claim it is charged against, in both settings of the switch that computes it, and
    the fixed base provably contains junk for the source-level claim. Every witness is
    built from `True`/`False`, so nothing about Jasmin is assumed beyond the reading.

    **Does not establish.** Minimality is relative to `JasminReading`. That structure is
    this repo's model of what S&P 2023 and POPL 2025 do, written down as a parameter
    rather than derived; a reading that did not route the assembly claim through the
    source claim could make an entry inert. Nothing here re-verifies Jasmin, its type
    system, or its compiler, and `JasminCert.lean`'s division of labour is unchanged.

    **What the check actually measures, said plainly.** `JasminReading` constrains the
    claims only *from below* — both fields are implications *into* `sourceSCT` and
    `asmSCT` — so a world may set a claim false whenever its antecedents fail. That makes
    a positive load-bearing witness cheap to build, and the three above are cheap. The
    substance is in the **negative**: `preservation_inert_for_source` cannot be witnessed
    at all, because the reading forces the source claim out of the other two entries. So
    what `Minimal` measures here is the reading's *implication structure* — an entry
    bears exactly when the remaining entries do not already force the goal — and that is
    the right target precisely because the tool's internals are out of scope. The
    asymmetry is worth stating: the affirmative results are a sanity check, the inertness
    result is the one that could have come out either way.

    **Why this one worked when CN did not.** `CNTrust.needs` keys on *how a proof was
    discharged*; saying what the solver's soundness does would be restating CN's
    soundness theorem. `JasminTrust.needs` keys on *what the claim is about*, and that is
    a distinction expressible in one implication. The lesson is about which computed
    bases admit a minimality check at all, and it is a property of the switch rather than
    of the tool. -/

end ConfTyping
