/-
  A shared obligation vocabulary — proposed, measured, and mostly killed.

  `minimal_pair` composes minimality across **independent** worlds, and independence is
  the formal content of "the two tools' assumptions have nothing to do with each other".
  The gap recorded there was the realistic-looking case: two tools that *share* an
  assumption — both trusting the same C semantics, say — are not independent, and neither
  `minimal_pair` (worlds not independent) nor `jcompD_minimal` (no shared index) covers
  them. The proposed repair was a common obligation datatype across foreign tools.

  **The measurement comes before the machinery, and it mostly kills it.** Embedding both
  existing foreign bases into one vocabulary and checking for collisions: **there are
  none.** CN's obligations and Jasmin's are pairwise distinct, so a CN base beside a
  Jasmin base contains no duplicates, `minimal_pair` applies verbatim, and the
  cross-tool deduplication this module was going to build has nothing to deduplicate.

  That is worth having found rather than assumed. The intuition was that shared trust
  (everyone rests on a solver, everyone rests on a C semantics) would be common. For the
  two tools actually encoded here it is absent: CN rests on *Cerberus's* C semantics and
  *CN's* type system; Jasmin rests on *its own* speculative semantics and *its own* type
  system; the one plausible common entry — an SMT backend — is charged by CN and not by
  Jasmin, whose SCT checker is a type system rather than a solver call.

  ── So what survives ──
  Not a deduplication mechanism, but a **tripwire**. `crossBase_no_collisions` is a
  decidable fact that holds today and would stop holding the moment a third tool's
  obligation was mapped onto an existing one — at which point `minimal_pair` would
  silently become inapplicable to a pair it is currently being used for. The value is in
  the check firing, not in the machinery it would gate.

  ── Honest note on what is not modelled ──
  `KaniTrust` and `VerusTrust` do not exist in this repo, so the cross-check tools are
  **not** in this vocabulary. Stage G and stage K each record a correspondence assumption
  in prose — the Rust port models `uexec`; the Verus spec transliterates the Lean rather
  than the Rust — and those are *different* assumptions about *different* artifacts, so
  they would not have collided either. Encoding them would mean inventing two trust
  records the repo has not measured, which is the rigging `PLAN-2026-08` §1.1 exists to
  refuse. Recorded as absent rather than guessed.
-/
import ConfTyping.IndexedBases
import ConfTyping.MinimalCompose

namespace ConfTyping

/-! ## One vocabulary

Each constructor names the tool it came from. That is deliberate: a shared obligation
would have to be introduced as a *new* constructor that two embeddings both target, which
makes the sharing a visible edit rather than an accident of naming. -/

/-- Obligations across the foreign tools this repo has encoded. -/
inductive XObligation where
  | cnCerberus
  | cnVcgen
  | cnSmt
  | cnTrustedSpec     : String → XObligation
  | jasminTypeSystem
  | jasminSpecSem
  | jasminPreservation
  deriving Repr, DecidableEq

def CNAssume.embed : CNAssume → XObligation
  | .cerberus      => .cnCerberus
  | .vcgen         => .cnVcgen
  | .smt           => .cnSmt
  | .trustedSpec s => .cnTrustedSpec s

def JAssume.embed : JAssume → XObligation
  | .typeSystem   => .jasminTypeSystem
  | .specSem      => .jasminSpecSem
  | .preservation => .jasminPreservation

/-! ## The measurement -/

/-- **The two vocabularies do not meet.** No CN obligation is any Jasmin obligation, so
    appending the two bases introduces no duplicate and there is nothing to deduplicate
    across the seam. -/
theorem cn_jasmin_obligations_disjoint (a : CNAssume) (b : JAssume) :
    a.embed ≠ b.embed := by
  cases a <;> cases b <;> simp [CNAssume.embed, JAssume.embed]

/-- The embeddings are injective, so the count of obligations is not an artefact of the
    encoding collapsing entries. -/
theorem cnEmbed_injective (a a' : CNAssume) (h : a.embed = a'.embed) : a = a' := by
  cases a <;> cases a' <;> simp_all [CNAssume.embed]

theorem jEmbed_injective (b b' : JAssume) (h : b.embed = b'.embed) : b = b' := by
  cases b <;> cases b' <;> simp_all [JAssume.embed]

/-- The cross-tool index for a frame-only CN result beside a source-level Jasmin claim. -/
def crossIdx (pf : CNProof) (asm : Bool) : List XObligation :=
  (cnNeedsIdx pf).map CNAssume.embed ++ (jNeedsIdx asm).map JAssume.embed

/-- **No collisions, so deduplication buys nothing.** Four obligations in, four out —
    the composite base is already duplicate-free, which is precisely the condition under
    which `minimal_pair` is the right theorem and `jcompD`'s repair is unnecessary. -/
theorem crossBase_no_collisions :
    (crossIdx frameOnlyProof false).length = 4
  ∧ (crossIdx frameOnlyProof false).eraseDups.length = 4 := by decide

/-- And with the solver charged on the CN side it is still collision-free — the one
    entry that looked most likely to be shared is charged by one tool and not the other. -/
theorem crossBase_no_collisions_with_smt :
    (crossIdx { usesArith := true, trustedSpecs := [] } true).length = 6
  ∧ (crossIdx { usesArith := true, trustedSpecs := [] } true).eraseDups.length = 6 := by
  decide

/-! ## What that settles

The proposed mechanism is unnecessary for every pair currently encoded, so it is not
built. What is kept is the check that would notice if that stopped being true. -/

/-- **The tripwire.** Deduplicating the cross-tool index is the identity, for the two
    tools encoded. If a third tool were added whose obligation was mapped onto an
    existing constructor — or if `CNAssume.embed` and `JAssume.embed` were ever made to
    agree on an entry — this stops holding, and `minimal_pair`'s independence hypothesis
    would have quietly stopped applying to a composite that relies on it. -/
theorem crossIdx_dedup_is_identity (pf : CNProof) (asm : Bool)
    (hpf : pf.trustedSpecs = []) :
    (crossIdx pf asm).eraseDups = crossIdx pf asm := by
  cases pf with
  | mk usesArith trustedSpecs =>
      subst hpf
      cases usesArith <;> cases asm <;> decide

/-- Stated as the pair it belongs to: the bases are disjoint, therefore `minimal_pair`
    is the applicable composition theorem and `jcompD`'s deduplication is not needed.
    Both halves in one place so the conclusion cannot be quoted without its premise. -/
theorem cross_tool_composition_is_the_independent_case :
    (∀ (a : CNAssume) (b : JAssume), a.embed ≠ b.embed)
  ∧ (crossIdx frameOnlyProof false).eraseDups = crossIdx frameOnlyProof false :=
  ⟨cn_jasmin_obligations_disjoint, by decide⟩

/-! ## The record

    **Proposed:** a shared obligation vocabulary so that two tools resting on one
    assumption are charged for it once.

    **Measured:** the two foreign bases this repo encodes share nothing. Four obligations
    compose to four; six to six; the SMT backend — the entry most likely to be common —
    is charged by CN and not by Jasmin, because Jasmin's SCT checker is a type system.

    **Kept:** the tripwire, and the embeddings that make sharing expressible as a visible
    edit rather than a coincidence. **Not built:** the deduplication mechanism, which
    would have had nothing to act on.

    **What would change the verdict.** A tool that shares an obligation with one already
    encoded — a second C verifier resting on Cerberus, or an SMT-backed SCT checker. At
    that point the embedding gains a constructor two tools both target, `crossIdx_dedup_is_identity`
    fails, and the mechanism becomes worth building. Until then this is a stage that
    tripped its own kill criterion, and the honest cost of finding that out was one
    datatype and two `decide`s. -/

end ConfTyping
