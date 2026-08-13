/-
  Stage C, second pass — the other tool already had a name for the gap.

  The first pass (`HeteroCompose.lean`) found that a CN certificate does not
  transfer to a speculative machine, and that the obligation hides in
  `Bridge.pair`'s `hmap`. Its second certificate was *invented*: `sctGA`, a
  public set accumulating by intersection, SCT-shaped but transcribed from
  nothing.

  This module replaces it with the real structure, read out of Jasmin's own
  test corpus (`corpus/jasmin/SOURCES.md`), and the reading changed the result.

  ── A Jasmin SCT level is a PAIR ──
  Not one level but two — one for normal execution and one for misspeculating
  execution:

      public    = ⟨L, L⟩     transient = ⟨L, H⟩     secret = ⟨H, H⟩

  and the middle one is the whole of stage C. **`transient` is exactly what a CN
  certificate becomes when it is carried into a speculative world**: public
  normally, unconstrained under misspeculation. The first pass discovered that gap
  and had to describe it longhand. Jasmin had already named it — and, tellingly,
  named it as something distinct from `public`, which is precisely the distinction
  `arch_reconciliation_insufficient` had to construct a counterexample to make.

  `bcb_footprint_is_transient` is that sentence as a theorem: the bounds-check
  bypass gadget's footprint certificate sits at `transient`, not at `public`.
  `protected_footprint_is_public` is Jasmin's fix — `#protect` masks the
  misspeculated value, and the certificate moves up to `public`.

  ── Why this is a better second certificate than the invented one ──
  `sctLvlGA` accumulates by **componentwise join**, which is the IFC law and is
  Jasmin's, not one chosen to look different from CN's union. That the two monoids
  differ (union beside join) is now a fact about two real tools rather than a
  property of a witness built to have it.

  ── Scope ──
  * Nothing here proves that Jasmin's `#[sct = ...]` annotation *implies* these
    predicates; that is Jasmin's soundness theorem over its own semantics. The
    encoding is by hand, **unchecked against the Jasmin checker**, and no `.jazz`
    file is parsed.
  * `#protect`/MSF is modelled **by its effect only** — the transient access
    contributes nothing outside the footprint.
  * Value-dependence, arrays, the `ptr`/`val` split and `#update_msf` placement are
    not modelled. None of them bears on the composition law, which is what stage C
    is about.
-/
import ConfTyping.HeteroCompose

namespace ConfTyping

open TransportCalculus

/-! ## Jasmin's level pair -/

/-- A confidentiality level. Jasmin's `L`/`H`. -/
inductive Lvl where
  | pub
  | sec
deriving DecidableEq, Repr

/-- Join: `pub` is the identity, `sec` absorbs. -/
def Lvl.join : Lvl → Lvl → Lvl
  | .pub, l => l
  | .sec, _ => .sec

theorem Lvl.join_assoc (a b c : Lvl) : (a.join b).join c = a.join (b.join c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **A Jasmin SCT level: two levels, not one.** One for normal execution, one for
    execution that is misspeculating. This pair is the structure the whole stage
    turns on. -/
structure SLvl where
  normal : Lvl
  spec   : Lvl
deriving DecidableEq, Repr

/-- `public` — ⟨L, L⟩. -/
def SLvl.public : SLvl := ⟨.pub, .pub⟩

/-- `transient` — ⟨L, H⟩. Public normally, secret under misspeculation. **The
    level of a certificate that was proved architecturally and carried into a
    speculative world.** -/
def SLvl.transient : SLvl := ⟨.pub, .sec⟩

/-- `secret` — ⟨H, H⟩. -/
def SLvl.secret : SLvl := ⟨.sec, .sec⟩

/-- The three are distinct — in particular `transient ≠ public`, which is the
    distinction stage C's first pass had to build a counterexample to expose. -/
theorem slvl_transient_ne_public : SLvl.transient ≠ SLvl.public := by decide

theorem slvl_transient_ne_secret : SLvl.transient ≠ SLvl.secret := by decide

/-! ## The graded action: levels accumulate by componentwise join

This is the IFC law, and it is Jasmin's. Set beside `cnGA`'s union it makes the
bundle heterogeneous as a fact about two tools rather than by construction. -/

/-- Componentwise join on level pairs. -/
def SLvl.join (a b : SLvl) : SLvl := ⟨a.normal.join b.normal, a.spec.join b.spec⟩

/-- Level ordering: `a ≤ b` when joining `a` into `b` changes nothing. -/
def SLvl.le (a b : SLvl) : Prop := a.join b = b

/-- **The SCT graded action.** Grades are level pairs, composed by join. `act_mul`
    is associativity of join, where `cnGA`'s was associativity of `∨`. -/
def sctLvlGA : GradedAction SLvl SLvl where
  mul      := SLvl.join
  le       := SLvl.le
  act      := SLvl.join
  le_trans := by
    intro a b c hab hbc
    show SLvl.join a c = c
    calc SLvl.join a c = SLvl.join a (SLvl.join b c) := by rw [hbc]
      _ = SLvl.join (SLvl.join a b) c := by
            simp only [SLvl.join, SLvl.mk.injEq]
            exact ⟨(Lvl.join_assoc _ _ _).symm, (Lvl.join_assoc _ _ _).symm⟩
      _ = SLvl.join b c := by rw [hab]
      _ = c := hbc
  act_mul  := by
    intro a b d
    show SLvl.join (SLvl.join a b) d = SLvl.join a (SLvl.join b d)
    simp only [SLvl.join, SLvl.mk.injEq]
    exact ⟨Lvl.join_assoc _ _ _, Lvl.join_assoc _ _ _⟩
  act_mono := by
    intro m d d' h
    show SLvl.join (SLvl.join m d) (SLvl.join m d') = SLvl.join m d'
    have hd : SLvl.join d d' = d' := h
    cases m with
    | mk mn ms =>
      cases d with
      | mk dn ds =>
        cases d' with
        | mk dn' ds' =>
          simp only [SLvl.join, SLvl.mk.injEq] at hd ⊢
          obtain ⟨h1, h2⟩ := hd
          constructor
          · cases mn <;> cases dn <;> cases dn' <;> simp_all [Lvl.join]
          · cases ms <;> cases ds <;> cases ds' <;> simp_all [Lvl.join]

/-- CN unions, Jasmin joins. Two real tools, two different monoids, one
    `Bridge.comp`. -/
theorem cn_unions_jasmin_joins (A B : Footprint) (Γ : Ledger) (a b : SLvl) :
    (cnGA.mul (A, Γ) (B, Γ)).1 = (fun l => A l ∨ B l)
    ∧ sctLvlGA.mul a b = ⟨a.normal.join b.normal, a.spec.join b.spec⟩ := ⟨rfl, rfl⟩

/-! ## The finding, in Jasmin's vocabulary

The level a *footprint* certificate occupies on an artifact: public in the
normal component when the footprint holds architecturally, public in the
speculative component when it holds under every schedule. -/

/-- The SCT level of a footprint certificate on an artifact. -/
def footprintLevel (fs : SpecArtifact) (F : Footprint) (lv : SLvl) : Prop :=
  (lv.normal = Lvl.pub ↔ ArchTouchesOnly fs F)
  ∧ (lv.spec = Lvl.pub ↔ TouchesOnly fs F)

/-- **The lattice's own well-formedness, earned.** No artifact sits at ⟨H, L⟩ —
    secret normally but public speculatively — because containment under every
    schedule includes the architectural one. Jasmin's level pairs are ordered for
    a reason, and here is the reason at this altitude. -/
theorem touchesOnly_imp_arch {fs : SpecArtifact} {F : Footprint}
    (h : TouchesOnly fs F) : ArchTouchesOnly fs F :=
  fun σ l hl => h 0 σ l hl

/-- **The stage-C finding, in the other tool's words.** The bounds-check bypass
    gadget's footprint certificate is `transient` — ⟨public, secret⟩ — and not
    `public`. Everything `arch_reconciliation_insufficient` had to construct is
    this one level assignment.

    A CN result is a fact about the architectural machine. Carried into a
    speculative world it lands here, and Jasmin's type system has been saying so
    all along. -/
theorem bcb_footprint_is_transient :
    footprintLevel bcbGadget bcbFootprint SLvl.transient := by
  constructor
  · exact ⟨fun _ => bcb_arch_touches, fun _ => rfl⟩
  · constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h bcb_not_touches

/-! ## `#protect`, and the upgrade to `public`

Jasmin's fix, modelled by its effect: the misspeculated value is masked, so the
access it feeds contributes nothing outside the footprint. This is `fig3a`'s
`x = #protect(x, ms)`. -/

/-- The gadget with the protect in place: the transient window no longer
    contributes an out-of-footprint address. -/
def bcbProtected : SpecArtifact := fun _ σ =>
  if σ 0 < 4 then { store := σ, trace := [σ 0] }
  else { store := σ, trace := [] }

/-- Protecting makes speculation observationally inert — the first pass's
    sufficient condition, now with a witness that satisfies it. -/
theorem bcbProtected_trace_inert : TraceInert bcbProtected := fun _ _ => rfl

theorem bcbProtected_arch_touches : ArchTouchesOnly bcbProtected bcbFootprint := by
  intro σ l hl
  unfold bcbProtected at hl
  split at hl
  · rename_i hlt
    simp only [List.mem_singleton] at hl
    exact hl ▸ hlt
  · simp at hl

/-- **The upgrade.** With `#protect` in place the footprint certificate sits at
    `public` — ⟨L, L⟩ — so it may be bundled with a certificate about the
    speculative machine. This is `cn_reception_transfers`'s hypothesis discharged
    by the mechanism Jasmin actually ships. -/
theorem protected_footprint_is_public :
    footprintLevel bcbProtected bcbFootprint SLvl.public := by
  refine ⟨⟨fun _ => bcbProtected_arch_touches, fun _ => rfl⟩,
          ⟨fun _ => ?_, fun _ => rfl⟩⟩
  exact touchesOnly_of_inert bcbProtected_trace_inert bcbProtected_arch_touches

/-- **The two artifacts differ in exactly the speculative component.** Same
    architectural behaviour, same footprint, and the certificates land at
    different SCT levels — which is what it means for the gap to be real and for
    `#protect` to be doing work. -/
theorem protect_changes_only_the_speculative_component :
    SLvl.transient.normal = SLvl.public.normal
    ∧ SLvl.transient.spec ≠ SLvl.public.spec := by decide

/-! ## What the second pass changed

The first pass's conclusion stands and is now stated in the second tool's own
vocabulary rather than longhand:

* A CN certificate carried into a speculative world is **`transient`**, and
  Jasmin's type system distinguishes `transient` from `public` for exactly the
  reason `arch_reconciliation_insufficient` exhibits.
* The sufficient condition of `cn_reception_transfers` is what Jasmin's
  `#protect` implements, and `bcbProtected` is a witness that satisfies it.
* The heterogeneity of the bundle is now a fact about two real tools: CN's
  footprints accumulate by **union**, Jasmin's levels by **join**, and one
  `Bridge.comp` advances both.

What is still not done: no `.jazz` file is parsed, no Jasmin output is consumed,
and the reception remains a hand encoding — the same gap named in `CNReceive.lean`,
and the thing Stage D would have to close for either tool. -/

end ConfTyping
