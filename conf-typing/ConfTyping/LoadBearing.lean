/-
  Is the carried trusted base *minimal*? — the predicate, and its first test.

  `needs` computes a base from the program's syntax and `needsLedger` maps it into
  stage 1e's `Ledger`. Two vacuity lemmas (`no_access_no_reads`,
  `unwritten_sink_untouched`) prove the entries a program does *not* incur are ones it
  genuinely does not need. What no theorem in the repo says is the other direction:
  that the entries a program *does* carry are all of them load-bearing.

  The gap is structural rather than an oversight. `condBoundary_weaken` and
  `condBoundary_of_unconditional` prove that any assumption may be added to any ledger
  and any unconditional certificate holds relative to any base — so the shape
  `Sat Γ → X` can only ever **over-approximate** the trusted base. There is a
  `condBoundary_weaken`; there is no `condBoundary_no_junk`. "Omissions are earned" is
  established by *exhibiting* smaller bases (`cn_base_strictly_smaller`,
  `pureProg_deployed_with_nothing`), not by any property a certificate carries.

  `LoadBearing` is that missing property, in the shape the repo already writes by hand:
  `sink_assumption_is_load_bearing` exhibits a deployment where one entry fails and the
  conclusion fails with it. Generalised, an entry is load-bearing when there is a world
  satisfying **every other** entry at which the goal still fails — so no entry is
  inert, and the base is minimal for that goal.

  ── What the test found ──
  * `fiveProg`'s **computed** two-entry base passes (`fiveProg_base_is_load_bearing`).
  * Stage 1s's **fixed** three-entry base **fails** (`toLedger_not_load_bearing`) — the
    filesystem entry is inert for this program, and dropping it changes nothing.
    So `LoadBearing` separates the computed base from the fixed one *mechanically*,
    where before the separation was two examples and a paragraph.
  * The predicate has teeth in the other direction too: padding the computed base with
    a trivially-true entry breaks it (`padded_base_not_load_bearing`), and the proof is
    `fiveProg_deployed_with_two` — the theorem that the base *suffices* is exactly the
    theorem that junk cannot hide in it.

  ── One thing this exposed, recorded rather than fixed ──
  `policy_assumption_is_load_bearing` (Deploy.lean) does not prove what its docstring
  claims. It proves `¬ (∀ r, true = false)` — that the assumption is falsifiable —
  and mentions neither `fiveProg` nor any conclusion. `sink_assumption_is_load_bearing`
  beside it does the full job. `policy_entry_load_bearing` below is the missing half.

  ── Scope ──
  Load-bearing is relative to a **goal**. An entry inert for one conclusion may be
  load-bearing for another, so `LoadBearing mkΓ goal n` is a statement about the pair.
  That is a feature: it is what lets the same base be minimal for `fiveGoal` and
  redundant for a weaker one.
-/
import ConfTyping.Assumptions

namespace ConfTyping

/-! ## The predicate -/

/-- **Entry `i` is load-bearing**: some world satisfies every *other* entry of the
    base and still fails the goal. Dropping it is therefore unsound, in the shape
    `ledger_no_silent_discharge` and `sink_assumption_is_load_bearing` use by hand. -/
def LoadBearingAt (mkΓ : Deployment → Ledger) (goal : Deployment → Prop) (i : Nat) : Prop :=
  ∃ D : Deployment, Sat ((mkΓ D).eraseIdx i) ∧ ¬ goal D

/-- **No junk**: every one of the base's `n` entries is load-bearing for the goal.
    The converse of `condBoundary_weaken`, which the ledger's shape cannot supply. -/
def LoadBearing (mkΓ : Deployment → Ledger) (goal : Deployment → Prop) (n : Nat) : Prop :=
  ∀ i, i < n → LoadBearingAt mkΓ goal i

/-! ## The goal

The two non-vacuous deployment-level conclusions of `fiveProg_deployed_with_two`. The
third — the filesystem — is omitted deliberately: `fiveProg` never emits to `fs`, so it
holds vacuously and could not distinguish anything. -/

/-- Mediation in the specification's terms, and every emitted string accepted. -/
def fiveGoal (D : Deployment) : Prop :=
  (∀ (n : Nat) (σ : Store) (r : UState × Nat × List Bool),
      uexec n fiveProg D.policy (initU σ) = some r → ∀ q ∈ r.1.reads, D.intended q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
      uexec n fiveProg π (initU σ) = some r → ∀ t ∈ r.1.sink, D.accepts t.2)

/-- The computed base, as a ledger-maker. -/
def fiveBase (D : Deployment) : Ledger := needsLedger D [2] "fs" fiveProg

/-! ## Entry 0 — the policy author

A deployment that grants everything while the specification intends nothing. Every
machine certificate still holds; the parser entry is satisfied trivially; and the
mediation conclusion fails, because `fiveProg` really does read `db`. -/

/-- Permissive where it is deployed, restrictive where it is specified. -/
def permissivePolicy : Deployment :=
  { policy := fun _ => true, intended := fun _ => false,
    accepts := fun _ => True, inside := fun _ => True }

/-- **The policy entry cannot be dropped.** This is the theorem
    `policy_assumption_is_load_bearing`'s docstring describes and its statement does
    not: the parser entry holds, and the mediation conclusion fails anyway. -/
theorem policy_entry_load_bearing : LoadBearingAt fiveBase fiveGoal 0 := by
  refine ⟨permissivePolicy, ?_, ?_⟩
  · show Sat ((needsLedger permissivePolicy [2] "fs" fiveProg).eraseIdx 0)
    rw [fiveProg_ledger]
    exact ⟨fun _ _ => trivial, trivial⟩
  · rintro ⟨hmed, -⟩
    have := hmed 15 (fun _ => 0) _ rfl "db" (by decide)
    exact absurd this (by decide)

/-! ## Entry 1 — the query parser

`hostileSink` (Deploy.lean) already has the shape: policy and intention agree, so the
first entry holds, and the parser accepts nothing. -/

/-- **The parser entry cannot be dropped.** `sink_assumption_is_load_bearing`'s
    witness, lifted into the predicate. -/
theorem sink_entry_load_bearing : LoadBearingAt fiveBase fiveGoal 1 := by
  refine ⟨hostileSink, ?_, ?_⟩
  · show Sat ((needsLedger hostileSink [2] "fs" fiveProg).eraseIdx 1)
    rw [fiveProg_ledger]
    exact ⟨fun _ => rfl, trivial⟩
  · rintro ⟨-, hacc⟩
    have := hacc 15 (fun _ => true) (fun _ => 0) _ rfl
              ("db", [UCh.ord, UCh.quote, UCh.quote]) (by decide)
    exact this

/-! ## The result -/

/-- **The computed base is minimal for this goal.** Both entries are load-bearing, so
    `fiveProg` carries no assumption it does not use — the direction `needs`'s vacuity
    lemmas do not cover. -/
theorem fiveProg_base_is_load_bearing : LoadBearing fiveBase fiveGoal 2 := by
  intro i hi
  match i with
  | 0     => exact policy_entry_load_bearing
  | 1     => exact sink_entry_load_bearing
  | _ + 2 => exact absurd hi (by omega)

/-! ## Non-vacuity: the goal is neither always true nor always false

If `fiveGoal` were false everywhere, every entry would be "load-bearing" for nothing
and the two theorems above would be worth nothing. If it were true everywhere, no
entry could ever be load-bearing. Both are checked. -/

/-- A deployment that keeps all its promises. -/
def honestDeployment : Deployment :=
  { policy := fun _ => true, intended := fun _ => true,
    accepts := fun _ => True, inside := fun _ => True }

/-- **Satisfiable** — so the load-bearing witnesses are refuting something real. -/
theorem fiveGoal_satisfiable : fiveGoal honestDeployment := by
  refine ⟨(fiveProg_deployed_with_two honestDeployment ?_).1,
          (fiveProg_deployed_with_two honestDeployment ?_).2.1⟩ <;>
    · rw [fiveProg_ledger]
      exact ⟨fun _ => rfl, fun _ _ => trivial, trivial⟩

/-- **And refutable** — `policy_entry_load_bearing`'s witness, restated as the other
    half of the bracket. -/
theorem fiveGoal_refutable : ¬ fiveGoal permissivePolicy := by
  rintro ⟨hmed, -⟩
  have := hmed 15 (fun _ => 0) _ rfl "db" (by decide)
  exact absurd this (by decide)

/-! ## The predicate has teeth in both directions

A property every base satisfies would be worthless. These two are the checks. -/

/-- The computed base with one trivially-true entry stapled to the front. -/
def paddedBase (D : Deployment) : Ledger := True :: fiveBase D

/-- **Padding is caught.** Erasing the junk entry leaves the real base, which
    *suffices* — so no world satisfies the remainder and fails the goal, and entry 0
    is not load-bearing. The proof is `fiveProg_deployed_with_two`: the theorem that
    the base is enough is the theorem that junk cannot hide in it. -/
theorem padded_base_not_load_bearing : ¬ LoadBearing paddedBase fiveGoal 3 := by
  intro h
  obtain ⟨D, hsat, hgoal⟩ := h 0 (by decide)
  exact hgoal ⟨(fiveProg_deployed_with_two D hsat).1,
               (fiveProg_deployed_with_two D hsat).2.1⟩

/-- **And the fixed base is caught, which is the point of the exercise.** Stage 1s
    charged every program three entries; for `fiveProg` the filesystem entry is inert,
    so erasing it leaves a base that still delivers the goal. `toLedger` therefore
    fails `LoadBearing` exactly where `needsLedger` passes it — the reduction from
    three entries to two, as a property rather than as a pair of examples. -/
theorem toLedger_not_load_bearing :
    ¬ LoadBearing (fun D => toLedger D [2]) fiveGoal 3 := by
  intro h
  obtain ⟨D, hsat, hgoal⟩ := h 2 (by decide)
  refine hgoal ⟨(fiveProg_deployed_with_two D ?_).1, (fiveProg_deployed_with_two D ?_).2.1⟩ <;>
    · rw [fiveProg_ledger]
      exact ⟨hsat.1, hsat.2.1, trivial⟩

/-! ## A hole in the predicate, found by trying the degenerate case

`LoadBearing mkΓ goal 0` is vacuously true for **every** `mkΓ`, including one that
returns a three-entry base — because the bound `n` is supplied separately from the
ledger and nothing ties them together. So `LoadBearing` alone cannot be read as
"minimal"; it is only meaningful when `n` really is the base's length.

`LedgerSize` states that, and `Minimal` is the pair. This is not a cosmetic fix: the
`pureProg` case below is exactly where the unsound reading would have been taken. -/

/-- The base has the same length in every world — so the index range is well defined. -/
def LedgerSize (mkΓ : Deployment → Ledger) (n : Nat) : Prop :=
  ∀ D, (mkΓ D).length = n

/-- **Minimal**: `n` really is the base's length, and all `n` entries bear weight. -/
def Minimal (mkΓ : Deployment → Ledger) (goal : Deployment → Prop) (n : Nat) : Prop :=
  LedgerSize mkΓ n ∧ LoadBearing mkΓ goal n

theorem fiveBase_size : LedgerSize fiveBase 2 := by
  intro D; show (needsLedger D [2] "fs" fiveProg).length = 2
  rw [fiveProg_ledger]; rfl

/-- **The computed base for `fiveProg` is minimal** — two entries, and both bear. -/
theorem fiveProg_base_is_minimal : Minimal fiveBase fiveGoal 2 :=
  ⟨fiveBase_size, fiveProg_base_is_load_bearing⟩

theorem toLedger_size (Ks : List Nat) : LedgerSize (fun D => toLedger D Ks) 3 :=
  fun _ => rfl

/-- **And the fixed base is not**, with the size claim now discharged rather than
    assumed — so the failure is a failure of minimality, not of bookkeeping. -/
theorem toLedger_not_minimal : ¬ Minimal (fun D => toLedger D [2]) fiveGoal 3 :=
  fun h => toLedger_not_load_bearing h.2

/-! ## The degenerate case: `pureProg`

`pureProg_ledger` proves its computed base is empty, so `Minimal … 0` should hold — and
the interesting half is what it takes for *any other* base to be minimal for it. The
answer is: nothing can be, and that is a theorem rather than an observation. -/

/-- The same two conclusions, for the pure program. -/
def pureGoal (D : Deployment) : Prop :=
  (∀ (n : Nat) (σ : Store) (r : UState × Nat × List Bool),
      uexec n pureProg D.policy (initU σ) = some r → ∀ q ∈ r.1.reads, D.intended q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
      uexec n pureProg π (initU σ) = some r → ∀ t ∈ r.1.sink, D.accepts t.2)

def pureBase (D : Deployment) : Ledger := needsLedger D [2] "fs" pureProg

/-- **The goal holds in every world**, with nothing assumed — `pureProg` reads nothing
    and emits nothing, so no deployment can break it. -/
theorem pureGoal_unconditional : ∀ D, pureGoal D := fun D =>
  ⟨(pureProg_deployed_with_nothing D [2] "fs").2.1,
   (pureProg_deployed_with_nothing D [2] "fs").2.2.1⟩

theorem pureBase_size : LedgerSize pureBase 0 := by
  intro D; show (needsLedger D [2] "fs" pureProg).length = 0
  rw [pureProg_ledger]; rfl

/-- **The empty base is minimal for `pureProg`** — vacuously in the second component,
    which is the honest content: there are no entries, so there is no junk. The
    predicate is *correct* here rather than *informative*, and `LedgerSize` is what
    stops that from being mistaken for a result about a longer base. -/
theorem pureProg_base_is_minimal : Minimal pureBase pureGoal 0 :=
  ⟨pureBase_size, fun i hi => absurd hi (by omega)⟩

/-- **The general no-go.** If a goal holds unconditionally, no entry of any base
    whatsoever bears weight for it — there is no world left in which to fail. -/
theorem no_entry_bears_of_unconditional {goal : Deployment → Prop}
    (h : ∀ D, goal D) (mkΓ : Deployment → Ledger) (i : Nat) :
    ¬ LoadBearingAt mkΓ goal i := by
  rintro ⟨D, -, hgoal⟩
  exact hgoal (h D)

/-- **So the empty base is the *only* minimal base for `pureProg`.** Every entry of
    every candidate base is inert — this is the strongest form the reduction takes, and
    it needs no `Sat` hypothesis at all. -/
theorem pureProg_admits_no_other_minimal (mkΓ : Deployment → Ledger) (n : Nat)
    (hn : 0 < n) : ¬ Minimal mkΓ pureGoal n :=
  fun h => no_entry_bears_of_unconditional pureGoal_unconditional mkΓ 0 (h.2 0 hn)

/-- Instantiated at the fixed base: **three entries, all three junk.** Stage 1s charged
    `pureProg` a policy author, a query parser and a filesystem; it needs none of them,
    and `needs` is why the computed base says so. -/
theorem toLedger_all_junk_for_pureProg :
    ¬ Minimal (fun D => toLedger D [2]) pureGoal 3 ∧
    ∀ i, ¬ LoadBearingAt (fun D => toLedger D [2]) pureGoal i :=
  ⟨pureProg_admits_no_other_minimal _ 3 (by omega),
   no_entry_bears_of_unconditional pureGoal_unconditional _⟩

/-! ## What this establishes, and what it does not

    **Establishes.** The computed base for `fiveProg` is minimal for `fiveGoal`, and
    the predicate that says so distinguishes it from the fixed base and from a padded
    one. "The trusted base is computed rather than fixed" now has a property attached
    to it instead of two worked examples.

    **Does not establish.** `LoadBearing` is checked here for one program and one goal,
    by hand-built witnesses. There is no theorem that `needs` produces a load-bearing
    base *in general* — and there cannot be an unconditional one, since `needs` is
    syntactic and deliberately conservative (`needs_is_syntactic`: an `access` in dead
    code is still charged, and that base is *not* minimal). The honest general
    statement would be conditional on reachability, which is a different analysis. -/

end ConfTyping
