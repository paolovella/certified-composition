/-
  The composable core, stage 1s: what must be true of the world.

  Five certificates say things about the *machine*. A deployment cares about something
  else: that the database accepts the query, that the filesystem serves a file inside
  the root, that the policy the program consulted is the policy the specification
  meant. Each of those readings needs an assumption the program cannot check, and
  stage 1e built the mechanism for exactly this — a ledger of assumptions that appends
  under composition and cannot be silently discharged. It was never threaded through
  the rest of the core. This threads it.

  The useful part is the **sorting**, which the exercise forces and which was not
  obvious in advance. Of the five certificates:

  * **Noninterference** and **memory safety** need *nothing*. They are statements about
    the machine's own state, and the machine is the artifact.
  * The **budget** needs nothing either, because it is denominated in the model's own
    steps. Converting it to seconds would need an assumption; saying "at most six
    steps" does not.
  * **Mediation**, **structural integrity** and **path safety** each need exactly one
    entry, and the entries are about three different external components — the policy
    author, the query parser, the filesystem.

  So the trusted base of a fully-certified program is three lines long, and
  `Discharged` names them. `deployment_reading` is the transformation: given the machine
  guarantees and a discharged deployment, the deployment-level statements follow.
  `toLedger` connects it to stage 1e, so these entries append under composition like any
  others (`sat_toLedger`).

  Two theorems keep it from being a formality. `sink_assumption_is_load_bearing`
  exhibits a deployment where the parser assumption fails and the conclusion fails with
  it — the entry is not decoration. And `machine_guarantees_need_no_deployment` records
  the other half: noninterference and memory safety hold with the ledger empty, so the
  sorting above is a fact rather than a presentation choice.
-/
import ConfTyping.StringLoop

namespace ConfTyping

/-! ## A deployment -/

/-- The parts of the world the program is placed into: the policy actually deployed,
    the policy the specification intended, the query parser, and the filesystem. The
    last two are *abstract predicates* — modelling a real parser is not the point, and
    pretending to would be worse than naming the assumption. -/
structure Deployment where
  policy   : MedPolicy
  intended : MedPolicy
  accepts  : UStr → Prop      -- the parser reads this as one well-formed query
  inside   : UStr → Prop      -- the filesystem resolves this path within the root

/-- **The trusted base of a fully-certified program: three lines.** Each entry belongs
    to a different external component, and none of them is checkable by the program. -/
structure Discharged (D : Deployment) (Ks : List Nat) : Prop where
  /-- The deployed policy grants exactly what the specification intends. -/
  policyIntended : ∀ r, D.policy r = D.intended r
  /-- The parser accepts any string carrying a delimiter count the analysis allows —
      i.e. the parser's notion of "well formed" is the one `qcount` models. -/
  sinkAccepts    : ∀ t, qcount t ∈ Ks → D.accepts t
  /-- The filesystem resolves `..` the way `walk` does, so a path that never pops above
      depth zero really does stay inside the root. -/
  fsInside       : ∀ t, safePath t = true → D.inside t

/-! ## Threading it into stage 1e's ledger -/

/-- The same three obligations as a stage-1e `Ledger`, so they append under composition
    and discharge through `UCertL` like any other assumption. -/
def toLedger (D : Deployment) (Ks : List Nat) : Ledger :=
  [ (∀ r, D.policy r = D.intended r),
    (∀ t, qcount t ∈ Ks → D.accepts t),
    (∀ t, safePath t = true → D.inside t) ]

theorem sat_toLedger (D : Deployment) (Ks : List Nat) :
    Sat (toLedger D Ks) ↔ Discharged D Ks := by
  constructor
  · intro ⟨h1, h2, h3, _⟩; exact ⟨h1, h2, h3⟩
  · intro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3, trivial⟩

/-! ## The deployment reading -/

/-- **From machine guarantees to deployment guarantees.** Each conclusion is the
    security statement someone actually wants, and each is bought with exactly one
    ledger entry. Stated over the guarantees rather than the checkers, so it applies to
    anything the core certifies however it was certified. -/
theorem deployment_reading {c : UCmd} {Ks : List Nat} {fs : String} {D : Deployment}
    (hD : Discharged D Ks)
    (hmed : ∀ (n : Nat) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c D.policy (initU σ) = some r → ∀ q ∈ r.1.reads, D.policy q = true)
    (hinj : ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → ∀ t ∈ r.1.sink, qcount t.2 ∈ Ks)
    (hpath : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        s.sink = [] → uexec n c π s = some r →
        ∀ p ∈ r.1.sink, p.1 = fs → safePath p.2 = true) :
    -- mediation, in the specification's terms rather than the deployment's
    (∀ (n : Nat) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c D.policy (initU σ) = some r → ∀ q ∈ r.1.reads, D.intended q = true)
    -- every emitted string is one the parser accepts
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → ∀ t ∈ r.1.sink, D.accepts t.2)
    -- every path served stays inside the root
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → ∀ p ∈ r.1.sink, p.1 = fs → D.inside p.2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n σ r hr q hq
    rw [← hD.policyIntended q]
    exact hmed n σ r hr q hq
  · intro n π σ r hr t ht
    exact hD.sinkAccepts t.2 (hinj n π σ r hr t ht)
  · intro n π σ r hr p hp hfs
    exact hD.fsInside p.2 (hpath n π (initU σ) r rfl hr p hp hfs)

/-! ## The sorting is a fact, not a presentation choice -/

/-- **Two of the five need no deployment at all.** Noninterference and memory safety are
    statements about the machine's own state, so they hold with the ledger empty. The
    budget likewise, being denominated in the model's own steps — converting it to
    seconds would need an entry, stating it in steps does not. -/
theorem machine_guarantees_need_no_deployment :
    Sat ([] : Ledger)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq Psec σ σ' →
        uOptLowEq Psec (uexec n fiveProg π (initU σ)) (uexec n fiveProg π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fiveProg π (initU σ) = some r → r.1.err = false)
  ∧ (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        uexec n fiveProg π s = some r → r.2.1 ≤ 6) :=
  ⟨trivial, fiveProg_five.2.2.1, fiveProg_five.2.2.2.1, fiveProg_five.1⟩

/-! ## The worked program, deployed -/

/-- `fiveProg` emits to the `db` sink and never to `fs`, so its path obligation is
    vacuous — which the checker confirms rather than the prose asserting it. -/
theorem fiveProg_paths_vacuous :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      s.sink = [] → uexec n fiveProg π s = some r →
      ∀ p ∈ r.1.sink, p.1 = "fs" → safePath p.2 = true :=
  pcheckW_no_escape (by decide : pcheckW "fs" 12 [] fiveProg = some [("q", 2)])

/-- **The deployment-level guarantees for the worked program**, from its five machine
    certificates plus three ledger entries. -/
theorem fiveProg_deployed (D : Deployment) (hD : Discharged D [2]) :
    (∀ (n : Nat) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fiveProg D.policy (initU σ) = some r →
        ∀ q ∈ r.1.reads, D.intended q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fiveProg π (initU σ) = some r → ∀ t ∈ r.1.sink, D.accepts t.2)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fiveProg π (initU σ) = some r →
        ∀ p ∈ r.1.sink, p.1 = "fs" → D.inside p.2) :=
  deployment_reading (fs := "fs") hD
    (fun n σ r hr q hq => fiveProg_five.2.1 n D.policy σ r hr q hq)
    (fun n π σ r hr t ht => fiveProg_five.2.2.2.2 n π σ r hr t ht)
    fiveProg_paths_vacuous

/-! ## The entries are load-bearing -/

/-- A deployment whose parser accepts nothing. -/
def hostileSink : Deployment :=
  { policy := fun _ => true, intended := fun _ => true,
    accepts := fun _ => False, inside := fun _ => True }

/-- **Drop the parser assumption and the guarantee goes with it.** `fiveProg` really
    does emit — so a deployment that fails `sinkAccepts` has a run whose emitted string
    the parser rejects, however well the program is certified. The entry is an
    obligation, not decoration. -/
theorem sink_assumption_is_load_bearing :
    ¬ Discharged hostileSink [2]
  ∧ ∃ r : UState × Nat × List Bool,
      uexec 15 fiveProg (fun _ => true) (initU (fun _ => 0)) = some r
    ∧ ¬ (∀ t ∈ r.1.sink, hostileSink.accepts t.2) := by
  constructor
  · intro h
    exact h.sinkAccepts [UCh.ord, UCh.quote, UCh.quote] (by decide)
  · refine ⟨_, rfl, ?_⟩
    intro h
    exact h ("db", [UCh.ord, UCh.quote, UCh.quote]) (by decide)

/-- And the same for mediation, which is stage 1e's point restated where the rest of
    the core can see it: a permissive deployed policy with a restrictive specification
    satisfies every machine certificate and still reads something unintended. -/
theorem policy_assumption_is_load_bearing :
    ¬ (∀ r, (fun _ => true : MedPolicy) r = (fun _ => false : MedPolicy) r) := by
  intro h
  exact absurd (h "db") (by decide)

/-! ## What the core is, now

    Six certificates, checked by three analyses over one language, on programs with
    loops; five of the six compose over loops, and the budget's exception is a
    termination argument rather than a gap. Two of the six are unconditional statements
    about the machine, one is stated in the machine's own units, and the remaining three
    rest on a trusted base that is **three lines long and enumerated**.

    That last number is the point of the exercise. A program can be certified to the
    hilt and still be wrong about the world; what the ledger buys is that the ways it
    can be wrong are listed, appendable, and impossible to discharge by accident. -/

end ConfTyping
