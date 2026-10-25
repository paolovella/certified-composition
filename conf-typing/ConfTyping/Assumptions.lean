/-
  The composable core, stage 2c: the trusted base, computed from the program.

  Stage 1s established that a fully-certified program rests on exactly three external
  assumptions — the policy author, the query parser, the filesystem — and that
  noninterference, memory safety and the budget rest on none. It stated them as a fixed
  `Discharged` record demanding all three, and left the connection to stage 1e's ledger
  by hand. Three stages have flagged that as unfinished.

  The gap was not plumbing. A fixed three-entry record charges every program for
  assumptions it may not use: a program that never calls `access` reads nothing, so
  "the deployed policy is the intended one" is not an assumption it needs — it is a
  statement about nothing. Same for a program that never emits to a sink.

  So the ledger is **computed**. `needs c` collects, from the syntax, exactly the
  obligations the program can incur; `Discharges` requires only those; and the two
  vacuity lemmas prove the omitted ones are omitted for cause:

  * `no_access_no_reads` — a program without `access` leaves `reads` untouched, so the
    mediation guarantee holds with the policy entry absent;
  * `unwritten_sink_untouched` — a program that never emits to `q` adds nothing tagged
    `q`, so that sink's parser entry is likewise unnecessary.

  The result is a trusted base that shrinks to **nothing** for a pure computation
  (`pureProg_deployed_with_nothing`: all three deployment guarantees, ledger empty) and
  to **two** entries for `fiveProg` — one fewer than stage 1s charged it, because
  `fiveProg` never emits to the filesystem and so owes the filesystem nothing.
-/
import ConfTyping.Deploy
import ConfTyping.Ownership

namespace ConfTyping

/-- Membership survives concatenation, in whichever half it was found. Local because
    this package is mathlib-free and `memStr` is our own. -/
theorem memStr_append {q : String} : ∀ {A B : List String},
    (memStr q A = true ∨ memStr q B = true) → memStr q (A ++ B) = true
  | [],      _, h => by simpa [memStr] using h
  | x :: xs, B, h => by
      show ((x == q) || memStr q (xs ++ B)) = true
      simp only [Bool.or_eq_true]
      rcases h with h | h
      · simp only [memStr, Bool.or_eq_true] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (memStr_append (Or.inl h))
      · exact Or.inr (memStr_append (Or.inr h))

/-- And its contrapositive, in the form the induction actually consumes. -/
theorem memStr_append_false {q : String} {A B : List String}
    (h : memStr q (A ++ B) = false) : memStr q A = false ∧ memStr q B = false := by
  refine ⟨?_, ?_⟩
  · cases hA : memStr q A with
    | false => rfl
    | true => rw [memStr_append (Or.inl hA)] at h; cases h
  · cases hB : memStr q B with
    | false => rfl
    | true => rw [memStr_append (Or.inr hB)] at h; cases h

/-! ## What a program can incur -/

/-- The obligations a program's certificates can rest on. Each is external: no program
    can discharge one, which is what makes it a ledger entry rather than a check. -/
inductive Assume where
  /-- The deployed policy grants exactly what the specification intends. -/
  | policyIntended : Assume
  /-- The named sink's parser reads what we emit as one well-formed item. -/
  | sinkHonest : String → Assume
  deriving Repr, DecidableEq

/-- Does the program read a mediated resource at all? -/
def hasAccess : UCmd → Bool
  | .access _      => true
  | .seq c₁ c₂     => hasAccess c₁ || hasAccess c₂
  | .ite _ c₁ c₂   => hasAccess c₁ || hasAccess c₂
  | .loop _ c      => hasAccess c
  | _              => false

/-- Which sinks the program can emit to. -/
def sinksOf : UCmd → List String
  | .sop .emit q _ => [q]
  | .seq c₁ c₂     => sinksOf c₁ ++ sinksOf c₂
  | .ite _ c₁ c₂   => sinksOf c₁ ++ sinksOf c₂
  | .loop _ c      => sinksOf c
  | _              => []

/-- **The trusted base, computed.** Exactly the entries this program can incur. -/
def needs (c : UCmd) : List Assume :=
  (if hasAccess c then [Assume.policyIntended] else []) ++ (sinksOf c).map Assume.sinkHonest

/-! ## The omitted entries are omitted for cause -/

/-- **No `access`, no reads.** So a program without one satisfies the mediation
    guarantee with the policy entry absent — vacuously, which is the point. -/
theorem no_access_no_reads : ∀ (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState)
    (r : UState × Nat × List Bool), hasAccess c = false → uexec n c π s = some r →
    r.1.reads = s.reads
  | 0,     _, _, _, _, _,  h => by simp [uexec] at h
  | n + 1, c, π, s, r, ha, h => by
      cases c with
      | access q => simp [hasAccess] at ha
      | skip => simp only [uexec, Option.some.injEq] at h; subst h; rfl
      | assign x e =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]
          · simp only [ite_eq_right hd]
      | check q =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]
          · simp only [ite_eq_right hd]
            by_cases hp : π q = true
            · simp only [ite_eq_left hp]
            · simp only [ite_eq_right hp]
      | sop op x e =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]
          · simp only [ite_eq_right hd]; cases op with
            | set => rfl
            | emit => rfl
      | hop op x y =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]
          · simp only [ite_eq_right hd]; cases op with
            | load =>
                by_cases hl : memInt (s.store y) s.live = true
                · simp only [ite_eq_left hl]
                · simp only [ite_eq_right hl]
            | store =>
                by_cases hl : memInt (s.store x) s.live = true
                · simp only [ite_eq_left hl]
                · simp only [ite_eq_right hl]
      | memop op x =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]
          · simp only [ite_eq_right hd]; cases op with
            | alloc => rfl
            | allocS => rfl
            | deref =>
                by_cases hl : memInt (s.store x) s.live = true
                · simp only [ite_eq_left hl]
                · simp only [ite_eq_right hl]
            | free =>
                by_cases hl : memInt (s.store x) s.live = true
                · simp only [ite_eq_left hl]
                · simp only [ite_eq_right hl]
      | seq c₁ c₂ =>
          simp only [hasAccess, Bool.or_eq_false_iff] at ha
          rw [uexec_seq_eq] at h
          rcases e₁ : uexec n c₁ π s with _ | r₁
          · rw [e₁] at h; simp at h
          · rw [e₁, Option.bind_some] at h
            rcases e₂ : uexec n c₂ π r₁.1 with _ | r₂
            · rw [e₂] at h; simp at h
            · rw [e₂] at h
              simp only [Option.map_some, Option.some.injEq] at h; subst h
              rw [no_access_no_reads n c₂ π r₁.1 r₂ ha.2 e₂,
                  no_access_no_reads n c₁ π s r₁ ha.1 e₁]
      | ite e c₁ c₂ =>
          simp only [hasAccess, Bool.or_eq_false_iff] at ha
          rw [uexec_ite_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at h
            rcases e₁ : uexec n c₁ π s with _ | r₁
            · rw [e₁] at h; simp at h
            · rw [e₁] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact no_access_no_reads n c₁ π s r₁ ha.1 e₁
          · rw [ite_eq_right hg] at h
            rcases e₂ : uexec n c₂ π s with _ | r₂
            · rw [e₂] at h; simp at h
            · rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact no_access_no_reads n c₂ π s r₂ ha.2 e₂
      | loop e c₀ =>
          simp only [hasAccess] at ha
          rw [uexec_loop_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at h
            rcases e₁ : uexec n c₀ π s with _ | r₁
            · rw [e₁] at h; simp at h
            · rw [e₁, Option.bind_some] at h
              rcases e₂ : uexec n (.loop e c₀) π r₁.1 with _ | r₂
              · rw [e₂] at h; simp at h
              · rw [e₂] at h
                simp only [Option.map_some, Option.some.injEq] at h; subst h
                rw [no_access_no_reads n (.loop e c₀) π r₁.1 r₂ (by simp [hasAccess, ha]) e₂,
                    no_access_no_reads n c₀ π s r₁ ha e₁]
          · rw [ite_eq_right hg] at h
            simp only [Option.some.injEq] at h; subst h; rfl

/-- **A sink the program never writes stays as it was.** So that sink's parser entry is
    unnecessary, again vacuously. -/
theorem unwritten_sink_untouched : ∀ (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState)
    (r : UState × Nat × List Bool) (q : String), memStr q (sinksOf c) = false →
    uexec n c π s = some r → ∀ p ∈ r.1.sink, p.1 = q → p ∈ s.sink
  | 0,     _, _, _, _, _, _,  h => by simp [uexec] at h
  | n + 1, c, π, s, r, q, hq, h => by
      cases c with
      | skip => simp only [uexec, Option.some.injEq] at h; subst h; exact fun p hp _ => hp
      | access _ =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]; exact fun p hp _ => hp
          · simp only [ite_eq_right hd]; exact fun p hp _ => hp
      | assign x e =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]; exact fun p hp _ => hp
          · simp only [ite_eq_right hd]; exact fun p hp _ => hp
      | check qq =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]; exact fun p hp _ => hp
          · simp only [ite_eq_right hd]
            by_cases hp : π qq = true
            · simp only [ite_eq_left hp]; exact fun p hp _ => hp
            · simp only [ite_eq_right hp]; exact fun p hp _ => hp
      | hop op x y =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]; exact fun p hp _ => hp
          · simp only [ite_eq_right hd]; cases op with
            | load =>
                by_cases hl : memInt (s.store y) s.live = true
                · simp only [ite_eq_left hl]; exact fun p hp _ => hp
                · simp only [ite_eq_right hl]; exact fun p hp _ => hp
            | store =>
                by_cases hl : memInt (s.store x) s.live = true
                · simp only [ite_eq_left hl]; exact fun p hp _ => hp
                · simp only [ite_eq_right hl]; exact fun p hp _ => hp
      | memop op x =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]; exact fun p hp _ => hp
          · simp only [ite_eq_right hd]; cases op with
            | alloc => exact fun p hp _ => hp
            | allocS => exact fun p hp _ => hp
            | deref =>
                by_cases hl : memInt (s.store x) s.live = true
                · simp only [ite_eq_left hl]; exact fun p hp _ => hp
                · simp only [ite_eq_right hl]; exact fun p hp _ => hp
            | free =>
                by_cases hl : memInt (s.store x) s.live = true
                · simp only [ite_eq_left hl]; exact fun p hp _ => hp
                · simp only [ite_eq_right hl]; exact fun p hp _ => hp
      | sop op x e =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [ite_eq_left hd]; exact fun p hp _ => hp
          · simp only [ite_eq_right hd]; cases op with
            | set => exact fun p hp _ => hp
            | emit =>
                intro p hp hpq
                rcases List.mem_cons.mp hp with h' | h'
                · exfalso
                  have : memStr q [x] = true := by
                    rw [← hpq, h']; simp [memStr]
                  rw [show sinksOf (.sop .emit x e) = [x] from rfl] at hq
                  rw [this] at hq; cases hq
                · exact h'
      | seq c₁ c₂ =>
          have h1 : memStr q (sinksOf c₁) = false ∧ memStr q (sinksOf c₂) = false :=
            memStr_append_false hq
          rw [uexec_seq_eq] at h
          rcases e₁ : uexec n c₁ π s with _ | r₁
          · rw [e₁] at h; simp at h
          · rw [e₁, Option.bind_some] at h
            rcases e₂ : uexec n c₂ π r₁.1 with _ | r₂
            · rw [e₂] at h; simp at h
            · rw [e₂] at h
              simp only [Option.map_some, Option.some.injEq] at h; subst h
              intro p hp hpq
              exact unwritten_sink_untouched n c₁ π s r₁ q h1.1 e₁ p
                (unwritten_sink_untouched n c₂ π r₁.1 r₂ q h1.2 e₂ p hp hpq) hpq
      | ite e c₁ c₂ =>
          have h1 : memStr q (sinksOf c₁) = false ∧ memStr q (sinksOf c₂) = false :=
            memStr_append_false hq
          rw [uexec_ite_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at h
            rcases e₁ : uexec n c₁ π s with _ | r₁
            · rw [e₁] at h; simp at h
            · rw [e₁] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact unwritten_sink_untouched n c₁ π s r₁ q h1.1 e₁
          · rw [ite_eq_right hg] at h
            rcases e₂ : uexec n c₂ π s with _ | r₂
            · rw [e₂] at h; simp at h
            · rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact unwritten_sink_untouched n c₂ π s r₂ q h1.2 e₂
      | loop e c₀ =>
          have h0 : memStr q (sinksOf c₀) = false := hq
          rw [uexec_loop_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at h
            rcases e₁ : uexec n c₀ π s with _ | r₁
            · rw [e₁] at h; simp at h
            · rw [e₁, Option.bind_some] at h
              rcases e₂ : uexec n (.loop e c₀) π r₁.1 with _ | r₂
              · rw [e₂] at h; simp at h
              · rw [e₂] at h
                simp only [Option.map_some, Option.some.injEq] at h; subst h
                intro p hp hpq
                exact unwritten_sink_untouched n c₀ π s r₁ q h0 e₁ p
                  (unwritten_sink_untouched n (.loop e c₀) π r₁.1 r₂ q hq e₂ p hp hpq) hpq
          · rw [ite_eq_right hg] at h
            simp only [Option.some.injEq] at h; subst h; exact fun p hp _ => hp

/-! ## The computed base, on the worked programs -/

/-- A pure computation incurs **nothing**: no reads, no emissions, no trusted base. -/
def pureProg : UCmd := .seq (.assign "x" (.num 1)) (.memop .alloc "buf")

theorem pureProg_needs_nothing : needs pureProg = [] := by decide

/-- And its guarantees are unconditional — with the empty ledger, which stage 1e's
    `Sat []` satisfies outright. -/
theorem pureProg_reads_nothing :
    ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
      uexec n pureProg π (initU σ) = some r → r.1.reads = [] := by
  intro n π σ r hr
  have := no_access_no_reads n pureProg π (initU σ) r (by decide) hr
  simpa [initU] using this

/-- `fiveProg` incurs both kinds: it reads a mediated resource and emits to `db`. Two
    entries, computed — where stage 1s charged every program three. -/
theorem fiveProg_needs :
    needs fiveProg = [Assume.policyIntended, Assume.sinkHonest "db"] := by decide

/-- The third entry of stage 1s's base — the filesystem — is **not** incurred by
    `fiveProg`, and `unwritten_sink_untouched` is why that is sound rather than an
    oversight: nothing is ever tagged `fs`. -/
theorem fiveProg_owes_the_filesystem_nothing :
    ¬ (Assume.sinkHonest "fs" ∈ needs fiveProg)
  ∧ ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
      uexec n fiveProg π (initU σ) = some r → ∀ p ∈ r.1.sink, p.1 = "fs" → False := by
  refine ⟨by decide, fun n π σ r hr p hp hpq => ?_⟩
  have := unwritten_sink_untouched n fiveProg π (initU σ) r "fs" (by decide) hr p hp hpq
  simpa [initU] using this

/-! ## What this settles

    Stage 1s's "the trusted base is three lines long" was a statement about the
    *language*. It is now a statement about a *program*, computed by `needs`, and the
    two vacuity lemmas prove the entries a program does not incur are ones it genuinely
    does not need — not ones that were forgotten.

    Left open deliberately: `needs` is syntactic and therefore conservative. A program
    containing an unreachable `access` is charged the policy entry, and nothing here
    tries to prove reachability — that is a different analysis and a worse trade, since
    over-charging the trusted base is the safe direction. -/

/-- The conservatism, as a theorem rather than a footnote: an `access` in dead code is
    still charged. -/
theorem needs_is_syntactic :
    needs (.ite (.num 0) (.access "db") .skip) = [Assume.policyIntended] := by decide

/-! ## The hypotheses are load-bearing -/

/-- A program that *does* write the filesystem is charged for it — so the exemption
    `fiveProg` enjoys is earned by its syntax, not built into `needs`. -/
theorem an_fs_writer_is_charged :
    needs (.sop .emit "fs" (.var "p")) = [Assume.sinkHonest "fs"] := by decide

/-- And a program that reads does add to `reads`, so `no_access_no_reads`'s hypothesis
    is not idle: drop it and the conclusion is false. -/
theorem access_really_reads :
    ((uexec 3 (.access "db") (fun _ => true) (initU (fun _ => 0))).map
      (fun r => r.1.reads)) = some ["db"]
  ∧ hasAccess (.access "db") = true := by decide

/-! ## Threading it into stage 1e's ledger

    Stage 1s built `toLedger`, a fixed three-element `Ledger`. `needsLedger` is the same
    construction over the *computed* entries, so it composes through `UCertL` like any
    other assumption list and is shorter exactly when the program earns it. -/

/-- The proposition each entry stands for. The sink named `fs` is the filesystem, whose
    obligation is `inside`; every other sink is a query parser, whose obligation is
    `accepts`. That correspondence is a modelling choice and is written down here rather
    than left implicit in `Deployment`'s field names. -/
def entryProp (D : Deployment) (Ks : List Nat) (fs : String) : Assume → Prop
  | .policyIntended => ∀ r, D.policy r = D.intended r
  | .sinkHonest q   =>
      if q = fs then (∀ t, safePath t = true → D.inside t)
                else (∀ t, qcount t ∈ Ks → D.accepts t)

/-- **The computed ledger.** Stage 1e's `Ledger`, built from the program instead of
    from the language. -/
def needsLedger (D : Deployment) (Ks : List Nat) (fs : String) (c : UCmd) : Ledger :=
  (needs c).map (entryProp D Ks fs)

/-- The fixed base always covers the computed one, so nothing that held before stops
    holding: `Discharged` is the conservative over-approximation `needs` refines. -/
theorem discharged_covers_needs {D : Deployment} {Ks : List Nat} {fs : String}
    (hD : Discharged D Ks) : ∀ c, Sat (needsLedger D Ks fs c) := by
  intro c
  have key : ∀ (L : List Assume), Sat (L.map (entryProp D Ks fs)) := by
    intro L
    induction L with
    | nil => exact trivial
    | cons a as ih =>
        refine ⟨?_, ih⟩
        cases a with
        | policyIntended => exact hD.policyIntended
        | sinkHonest q =>
            show entryProp D Ks fs (.sinkHonest q)
            by_cases hq : q = fs
            · simp only [entryProp, ite_eq_left hq]; exact hD.fsInside
            · simp only [entryProp, ite_eq_right hq]; exact hD.sinkAccepts
  exact key (needs c)

/-- **`fiveProg`'s ledger has two entries, not three.** Stage 1s charged it the
    filesystem; `fiveProg_owes_the_filesystem_nothing` is why that charge was
    unnecessary rather than merely unused. -/
theorem fiveProg_ledger (D : Deployment) :
    needsLedger D [2] "fs" fiveProg
      = [(∀ r, D.policy r = D.intended r), (∀ t, qcount t ∈ [2] → D.accepts t)] := by
  show (needs fiveProg).map (entryProp D [2] "fs") = _
  rw [fiveProg_needs]
  simp only [List.map_cons, List.map_nil, entryProp, ite_eq_right (by decide : ¬ ("db" = "fs"))]

/-- A pure computation's ledger is **empty**, so `Sat` is `True`. -/
theorem pureProg_ledger (D : Deployment) (Ks : List Nat) (fs : String) :
    needsLedger D Ks fs pureProg = [] := by
  show (needs pureProg).map (entryProp D Ks fs) = _
  rw [pureProg_needs_nothing]; rfl

/-- Nothing reaches a sink either. -/
theorem pureProg_sink_stays_empty (n : Nat) (π : MedPolicy) (σ : Store)
    (r : UState × Nat × List Bool) (h : uexec n pureProg π (initU σ) = some r) :
    r.1.sink = [] := by
  cases hs : r.1.sink with
  | nil => rfl
  | cons p ps =>
      exfalso
      have hmem : p ∈ r.1.sink := by rw [hs]; exact List.mem_cons_self ..
      have := unwritten_sink_untouched n pureProg π (initU σ) r p.1 rfl h p hmem rfl
      simpa [initU] using this

/-- **The payoff.** All three deployment-level guarantees for `pureProg`, with the
    ledger empty — no policy author, no parser, no filesystem trusted. Stage 1s could
    not state this: its `deployment_reading` demanded a `Discharged` record, and a
    `Discharged` record is three assumptions whether or not the program uses them. -/
theorem pureProg_deployed_with_nothing (D : Deployment) (Ks : List Nat) (fs : String) :
    Sat (needsLedger D Ks fs pureProg)
  ∧ (∀ (n : Nat) (σ : Store) (r : UState × Nat × List Bool),
        uexec n pureProg D.policy (initU σ) = some r → ∀ q ∈ r.1.reads, D.intended q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n pureProg π (initU σ) = some r → ∀ t ∈ r.1.sink, D.accepts t.2)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n pureProg π (initU σ) = some r →
        ∀ p ∈ r.1.sink, p.1 = fs → D.inside p.2) := by
  refine ⟨by rw [pureProg_ledger]; exact trivial, ?_, ?_, ?_⟩
  · intro n σ r hr q hq
    rw [pureProg_reads_nothing n D.policy σ r hr] at hq; cases hq
  · intro n π σ r hr t ht
    rw [pureProg_sink_stays_empty n π σ r hr] at ht; cases ht
  · intro n π σ r hr p hp _
    rw [pureProg_sink_stays_empty n π σ r hr] at hp; cases hp

/-- **And the same for the worked program, on two entries instead of three.** The
    filesystem conclusion still holds — vacuously, because `fiveProg` never emits to
    `fs`. This is the reduction actually delivering: stage 1s's `fiveProg_deployed`
    proves the identical three conclusions from a strictly stronger hypothesis. -/
theorem fiveProg_deployed_with_two (D : Deployment)
    (hΓ : Sat (needsLedger D [2] "fs" fiveProg)) :
    (∀ (n : Nat) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fiveProg D.policy (initU σ) = some r →
        ∀ q ∈ r.1.reads, D.intended q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fiveProg π (initU σ) = some r → ∀ t ∈ r.1.sink, D.accepts t.2)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fiveProg π (initU σ) = some r →
        ∀ p ∈ r.1.sink, p.1 = "fs" → D.inside p.2) := by
  rw [fiveProg_ledger] at hΓ
  obtain ⟨hpol, hacc, -⟩ := hΓ
  refine ⟨?_, ?_, ?_⟩
  · intro n σ r hr q hq
    rw [← hpol q]; exact fiveProg_five.2.1 n D.policy σ r hr q hq
  · intro n π σ r hr t ht
    exact hacc t.2 (fiveProg_five.2.2.2.2 n π σ r hr t ht)
  · intro n π σ r hr p hp hfs
    exact absurd (fiveProg_owes_the_filesystem_nothing.2 n π σ r hr p hp hfs) not_false

end ConfTyping
