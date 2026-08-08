/-
  Races and TOCTOU — brick 32: the class the map called OUT-OF-MODEL.

  Row 8 of `VULN-COVERAGE.md` (CWE-362/367) has been OUT-OF-MODEL [classified]
  since brick 1, with a named extension: *a nondeterministic small-step
  semantics with demonic scheduling*. This brick builds it, and the class moves
  to IN-WITH-MODEL (generated) [proved] — by the recipe §0 states for growing
  coverage: put the channel in the semantics, then the same machinery applies.

  The machine is deliberately small and deliberately *fine-grained*, because
  fine grain is the whole phenomenon. A thread is a list of instructions, each
  of which is one indivisible machine step over a shared store; every thread
  has private registers. A **schedule** is a list of thread indices, so the
  nondeterminism is a data parameter: "under some interleaving" is an existential
  a witness can discharge by `decide`, and "under every interleaving" is a
  universal over *all* index lists — demonic, unfair, arbitrary — which is the
  strongest quantification a safety property can ask for.

  What gets proved:

  * **The race.** Two threads each run the classic check-then-act withdrawal
    (`load` the balance, `guard` that it covers the amount, `decsh` debit it).
    `toctou_interleaving_unsafe` — under one interleaving the balance goes
    *negative*: both threads read 100, both pass the guard, both debit 60.
    CWE-367 as a theorem, on a machine where the check and the act are separate
    steps because they are separate steps.

  * **Why the class was out of model, precisely.**
    `sequential_model_misses_races` — every *sequential* schedule of the same
    two threads keeps the balance non-negative. So a proof in the sequential
    semantics is not wrong; it is true of a different machine. That gap is what
    row 8 was recording, and it is now a theorem rather than a caveat.

  * **The fix, safe by construction.** Wrapping the critical section in an
    `atom` makes it one scheduling step. `atomic_all_schedules_safe` — the
    invariant holds under **every** schedule, proved (not sampled) by induction
    over the schedule.

  * **Generated.** `racefree` is a decidable syntactic check: no bare shared
    write outside a critical section. `racy_rejected`/`atomic_accepted` decide
    it, and `racefree_all_schedules` is the soundness theorem — and it is the
    interesting one, because it is a *reduction*: for a checked pool, the
    concurrent obligation "the invariant survives every interleaving" follows
    from the sequential obligation "each critical section preserves the
    invariant". Concurrency verification collapses to per-section sequential
    verification, gated by a Boolean.

  Honest limits, stated: this is a **safety** result under demonic scheduling —
  fairness, liveness, deadlock and the lock-acquisition discipline are not
  modeled (an `atom` is an idealized critical section, not a lock protocol);
  the check reduces the concurrent obligation but does not discharge it, so a
  critical section that is itself wrong is still wrong (`Preserves` is a
  hypothesis, and `bad_atom_not_preserving` witnesses that it has teeth); and
  the memory model is sequentially consistent — no store buffers, no
  reordering.
-/
import ConfTyping.Imp

namespace ConfTyping

/-! ## The machine

    Base instructions are the indivisible steps. The grain matters: `load` and
    `decsh` being *separate* steps is exactly what makes check-then-act
    exploitable, and collapsing them is exactly what the fix does. -/

/-- One indivisible machine step. -/
inductive RBase where
  | load  : String → String → RBase   -- `load r s` : ρ r := σ s (read shared)
  | guard : String → Int → RBase      -- `guard r n` : abort this thread if ρ r < n
  | decsh : String → Int → RBase      -- `decsh s n` : σ s := σ s − n (relative write)
  | store : String → String → RBase   -- `store s r` : σ s := ρ r (absolute write)
  deriving Repr

/-- A thread instruction: a base step, or a **critical section** — a list of
    base steps executed as one indivisible scheduling step. -/
inductive RInstr where
  | base : RBase → RInstr
  | atom : List RBase → RInstr
  deriving Repr

/-- Thread-private registers; same shape as the shared store, so `upd` serves
    both, but no thread can observe another's. -/
abbrev Regs := Store

/-- A thread: its remaining instructions and its private registers. -/
abbrev RThread := List RInstr × Regs

/-- A configuration: a pool of threads over one shared store. -/
structure RCfg where
  pool : List RThread
  sh   : Store

/-! ## Execution

    Each executor returns the new shared store, the new registers, and whether
    the thread **aborted** (a failed guard abandons the rest of the thread —
    "the check failed, so don't act"). -/

/-- One indivisible step. -/
def rexecBase : RBase → Store → Regs → (Store × Regs × Bool)
  | .load r s,  σ, ρ => (σ, upd ρ r (σ s), false)
  | .guard r n, σ, ρ => (σ, ρ, decide (ρ r < n))
  | .decsh s n, σ, ρ => (upd σ s (σ s - n), ρ, false)
  | .store s r, σ, ρ => (upd σ s (ρ r), ρ, false)

/-- A critical section runs its base steps to completion, with no scheduling
    point in between — that is the entire content of atomicity here. -/
def rexecSeq : List RBase → Store → Regs → (Store × Regs × Bool)
  | [],      σ, ρ => (σ, ρ, false)
  | b :: bs, σ, ρ =>
      let s := rexecBase b σ ρ
      if s.2.2 then (s.1, s.2.1, true) else rexecSeq bs s.1 s.2.1

/-- One scheduling step of a thread instruction. -/
def rexec : RInstr → Store → Regs → (Store × Regs × Bool)
  | .base b,  σ, ρ => rexecBase b σ ρ
  | .atom bs, σ, ρ => rexecSeq bs σ ρ

/-- Run one step of the `i`-th thread. Scheduling a finished or nonexistent
    thread is a no-op — so a schedule may be arbitrary, unfair, and repetitive,
    which is what makes the universal quantification demonic. -/
def rstepPool : Nat → List RThread → Store → (List RThread × Store)
  | _,     [],      σ => ([], σ)
  | 0,     t :: ts, σ =>
      match t.1 with
      | []          => (t :: ts, σ)
      | ins :: rest =>
          let s := rexec ins σ t.2
          (((if s.2.2 then [] else rest), s.2.1) :: ts, s.1)
  | n + 1, t :: ts, σ =>
      let r := rstepPool n ts σ
      (t :: r.1, r.2)

/-- One step of the whole configuration, under scheduler choice `i`. -/
def rstep (i : Nat) (c : RCfg) : RCfg :=
  let r := rstepPool i c.pool c.sh
  ⟨r.1, r.2⟩

/-- Run a schedule: the interleaving is the data. -/
def rrun : List Nat → RCfg → RCfg
  | [],     c => c
  | i :: s, c => rrun s (rstep i c)

/-! ## The syntactic check

    A bare shared write outside a critical section is the syntactic signature
    of a race: it is the point at which another thread's step can land between
    a read and its dependent write. -/

/-- Does this base step write the shared store? -/
def writesShB : RBase → Bool
  | .decsh _ _ => true
  | .store _ _ => true
  | _          => false

/-- The rule: shared writes only inside critical sections. -/
def rfI : RInstr → Bool
  | .base b => !writesShB b
  | .atom _ => true

/-- The decidable check on a thread. -/
def racefree (t : List RInstr) : Bool := t.all rfI

/-! ## Soundness: the reduction to a sequential obligation -/

/-- An instruction preserves the invariant `I` of the shared store, whatever
    the registers. For non-writing steps this is free; for a critical section
    it is a *sequential* proof obligation. -/
def Preserves (I : Store → Prop) (ins : RInstr) : Prop :=
  ∀ σ ρ, I σ → I (rexec ins σ ρ).1

/-- Every instruction still to be executed by every thread preserves `I`. -/
def PoolPreserves (I : Store → Prop) (P : List RThread) : Prop :=
  ∀ t ∈ P, ∀ ins ∈ t.1, Preserves I ins

/-- A step that does not write the shared store leaves it untouched — so it
    preserves every store predicate, with no obligation at all. -/
theorem rexecBase_pure : ∀ (b : RBase), writesShB b = false → ∀ σ ρ,
    (rexecBase b σ ρ).1 = σ
  | .load _ _,  _, _, _ => rfl
  | .guard _ _, _, _, _ => rfl
  | .decsh _ _, h, _, _ => by simp [writesShB] at h
  | .store _ _, h, _, _ => by simp [writesShB] at h

/-- **The syntactic bridge.** A thread that passes the check carries no
    obligation except at its critical sections: everything else provably cannot
    touch the shared store. -/
theorem racefree_poolPreserves {I : Store → Prop} {P : List RThread}
    (hrf : ∀ t ∈ P, racefree t.1 = true)
    (hat : ∀ t ∈ P, ∀ bs, RInstr.atom bs ∈ t.1 → Preserves I (.atom bs)) :
    PoolPreserves I P := by
  intro t ht ins hins
  have hall : rfI ins = true := by
    have := hrf t ht
    simp only [racefree, List.all_eq_true] at this
    exact this ins hins
  cases ins with
  | base b =>
      have hw : writesShB b = false := by
        simpa [rfI] using hall
      intro σ ρ hI
      show I (rexecBase b σ ρ).1
      rw [rexecBase_pure b hw σ ρ]
      exact hI
  | atom bs => exact hat t ht bs hins

/-- Instructions preserved by a pool are preserved by any thread's tail. -/
theorem poolPreserves_step {I : Store → Prop} : ∀ (i : Nat) (P : List RThread) (σ : Store),
    PoolPreserves I P → I σ →
    PoolPreserves I (rstepPool i P σ).1 ∧ I (rstepPool i P σ).2
  | _,     [],      σ, _,  hI => by
      constructor
      · intro t ht; simp [rstepPool] at ht
      · simpa [rstepPool] using hI
  | 0,     t :: ts, σ, hp, hI => by
      cases hins : t.1 with
      | nil =>
          constructor
          · simp only [rstepPool, hins]; exact hp
          · simp only [rstepPool, hins]; exact hI
      | cons ins rest =>
          have hpre : Preserves I ins := hp t (by simp) ins (by rw [hins]; simp)
          have hIσ' : I (rexec ins σ t.2).1 := hpre σ t.2 hI
          refine ⟨?_, ?_⟩ <;> simp only [rstepPool, hins]
          · intro u hu
            rcases List.mem_cons.mp hu with hu | hu
            · subst hu
              intro j hj
              have : j ∈ rest := by
                by_cases hab : (rexec ins σ t.2).2.2 = true
                · simp only [hab, if_pos] at hj; simp at hj
                · simp only [Bool.not_eq_true] at hab
                  simpa [hab] using hj
              exact hp t (by simp) j (by rw [hins]; exact List.mem_cons_of_mem _ this)
            · exact hp u (List.mem_cons_of_mem _ hu)
          · exact hIσ'
  | n + 1, t :: ts, σ, hp, hI => by
      have ih := poolPreserves_step n ts σ
        (fun u hu => hp u (List.mem_cons_of_mem _ hu)) hI
      refine ⟨?_, ?_⟩ <;> simp only [rstepPool]
      · intro u hu
        rcases List.mem_cons.mp hu with hu | hu
        · subst hu; exact hp u (by simp)
        · exact ih.1 u hu
      · exact ih.2

/-- **The invariant survives every schedule.** Induction over the interleaving:
    each scheduler choice is one application of the step lemma. -/
theorem rrun_preserves {I : Store → Prop} : ∀ (sched : List Nat) (c : RCfg),
    PoolPreserves I c.pool → I c.sh → I (rrun sched c).sh
  | [],       _, _,  hI => hI
  | i :: s, c, hp, hI => by
      have h := poolPreserves_step i c.pool c.sh hp hI
      exact rrun_preserves s (rstep i c) h.1 h.2

/-- **The reduction — the brick's central theorem.** If the syntactic check
    passes (no bare shared write) and each critical section preserves the
    invariant *sequentially*, then the invariant holds after **every**
    interleaving. The concurrent obligation is discharged by a Boolean plus one
    sequential proof per critical section. -/
theorem racefree_all_schedules {I : Store → Prop} {P : List RThread} {σ : Store}
    (hrf : ∀ t ∈ P, racefree t.1 = true)
    (hat : ∀ t ∈ P, ∀ bs, RInstr.atom bs ∈ t.1 → Preserves I (.atom bs))
    (h0 : I σ) (sched : List Nat) : I (rrun sched ⟨P, σ⟩).sh :=
  rrun_preserves sched ⟨P, σ⟩ (racefree_poolPreserves hrf hat) h0

/-! ## The witness: concurrent withdrawal

    The textbook TOCTOU. Balance 100, two threads each withdrawing 60. The
    check (`guard`) and the act (`decsh`) are separate steps, so a scheduler
    can land the second thread's check before the first thread's debit. -/

def vBal : String := "b"
def rReg : String := "r"

/-- Read the balance, check it covers 60, debit 60. -/
def wdBody : List RBase := [.load rReg vBal, .guard rReg 60, .decsh vBal 60]

/-- The racy thread: three separate scheduling steps. -/
def racyT : List RInstr :=
  [.base (.load rReg vBal), .base (.guard rReg 60), .base (.decsh vBal 60)]

/-- The fixed thread: the same three steps, as one critical section. -/
def atomT : List RInstr := [.atom wdBody]

def rρ0 : Regs := fun _ => 0
def rσ0 : Store := upd (fun _ => 0) vBal 100

def racyCfg : RCfg := ⟨[(racyT, rρ0), (racyT, rρ0)], rσ0⟩
def atomCfg : RCfg := ⟨[(atomT, rρ0), (atomT, rρ0)], rσ0⟩

/-- The exploiting interleaving: both threads check before either debits. -/
def raceSched : List Nat := [0, 0, 1, 1, 0, 1]

/-- The two sequential schedules — what a test suite explores. -/
def seqSched01 : List Nat := [0, 0, 0, 1, 1, 1]
def seqSched10 : List Nat := [1, 1, 1, 0, 0, 0]

/-- **The race, as a theorem** (axiom-free). Under `raceSched` the balance goes
    negative: both threads read 100, both pass the guard, both debit 60. This
    is CWE-367 — the check is stale by the time the act runs. -/
theorem toctou_interleaving_unsafe : (rrun raceSched racyCfg).sh vBal < 0 := by decide

/-- Under either sequential schedule the same program is safe: the second
    thread's guard sees the debited balance and abandons the withdrawal. -/
theorem racy_seq_safe :
    0 ≤ (rrun seqSched01 racyCfg).sh vBal ∧ 0 ≤ (rrun seqSched10 racyCfg).sh vBal := by
  decide

/-- **Why row 8 was OUT-OF-MODEL, precisely.** Every sequential schedule of
    this program is safe and one interleaving is not — so a proof carried out
    in the sequential semantics is true, and true of a machine the program does
    not run on. The gap the map recorded as a caveat is now a theorem, and the
    fix for it is a bigger semantics, exactly as §0's recipe says. -/
theorem sequential_model_misses_races :
    (0 ≤ (rrun seqSched01 racyCfg).sh vBal)
  ∧ (0 ≤ (rrun seqSched10 racyCfg).sh vBal)
  ∧ ((rrun raceSched racyCfg).sh vBal < 0) := by decide

/-! ## The fix, generated -/

/-- The checker rejects the racy thread: a bare `decsh` on shared state. -/
theorem racy_rejected : racefree racyT = false := by decide

/-- The checker accepts the atomic thread. -/
theorem atomic_accepted : racefree atomT = true := by decide

/-- The balance invariant. -/
abbrev NonNeg (σ : Store) : Prop := 0 ≤ σ vBal

/-- **The sequential obligation, discharged.** The critical section preserves
    the invariant: either the guard fails and the store is untouched, or the
    balance covered the amount and the debit leaves it non-negative. One
    ordinary sequential proof — no interleavings appear. -/
theorem wd_atom_preserves : Preserves NonNeg (.atom wdBody) := by
  intro σ ρ h
  show NonNeg (rexecSeq wdBody σ ρ).1
  by_cases hg : σ vBal < 60
  · have he : (rexecSeq wdBody σ ρ).1 = σ := by
      simp [wdBody, rexecSeq, rexecBase, upd, hg]
    rw [he]; exact h
  · have he : (rexecSeq wdBody σ ρ).1 vBal = σ vBal - 60 := by
      simp [wdBody, rexecSeq, rexecBase, upd, hg]
    show 0 ≤ (rexecSeq wdBody σ ρ).1 vBal
    rw [he]
    omega

/-- **The fix is safe under every interleaving** — not sampled, proved. The
    schedule is universally quantified over all index lists: unfair, repetitive
    and adversarial ones included. -/
theorem atomic_all_schedules_safe (sched : List Nat) :
    0 ≤ (rrun sched atomCfg).sh vBal := by
  have hrf : ∀ t ∈ atomCfg.pool, racefree t.1 = true := by
    intro t ht
    rcases List.mem_cons.mp ht with h | h
    · subst h; exact atomic_accepted
    · rcases List.mem_cons.mp h with h | h
      · subst h; exact atomic_accepted
      · simp at h
  have hat : ∀ t ∈ atomCfg.pool, ∀ bs, RInstr.atom bs ∈ t.1 →
      Preserves NonNeg (.atom bs) := by
    intro t ht bs hbs
    have hT : t.1 = atomT := by
      rcases List.mem_cons.mp ht with h | h
      · subst h; rfl
      · rcases List.mem_cons.mp h with h | h
        · subst h; rfl
        · simp at h
    rw [hT, atomT] at hbs
    have : bs = wdBody := by simpa using hbs
    subst this
    exact wd_atom_preserves
  exact racefree_all_schedules hrf hat (by decide) sched

/-- **Row 8's upgrade, as one theorem.** The racy program is rejected by a
    decidable check and genuinely exploitable; the fixed program is accepted
    and safe under every interleaving. Attack and safe-by-construction defense,
    the same shape as the made-real sink bricks — now for a scheduling channel
    rather than a lexical one. -/
theorem race_rejected_atomic_safe :
    racefree racyT = false
  ∧ ((rrun raceSched racyCfg).sh vBal < 0)
  ∧ racefree atomT = true
  ∧ (∀ sched, 0 ≤ (rrun sched atomCfg).sh vBal) :=
  ⟨racy_rejected, toctou_interleaving_unsafe, atomic_accepted, atomic_all_schedules_safe⟩

/-! ## The check reduces the obligation — it does not discharge it -/

/-- A critical section that is atomic but *wrong*: it debits without checking. -/
def badBody : List RBase := [.decsh vBal 60]

/-- **The hypothesis has teeth.** Atomicity alone buys nothing: this section is
    a single scheduling step, so the checker accepts it, yet it does not
    preserve the invariant — and `racefree_all_schedules` therefore does not
    apply to it. The check reduces the concurrent obligation to a sequential
    one; it does not make the sequential one true. -/
theorem bad_atom_not_preserving : ¬ Preserves NonNeg (.atom badBody) := by
  intro h
  have := h (fun _ => 0) rρ0 (by decide)
  revert this
  decide

/-- And the checker does accept it — so the residual obligation is exactly the
    per-section one, visible and unautomated. -/
theorem bad_atom_accepted : racefree [.atom badBody] = true := by decide

end ConfTyping
