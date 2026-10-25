/-
  Speculative execution — brick 33: the last OUT-OF-MODEL row.

  Row 9 of `VULN-COVERAGE.md` (Spectre-class) has been OUT-OF-MODEL since brick 1,
  with the honest note that "nothing in this repo excludes Spectre, and no verdict
  pretends otherwise", plus the caveat that the model is research-scale. Brick 32 ran
  §0's recipe — put the channel in the semantics — for scheduling. This runs it a
  third time, for **speculation**, at the scale the caveat allows: not a
  microarchitecture, but a genuine transient-execution machine carrying the one
  channel that matters, with the bounds-check bypass (Spectre-v1) on it.

  The machine has an **architectural** state that rolls back and a
  **microarchitectural** trace that does not. A `brLt` branch may be *mispredicted*:
  its body then runs **transiently** for a bounded window, its register effects are
  discarded, and only the addresses it touched survive — in the trace. That asymmetry
  is the whole of Spectre, and it is the whole of this model.

  A **misprediction schedule** is a list of window budgets, consumed one per branch
  reached, so speculation is a data parameter exactly as the interleaving was in
  brick 32: "under some misprediction" is decidable on a witness, "under every
  misprediction" quantifies over all schedules, unbounded windows included.

  What gets proved:

  * **The attack.** The victim `if i < 4 then (x := mem[i]; y := mem[x])` is the
    textbook gadget — the second load's *address* is the first load's *value*. With
    `i` out of bounds the guard is false, yet a mispredicting schedule runs the body
    anyway and the trace records the secret **as an address**: `spectre_leaks`, two
    memories differing only at the secret giving different traces.

  * **Why the class was out of model, precisely.** `arch_indistinguishable` — the
    architectural machine executes nothing (the guard is false), so those same two
    memories give *identical* traces. The program is secure on the machine the
    semantics described and insecure on the machine it runs on. Third instance of
    §0's model gap made concrete, after bricks 2 (timing) and 32 (scheduling).

  * **The fix, by construction, and composable.** `specCheck` is a decidable rule —
    every branch body begins with a `fence`. Its soundness `spec_inert` is the strong
    form: on a checked program the speculative registers *and* trace **equal** the
    architectural ones, under **every** schedule. Speculation is then observationally
    inert, so every architectural guarantee transfers verbatim — including the
    noninterference the rest of this repo generates (`fixed_secret_independent`).

  Honest limits, stated. The microarchitectural state is an address trace: cache-line
  granularity, eviction, timing and contention are not modelled, so what is excluded
  is the address-visible channel, not every physical side channel. Only conditional
  branch misprediction (v1) is modelled — no indirect branches (v2), no
  store-to-load forwarding (v4), and rollback is perfect. Branch bodies are a
  *separate instruction type* with no `brLt` in it, so nested speculation is excluded
  **by the syntax** rather than silently ignored by the semantics. The
  check is **sufficient, not necessary**: it rejects safe bodies that merely begin
  with a constant-address load, whose transient trace is a constant and therefore
  carries nothing. Lifting it to "no address-dependent load before the fence" is the
  named follow-on.
-/
import ConfTyping.Imp

namespace ConfTyping

/-! ## The machine -/

abbrev Addr := Nat

/-- Memory: a flat address space. -/
abbrev Mem := Addr → Int

/-- Registers. Separate from `Store` so nothing collides with the earlier bricks. -/
abbrev SRegs := String → Int

/-- The microarchitectural residue: the addresses whose lines were touched, in order.
    This is the only state a rollback does **not** undo. -/
abbrev Trace := List Addr

/-- Straight-line instructions — what a branch body may contain. `loadK` reads a
    *constant* address; `loadIdx` reads the address held in a register, the
    address-dependent load Spectre-v1 turns into a channel. There is no branch here:
    nested speculation is excluded by the syntax. -/
inductive SBase where
  | loadK   : String → Addr → SBase       -- `r := mem a`,       touches `a`
  | loadIdx : String → String → SBase     -- `r := mem (reg s)`, touches `reg s`
  | fence   : SBase                       -- speculation barrier
  deriving Repr

/-- A program instruction: a straight-line step, or the mispredictable branch. -/
inductive SInstr where
  | base : SBase → SInstr
  | brLt : String → Int → List SBase → SInstr    -- `if reg r < n then body`
  deriving Repr

/-- A register value read as an address. -/
def toAddr (v : Int) : Addr := v.toNat

/-! ## Execution -/

/-- **Transient execution**: run a body for at most `w` steps and keep only the trace.
    Discarding the registers is the rollback; keeping the trace is the leak. A `fence`
    halts it. -/
def specRun : Nat → List SBase → Mem → SRegs → Trace
  | 0,     _,                  _, _ => []
  | _,     [],                 _, _ => []
  | w + 1, .loadK r a :: is,   m, ρ => a :: specRun w is m (upd ρ r (m a))
  | w + 1, .loadIdx r x :: is, m, ρ =>
      toAddr (ρ x) :: specRun w is m (upd ρ r (m (toAddr (ρ x))))
  | _ + 1, .fence :: _,        _, _ => []

/-- Straight-line execution: registers and trace. -/
def archBase : List SBase → Mem → SRegs → SRegs × Trace
  | [],                 _, ρ => (ρ, [])
  | .loadK r a :: is,   m, ρ => let s := archBase is m (upd ρ r (m a)); (s.1, a :: s.2)
  | .loadIdx r x :: is, m, ρ =>
      let a := toAddr (ρ x); let s := archBase is m (upd ρ r (m a)); (s.1, a :: s.2)
  | .fence :: is,       m, ρ => archBase is m ρ

/-- **Architectural execution**: a branch runs its body iff the guard holds, and
    nothing else ever runs. -/
def archRun : List SInstr → Mem → SRegs → SRegs × Trace
  | [],                    _, ρ => (ρ, [])
  | .base b :: is,         m, ρ =>
      let s1 := archBase [b] m ρ; let s2 := archRun is m s1.1; (s2.1, s1.2 ++ s2.2)
  | .brLt r n body :: is,  m, ρ =>
      if ρ r < n then
        let s1 := archBase body m ρ; let s2 := archRun is m s1.1; (s2.1, s1.2 ++ s2.2)
      else archRun is m ρ

/-- **Speculative execution.** At each branch the schedule supplies a misprediction
    window. When the prediction disagrees with the guard the body runs transiently:
    its trace is kept, its state is not. -/
def specExec : List Nat → List SInstr → Mem → SRegs → SRegs × Trace
  | _,     [],                   _, ρ => (ρ, [])
  | sched, .base b :: is,        m, ρ =>
      let s1 := archBase [b] m ρ
      let s2 := specExec sched is m s1.1
      (s2.1, s1.2 ++ s2.2)
  | sched, .brLt r n body :: is, m, ρ =>
      if ρ r < n then
        let s1 := archBase body m ρ
        let s2 := specExec (sched.tailD []) is m s1.1
        (s2.1, s1.2 ++ s2.2)
      else
        -- guard false, prediction says taken: the body runs transiently
        let s2 := specExec (sched.tailD []) is m ρ
        (s2.1, specRun (sched.headD 0) body m ρ ++ s2.2)

/-- The trace left under a given misprediction schedule. -/
def specTrace (sched : List Nat) (p : List SInstr) (m : Mem) (ρ : SRegs) : Trace :=
  (specExec sched p m ρ).2

/-- The trace the architectural machine leaves. -/
def archTrace (p : List SInstr) (m : Mem) (ρ : SRegs) : Trace := (archRun p m ρ).2

/-! ## The syntactic check -/

/-- A body that begins with a barrier (or is empty) leaves no transient trace. -/
def startsFenced : List SBase → Bool
  | []          => true
  | .fence :: _ => true
  | _           => false

/-- The check: every branch body begins with a `fence`. -/
def specCheck : List SInstr → Bool
  | []                => true
  | .brLt _ _ b :: r  => startsFenced b && specCheck r
  | _ :: r            => specCheck r

/-! ## Soundness: on a checked program, speculation is observationally inert -/

/-- A fenced body has an empty transient trace, whatever the window, memory or
    registers — the barrier is reached before anything is touched. -/
theorem specRun_startsFenced (w : Nat) (b : List SBase) (m : Mem) (ρ : SRegs)
    (h : startsFenced b = true) : specRun w b m ρ = [] := by
  cases w with
  | zero => rfl
  | succ w =>
      cases b with
      | nil => rfl
      | cons i is =>
          cases i with
          | fence => rfl
          | loadK r a => simp [startsFenced] at h
          | loadIdx r x => simp [startsFenced] at h

/-- **The soundness theorem.** On a checked program the speculative run agrees with
    the architectural run in *both* components — registers and trace — under every
    misprediction schedule. Every mispredicted body is fenced, so it contributes
    nothing; every correctly-predicted path is the architectural path. -/
theorem specCheck_sound : ∀ (p : List SInstr) (sched : List Nat) (m : Mem) (ρ : SRegs),
    specCheck p = true → specExec sched p m ρ = archRun p m ρ
  | [],                   _,     _, _, _ => rfl
  | .base b :: is,        sched, m, ρ, h => by
      have hr : specCheck is = true := by simpa [specCheck] using h
      simp only [specExec, archRun, specCheck_sound is sched m (archBase [b] m ρ).1 hr]
  | .brLt r n body :: is, sched, m, ρ, h => by
      obtain ⟨hb, hr⟩ : startsFenced body = true ∧ specCheck is = true := by
        simpa [specCheck] using h
      by_cases hg : ρ r < n
      · simp only [specExec, archRun, ite_eq_left hg,
          specCheck_sound is (sched.tailD []) m (archBase body m ρ).1 hr]
      · simp only [specExec, archRun, ite_eq_right hg,
          specRun_startsFenced (sched.headD 0) body m ρ hb,
          specCheck_sound is (sched.tailD []) m ρ hr, List.nil_append]

/-- **Speculation is observationally inert on checked programs**: the trace under any
    misprediction schedule is the architectural trace. -/
theorem spec_inert {p : List SInstr} (h : specCheck p = true)
    (sched : List Nat) (m : Mem) (ρ : SRegs) :
    specTrace sched p m ρ = archTrace p m ρ := by
  simp only [specTrace, archTrace, specCheck_sound p sched m ρ h]

/-- **The transfer, which is why the row is composable.** For a checked program, any
    two memories the *architectural* machine cannot distinguish are indistinguishable
    speculatively too — so every architectural noninterference result carries over,
    against every schedule. -/
theorem arch_ni_transfers {p : List SInstr} (h : specCheck p = true)
    {m₁ m₂ : Mem} {ρ : SRegs} (harch : archTrace p m₁ ρ = archTrace p m₂ ρ)
    (sched : List Nat) : specTrace sched p m₁ ρ = specTrace sched p m₂ ρ := by
  rw [spec_inert h sched m₁ ρ, spec_inert h sched m₂ ρ, harch]

/-! ## The witness: the bounds-check bypass -/

/-- The public array occupies `[0,4)`; address 8 holds the secret. -/
def secretAddr : Addr := 8

def memA : Mem := fun a => if a = secretAddr then 42 else 1
def memB : Mem := fun a => if a = secretAddr then 99 else 1

/-- The registers: `i` is **out of bounds**, so the guard is false. -/
def rho0 : SRegs := fun x => if x = "i" then 8 else 0

/-- The gadget: load `mem[i]`, then use the value *as an address*. -/
def gadget : List SBase := [.loadIdx "x" "i", .loadIdx "y" "x"]

/-- The victim: the bounds check, unfenced. -/
def victim : List SInstr := [.brLt "i" 4 gadget]

/-- The fix: the same program with a barrier after the bounds check. -/
def fixedP : List SInstr := [.brLt "i" 4 (.fence :: gadget)]

/-- A schedule granting a three-instruction misprediction window. -/
def misp : List Nat := [3]

/-- **The architectural machine sees nothing.** The guard is false, the body never
    runs, and the two memories are indistinguishable — the program is secure on the
    semantics bricks 1–32 describe. -/
theorem arch_indistinguishable :
    archTrace victim memA rho0 = archTrace victim memB rho0 := by decide

/-- **Spectre-v1, as a theorem** (axiom-free). Under a mispredicting schedule the
    body runs anyway; the first load reads the out-of-bounds secret, the second uses
    it as an address, and the trace differs between two memories that differ only at
    the secret. -/
theorem spectre_leaks :
    specTrace misp victim memA rho0 ≠ specTrace misp victim memB rho0 := by decide

/-- The leak is literally the secret, appearing as a touched address. -/
theorem spectre_trace_is_the_secret :
    specTrace misp victim memA rho0 = [8, 42] ∧
    specTrace misp victim memB rho0 = [8, 99] := by decide

/-- **Why row 9 was OUT-OF-MODEL, precisely.** Architecturally the two runs are
    identical; speculatively they are not. A proof carried out in the non-speculative
    semantics is true — of a machine the program does not run on. -/
theorem speculative_model_misses_it :
    (archTrace victim memA rho0 = archTrace victim memB rho0)
  ∧ (specTrace misp victim memA rho0 ≠ specTrace misp victim memB rho0) :=
  ⟨arch_indistinguishable, spectre_leaks⟩

/-- **The window has real depth.** A one-instruction misprediction window leaks only
    the (public) index; reaching the secret needs the second load, so the transient
    channel is not an artefact of an unbounded window — it has a measurable depth,
    and the model resolves it. -/
theorem leak_needs_window_two :
    specTrace [1] victim memA rho0 = specTrace [1] victim memB rho0
  ∧ specTrace [2] victim memA rho0 ≠ specTrace [2] victim memB rho0 := by decide

/-! ## The fix, generated -/

theorem victim_rejected : specCheck victim = false := by decide
theorem fixed_accepted : specCheck fixedP = true := by decide

/-- **The fix is safe under every misprediction schedule** — proved, not sampled. -/
theorem fixed_no_transient_leak (sched : List Nat) (m : Mem) (ρ : SRegs) :
    specTrace sched fixedP m ρ = archTrace fixedP m ρ :=
  spec_inert fixed_accepted sched m ρ

/-- And therefore the secret is invisible under every schedule: architectural
    indistinguishability transfers. -/
theorem fixed_secret_independent (sched : List Nat) :
    specTrace sched fixedP memA rho0 = specTrace sched fixedP memB rho0 :=
  arch_ni_transfers fixed_accepted (by decide) sched

/-- **Row 9's upgrade, as one theorem.** The victim is rejected by a decidable check
    and genuinely leaks the secret through the transient channel; the fixed program
    is accepted and observationally inert under every misprediction. Attack and
    safe-by-construction defense, the shape of bricks 14–32 — now for a
    microarchitectural channel. -/
theorem spectre_rejected_fixed_safe :
    specCheck victim = false
  ∧ (specTrace misp victim memA rho0 ≠ specTrace misp victim memB rho0)
  ∧ specCheck fixedP = true
  ∧ (∀ sched, specTrace sched fixedP memA rho0 = specTrace sched fixedP memB rho0) :=
  ⟨victim_rejected, spectre_leaks, fixed_accepted, fixed_secret_independent⟩

/-! ## The check has teeth, and the named residual -/

/-- Atomicity of the barrier is what does the work: a body that begins with a
    *constant-address* load is rejected, even though its transient trace is a
    constant and so carries nothing. The check is sufficient, not necessary — this is
    the follow-on. -/
def benignBody : List SBase := [.loadK "z" 0, .fence]

theorem benign_rejected : specCheck [.brLt "i" 4 benignBody] = false := by decide

/-- But it is not vacuously strict: the transient trace of that body really is
    independent of the secret, which is why the residual is a *refinement* and not a
    soundness bug. -/
theorem benign_transient_is_constant :
    specRun 3 benignBody memA rho0 = specRun 3 benignBody memB rho0 := by decide

end ConfTyping
