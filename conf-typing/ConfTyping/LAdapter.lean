/-
  UCmd as L's first `Lang` (PH1 step 6). Not Ring 0: an adapter from the existing language to
  the kernel's interface, plus the adequacy theorem that the existing checker's certificates
  are instances of the kernel's three shapes.

  A run starts from `initU σ`; the input is the store `σ`, and two inputs are indistinguishable
  when they agree on Low variables. The observation:
  - events: every read, then every emitted string (each list in program order; the
    interleaving of reads with emits is not recorded in v1);
  - leakage: the branch trace, then the address trace (`uaddrs`, S-OBS);
  - cost: `uexec`'s step count;
  - outcome: `abort` if the run refused or faulted, `done` otherwise, and `fuel` with an empty
    record when the fuel ran out (`uexec` returns no prefix).
-/
import ConfTyping.AddrLeak
import ConfTyping.CountedLoop
import LCore

namespace ConfTyping

def uchCode : UCh → Nat
  | .ord   => 0
  | .quote => 1

/-- A final state's events, in program order. -/
def uEvents (s : UState) : List LCore.Ev :=
  s.reads.reverse.map LCore.Ev.read ++
    s.sink.reverse.map (fun t => LCore.Ev.emit t.1 (t.2.map uchCode))

/-- The observation of one run. -/
def uBeh (r : Option (UState × Nat × List Bool)) (a : Option (List Int)) : LCore.Beh :=
  match r, a with
  | some r, some a =>
      { ev   := uEvents r.1
        lk   := r.2.2.map LCore.Lk.branch ++ a.map LCore.Lk.addr
        cost := r.2.1
        out  := if r.1.dead then .abort else .done }
  | _, _ => { ev := [], lk := [], cost := 0, out := .fuel }

/-- **UCmd as an L `Lang`**, for a partition `P` and a monitor policy `π`. -/
def ucmdLang (P : Partition) (π : MedPolicy) : LCore.Lang where
  Prog  := UCmd
  In    := Store
  lowIn := lowEq P
  run n c σ := uBeh (uexec n c π (initU σ)) (uaddrs n c π (initU σ))

/-- The mediation property as a `trace` predicate: every read resource is one the policy
    allows. -/
def mediated (π : MedPolicy) (evs : List LCore.Ev) : Prop :=
  ∀ r, LCore.Ev.read r ∈ evs → π r = true

/-- **Adequacy.** A program `bcheck` accepts carries the kernel's three certificate shapes on
    `ucmdLang`: its budget is a `bound`, its mediation is a `trace`, and its noninterference,
    with addresses in the leakage, is a `rel`. These are the existing theorems (`bcheck_sound`,
    `jsecTy_sound`, `jsecTy_addrs`) read through the one observation. -/
theorem bcheck_lcore {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.bound (ucmdLang P π) k c
  ∧ LCore.Cert.trace (ucmdLang P π) (mediated π) c
  ∧ LCore.Cert.rel (ucmdLang P π) c := by
  have hf := bcheck_sound c [] [] A' V' k h
  refine ⟨?_, ?_, ?_⟩
  · intro n σ _
    show (uBeh _ _).cost ≤ k
    unfold uBeh
    split
    · rename_i r a hr _
      exact hf.bundle.budget n π (initU σ) r hr
    · exact Nat.zero_le k
  · intro n σ _ q hq
    have hq' : LCore.Ev.read q ∈ (uBeh (uexec n c π (initU σ)) (uaddrs n c π (initU σ))).ev := hq
    unfold uBeh at hq'
    split at hq'
    · rename_i r a hr _
      have hinv : UMedInv π [] (initU σ) := ⟨by simp [initU], by simp [initU], by simp⟩
      have hm := (hf.bundle.auth n π (initU σ) r hinv hr).2.1
      simp only [uEvents, List.mem_append, List.mem_map, List.mem_reverse] at hq'
      rcases hq' with ⟨q', hq'm, hq'e⟩ | ⟨t, _, ht⟩
      · injection hq'e with hqq; subst hqq; exact hm _ hq'm
      · cases ht
    · cases hq'
  · intro n σ σ' _ _ hσ
    have hlow := jsecTy_sound n c [] V' hf.joint π (initU σ) (initU σ')
      SepInv.initU SepInv.initU LabInv.initU LabInv.initU
      ⟨hσ, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    have haddr := jsecTy_addrs_initU hf.joint n π σ σ' hσ
    show uBeh _ _ = uBeh _ _
    rw [haddr]
    rcases e₁ : uexec n c π (initU σ) with _ | r <;> rcases e₁' : uexec n c π (initU σ') with _ | r'
    · rfl
    · rw [e₁, e₁'] at hlow; exact hlow.elim
    · rw [e₁, e₁'] at hlow; exact hlow.elim
    rw [e₁, e₁'] at hlow
    obtain ⟨⟨_, hrd, hdd, _, _, hsk, _, _, _⟩, hc, hb⟩ := hlow
    cases uaddrs n c π (initU σ') with
    | none => rfl
    | some a => simp only [uBeh, uEvents, hrd, hsk, hc, hb, hdd]


/-! ## Witnesses -/

/-- The repo's loop handler carries the kernel's three shapes: budget 40, mediated reads, and
    noninterference with addresses in the leakage. -/
theorem loopHandler_lcore (π : MedPolicy) :
    LCore.Cert.bound (ucmdLang Psec π) 40 loopHandler
  ∧ LCore.Cert.trace (ucmdLang Psec π) (mediated π) loopHandler
  ∧ LCore.Cert.rel (ucmdLang Psec π) loopHandler :=
  bcheck_lcore loopHandler_checks π

def σSecret0 : Store := fun _ => 0

/-- A program that branches on the secret. -/
def secretBranch : UCmd := .ite (.var "secret") .skip .skip

/-- **`rel` is not vacuous on `ucmdLang`**: inputs differing only in the secret give different
    observations for a secret branch (the branch bit is in the leakage). -/
theorem secretBranch_not_rel : ¬ LCore.Cert.rel (ucmdLang Psec (fun _ => true)) secretBranch := by
  intro h
  have hlow : lowEq Psec σSecret5 σSecret0 := by
    intro x hx
    simp only [σSecret5, σSecret0]
    have : (x == "secret") = false := hx
    simp [this]
  have := h 2 σSecret5 σSecret0 trivial trivial hlow
  revert this
  decide

end ConfTyping
