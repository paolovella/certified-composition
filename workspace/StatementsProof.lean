/-
  The solution to `Statements.lean` (P0-03): each frozen statement, proved by the theorem it was
  copied from. `lake comparator` checks the two agree. This file holds no proof of its own, so a
  weakened source theorem fails here, at the citation.
-/
import ConfTyping
import TransportCalculus

namespace ConfTyping

theorem Frozen.allcheck_sound {P : Partition} : ∀ (c : UCmd) (A V A' V' : List String) (k : Nat),
    allcheck P A V c = some (A', V', k) → FullCert P A V c A' V' k := by
  first
  | exact ConfTyping.allcheck_sound
  | (apply ConfTyping.allcheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.bcheck_sound {P : Partition} : ∀ (c : UCmd) (A V A' V' : List String) (k : Nat),
    bcheck P A V c = some (A', V', k) → FullCert P A V c A' V' k := by
  first
  | exact ConfTyping.bcheck_sound
  | (apply ConfTyping.bcheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.costCheck_sound : ∀ (c : WCmd) (k : Nat), costCheck c = some k → CostAtMost c k := by
  first
  | exact ConfTyping.costCheck_sound
  | (apply ConfTyping.costCheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.hcheck_sound {P Q} :
    ∀ {pc : Bool} {c : HCmd}, hcheck P Q pc c = true → HSecTy P Q pc c := by
  first
  | exact ConfTyping.hcheck_sound
  | (apply ConfTyping.hcheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.jcheckW_sound {P : Partition} : ∀ (k : Nat) (c : UCmd) (V V' : List String),
    jcheckW P k V c = some V' → JSecTy P V c V' := by
  first
  | exact ConfTyping.jcheckW_sound
  | (apply ConfTyping.jcheckW_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.jcheck_sound {P : Partition} : ∀ (c : UCmd) (V V' : List String),
    jcheck P V c = some V' → JSecTy P V c V' := by
  first
  | exact ConfTyping.jcheck_sound
  | (apply ConfTyping.jcheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.medCheck_sound {p : List MedInstr} {A' : List String}
    (h : medCheck [] p = some A') : Mediated p := by
  first
  | exact ConfTyping.medCheck_sound
  | (apply ConfTyping.medCheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.pathCheck_sound (base : List Nat) (steps : List PStep)
    (h : pathCheck steps = true) : Contained base steps := by
  first
  | exact ConfTyping.pathCheck_sound
  | (apply ConfTyping.pathCheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.pcheckW_sound (fs : String) : ∀ (k : Nat) (c : UCmd) (C C' : TaintEnv),
    pcheckW fs k C c = some C' → PathCert fs C c C' := by
  first
  | exact ConfTyping.pcheckW_sound
  | (apply ConfTyping.pcheckW_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.pcheck_sound (fs : String) : ∀ (c : UCmd) (C C' : TaintEnv),
    pcheck fs C c = some C' → PathCert fs C c C' := by
  first
  | exact ConfTyping.pcheck_sound
  | (apply ConfTyping.pcheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.secCheckD_sound {P : Partition} {Δ : List Permit} :
    ∀ {c : Cmd} {pc : Bool}, secCheckD P Δ pc c = true → SecTyD P Δ pc c := by
  first
  | exact ConfTyping.secCheckD_sound
  | (apply ConfTyping.secCheckD_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.secCheckTD_sound {P : Partition} {Δ : List Permit} :
    ∀ {c : Cmd}, secCheckTD P Δ c = true → SecTyTD P Δ c := by
  first
  | exact ConfTyping.secCheckTD_sound
  | (apply ConfTyping.secCheckTD_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.secCheckT_sound {P : Partition} :
    ∀ {c : Cmd}, secCheckT P c = true → SecTyT P c := by
  first
  | exact ConfTyping.secCheckT_sound
  | (apply ConfTyping.secCheckT_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.secCheck_sound {P : Partition} :
    ∀ {c : Cmd} {pc : Bool}, secCheck P pc c = true → SecTy P pc c := by
  first
  | exact ConfTyping.secCheck_sound
  | (apply ConfTyping.secCheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.slcheck_sound : ∀ (c : UCmd) (V V' : List String),
    slcheck V c = some V' → SepCert V c V' := by
  first
  | exact ConfTyping.slcheck_sound
  | (apply ConfTyping.slcheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.specCheck_sound : ∀ (p : List SInstr) (sched : List Nat) (m : Mem) (ρ : SRegs),
    specCheck p = true → specExec sched p m ρ = archRun p m ρ := by
  first
  | exact ConfTyping.specCheck_sound
  | (apply ConfTyping.specCheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.tcheckW_sound : ∀ (k : Nat) (c : UCmd) (C C' : TaintEnv) (Ks : List Nat),
    tcheckW k C c = some (C', Ks) → TaintCert C c C' Ks := by
  first
  | exact ConfTyping.tcheckW_sound
  | (apply ConfTyping.tcheckW_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.tcheck_sound : ∀ (c : UCmd) (C C' : TaintEnv) (Ks : List Nat),
    tcheck C c = some (C', Ks) → TaintCert C c C' Ks := by
  first
  | exact ConfTyping.tcheck_sound
  | (apply ConfTyping.tcheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.ucheckNI_sound {P : Partition} :
    ∀ {c : UCmd}, ucheckNI P c = true → USecTy P c := by
  first
  | exact ConfTyping.ucheckNI_sound
  | (apply ConfTyping.ucheckNI_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.ucheck_sound : ∀ (c : UCmd) (A A' : List String) (k : Nat),
    ucheck A c = some (A', k) → UCert A c A' k := by
  first
  | exact ConfTyping.ucheck_sound
  | (apply ConfTyping.ucheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.umcheck_sound : ∀ (c : UCmd) (V V' : List String),
    umcheck V c = some V' → MemCert V c V' := by
  first
  | exact ConfTyping.umcheck_sound
  | (apply ConfTyping.umcheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.wcheck_sound {P : Partition} :
    ∀ {c : WCmd}, wcheck P c = true → WSecTy P c := by
  first
  | exact ConfTyping.wcheck_sound
  | (apply ConfTyping.wcheck_sound <;> assumption)

end ConfTyping

namespace ConfTyping

theorem Frozen.leakSafe_sound {c : UCmd} (h : leakSafe c = true) (π : MedPolicy) :
    LeakFree π c := by
  first
  | exact ConfTyping.leakSafe_sound
  | (apply ConfTyping.leakSafe_sound <;> assumption)

end ConfTyping

namespace ConfTyping.Src

theorem Frozen.source_certified {P : Partition} {src : String} {c : UCmd}
    {A V : List String} {k : Nat}
    (hp : parseSource src = some c) (hb : bcheck P [] [] c = some (A, V, k)) :
    (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        uexec n c π s = some r → r.2.1 ≤ k)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → ∀ q ∈ r.1.reads, π q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq P σ σ' →
        uOptLowEq P (uexec n c π (initU σ)) (uexec n c π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → r.1.err = false) := by
  first
  | exact ConfTyping.Src.source_certified
  | (apply ConfTyping.Src.source_certified <;> assumption)

end ConfTyping.Src

namespace TransportCalculus

theorem Frozen.Bridge.comp_cert {X M D : Type} {GA : GradedAction M D} {dist : X → X → D}
    (g f : Bridge X M D GA dist) :
    (g.comp f).cert = GA.mul g.cert f.cert := by
  first
  | exact TransportCalculus.Bridge.comp_cert
  | (apply TransportCalculus.Bridge.comp_cert <;> assumption)

end TransportCalculus

namespace ConfTyping

/-- **L's meaning for UCmd** (`ConfTyping.bcheck_lcoreT`, `conf-typing/ConfTyping/NiT.lean`;
    F2). A program `bcheck` accepts carries, on the lawful language `ucmdLangT`, its budget as a
    `bound`, its mediation and its memory safety as `trace`s, and its noninterference as a
    `rel`, over every run. Freezing it locks what "certified" means: the language, its run,
    the events and leakage, `mediated`, `faultEv`, and the kernel's certificate shapes, all
    through `ring0.lock`'s closure. `bcheck` is a checker, so it can still evolve. -/
theorem Frozen.bcheck_lcoreT_meaning {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.bound (ucmdLangT P π) k c
  ∧ LCore.Cert.trace (ucmdLangT P π) (mediated π) c
  ∧ LCore.Cert.trace (ucmdLangT P π) (fun evs => faultEv ∉ evs) c
  ∧ LCore.Cert.rel (ucmdLangT P π) c := 
  bcheck_lcoreT h π

/-- **The language is lawful** (`ConfTyping.ucmdLangT_lawful`, `conf-typing/ConfTyping/UTrace.lean`;
    F2): more fuel only extends a run, and a run that never finishes has unbounded cost, so
    the certificates above cannot hold vacuously. -/
theorem Frozen.ucmdLangT_lawful_meaning (P : Partition) (π : MedPolicy) :
    (ucmdLangT P π).Lawful := 
  ucmdLangT_lawful P π

end ConfTyping
