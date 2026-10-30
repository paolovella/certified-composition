/-
  The frozen statements (P0-03, PLAN-2026-10 §2). Ring 0: changed only with the user's key.

  Each theorem here is the statement of a result the repo relies on, copied from its source and
  proved here by `sorry`. This file is the only place in the repo where `sorry` is allowed
  (CLAUDE.md, the user's decision of 2026-10-26). It is a *challenge*: `lake comparator`
  (`comparator.json`) checks that `StatementsProof` proves every one of these statements
  exactly, with no axiom beyond the standard three. Nothing may import this file; check-claims
  (k) enforces that, and that every `sorry` is the whole body of a `Frozen.` theorem.

  A statement can also be weakened by editing a definition it mentions. `tools/ring0.lock`
  hashes those too (`tools/ring0-lock.sh`).
-/
import ConfTyping
import TransportCalculus

namespace ConfTyping

/-- `ConfTyping.allcheck_sound` (`conf-typing/ConfTyping/FullCert.lean`). -/
theorem Frozen.allcheck_sound {P : Partition} : ∀ (c : UCmd) (A V A' V' : List String) (k : Nat),
    allcheck P A V c = some (A', V', k) → FullCert P A V c A' V' k := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.bcheck_sound` (`conf-typing/ConfTyping/CountedLoop.lean`). -/
theorem Frozen.bcheck_sound {P : Partition} : ∀ (c : UCmd) (A V A' V' : List String) (k : Nat),
    bcheck P A V c = some (A', V', k) → FullCert P A V c A' V' k := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.costCheck_sound` (`conf-typing/ConfTyping/CostBound.lean`). -/
theorem Frozen.costCheck_sound : ∀ (c : WCmd) (k : Nat), costCheck c = some k → CostAtMost c k := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.hcheck_sound` (`conf-typing/ConfTyping/HeapFlow.lean`). -/
theorem Frozen.hcheck_sound {P Q} :
    ∀ {pc : Bool} {c : HCmd}, hcheck P Q pc c = true → HSecTy P Q pc c := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.jcheckW_sound` (`conf-typing/ConfTyping/HeapWiden.lean`). -/
theorem Frozen.jcheckW_sound {P : Partition} : ∀ (k : Nat) (c : UCmd) (V V' : List String),
    jcheckW P k V c = some V' → JSecTy P V c V' := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.jcheck_sound` (`conf-typing/ConfTyping/HeapJoint.lean`). -/
theorem Frozen.jcheck_sound {P : Partition} : ∀ (c : UCmd) (V V' : List String),
    jcheck P V c = some V' → JSecTy P V c V' := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.medCheck_sound` (`conf-typing/ConfTyping/Mediation.lean`). -/
theorem Frozen.medCheck_sound {p : List MedInstr} {A' : List String}
    (h : medCheck [] p = some A') : Mediated p := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.pathCheck_sound` (`conf-typing/ConfTyping/PathTraversal.lean`). -/
theorem Frozen.pathCheck_sound (base : List Nat) (steps : List PStep)
    (h : pathCheck steps = true) : Contained base steps := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.pcheckW_sound` (`conf-typing/ConfTyping/StringLoop.lean`). -/
theorem Frozen.pcheckW_sound (fs : String) : ∀ (k : Nat) (c : UCmd) (C C' : TaintEnv),
    pcheckW fs k C c = some C' → PathCert fs C c C' := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.pcheck_sound` (`conf-typing/ConfTyping/PathCert.lean`). -/
theorem Frozen.pcheck_sound (fs : String) : ∀ (c : UCmd) (C C' : TaintEnv),
    pcheck fs C c = some C' → PathCert fs C c C' := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.secCheckD_sound` (`conf-typing/ConfTyping/SecTyD.lean`). -/
theorem Frozen.secCheckD_sound {P : Partition} {Δ : List Permit} :
    ∀ {c : Cmd} {pc : Bool}, secCheckD P Δ pc c = true → SecTyD P Δ pc c := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.secCheckTD_sound` (`conf-typing/ConfTyping/SecTyTD.lean`). -/
theorem Frozen.secCheckTD_sound {P : Partition} {Δ : List Permit} :
    ∀ {c : Cmd}, secCheckTD P Δ c = true → SecTyTD P Δ c := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.secCheckT_sound` (`conf-typing/ConfTyping/SecTyT.lean`). -/
theorem Frozen.secCheckT_sound {P : Partition} :
    ∀ {c : Cmd}, secCheckT P c = true → SecTyT P c := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.secCheck_sound` (`conf-typing/ConfTyping/SecTy.lean`). -/
theorem Frozen.secCheck_sound {P : Partition} :
    ∀ {c : Cmd} {pc : Bool}, secCheck P pc c = true → SecTy P pc c := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.slcheck_sound` (`conf-typing/ConfTyping/MemLinear.lean`). -/
theorem Frozen.slcheck_sound : ∀ (c : UCmd) (V V' : List String),
    slcheck V c = some V' → SepCert V c V' := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.specCheck_sound` (`conf-typing/ConfTyping/Speculate.lean`). -/
theorem Frozen.specCheck_sound : ∀ (p : List SInstr) (sched : List Nat) (m : Mem) (ρ : SRegs),
    specCheck p = true → specExec sched p m ρ = archRun p m ρ := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.tcheckW_sound` (`conf-typing/ConfTyping/StringLoop.lean`). -/
theorem Frozen.tcheckW_sound : ∀ (k : Nat) (c : UCmd) (C C' : TaintEnv) (Ks : List Nat),
    tcheckW k C c = some (C', Ks) → TaintCert C c C' Ks := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.tcheck_sound` (`conf-typing/ConfTyping/TaintCert.lean`). -/
theorem Frozen.tcheck_sound : ∀ (c : UCmd) (C C' : TaintEnv) (Ks : List Nat),
    tcheck C c = some (C', Ks) → TaintCert C c C' Ks := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.ucheckNI_sound` (`conf-typing/ConfTyping/UnifiedNI.lean`). -/
theorem Frozen.ucheckNI_sound {P : Partition} :
    ∀ {c : UCmd}, ucheckNI P c = true → USecTy P c := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.ucheck_sound` (`conf-typing/ConfTyping/Bundle.lean`). -/
theorem Frozen.ucheck_sound : ∀ (c : UCmd) (A A' : List String) (k : Nat),
    ucheck A c = some (A', k) → UCert A c A' k := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.umcheck_sound` (`conf-typing/ConfTyping/MemCert.lean`). -/
theorem Frozen.umcheck_sound : ∀ (c : UCmd) (V V' : List String),
    umcheck V c = some V' → MemCert V c V' := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.wcheck_sound` (`conf-typing/ConfTyping/WhileImp.lean`). -/
theorem Frozen.wcheck_sound {P : Partition} :
    ∀ {c : WCmd}, wcheck P c = true → WSecTy P c := sorry

end ConfTyping

namespace ConfTyping

/-- `ConfTyping.leakSafe_sound` (`conf-typing/ConfTyping/LeakCert.lean`). -/
theorem Frozen.leakSafe_sound {c : UCmd} (h : leakSafe c = true) (π : MedPolicy) :
    LeakFree π c := sorry

end ConfTyping

namespace ConfTyping.Src

/-- `ConfTyping.Src.source_certified` (`conf-typing/ConfTyping/Surface.lean`). -/
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
        uexec n c π (initU σ) = some r → r.1.err = false) := sorry

end ConfTyping.Src

namespace TransportCalculus

/-- `TransportCalculus.Bridge.comp_cert` (`transport-calculus/TransportCalculus.lean`). -/
theorem Frozen.Bridge.comp_cert {X M D : Type} {GA : GradedAction M D} {dist : X → X → D}
    (g f : Bridge X M D GA dist) :
    (g.comp f).cert = GA.mul g.cert f.cert := sorry

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
  ∧ LCore.Cert.rel (ucmdLangT P π) c := sorry

/-- **The language is lawful** (`ConfTyping.ucmdLangT_lawful`, `conf-typing/ConfTyping/UTrace.lean`;
    F2): more fuel only extends a run, and a run that never finishes has unbounded cost, so
    the certificates above cannot hold vacuously. -/
theorem Frozen.ucmdLangT_lawful_meaning (P : Partition) (π : MedPolicy) :
    (ucmdLangT P π).Lawful := sorry

end ConfTyping

namespace ConfTyping

/-- **L's meaning for UCmd on step fuel** (`ConfTyping.bcheck_lcoreS`,
    `conf-typing/ConfTyping/UStep.lean`; F4). The same four guarantees as on `ucmdLangT`, on the
    step-indexed language whose observation marks every step. Freezing it locks `urunS`,
    `push`, `stepMk` and `ucmdLangS` through `ring0.lock`'s closure. -/
theorem Frozen.bcheck_lcoreS_meaning {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.bound (ucmdLangS P π) k c
  ∧ LCore.Cert.trace (ucmdLangS P π) (mediated π) c
  ∧ LCore.Cert.trace (ucmdLangS P π) (fun evs => faultEv ∉ evs) c
  ∧ LCore.Cert.rel (ucmdLangS P π) c := sorry

/-- **The step-fuel language is lawful** (`ConfTyping.ucmdLangS_lawful`; F4). -/
theorem Frozen.ucmdLangS_lawful_meaning (P : Partition) (π : MedPolicy) :
    (ucmdLangS P π).Lawful := sorry

end ConfTyping
