/-
  The one observation (PLAN-2026-10 §2, `Obs.lean`). Ring 0.

  Every language L compiles through, every pass, and every certificate speaks about the same
  record: what happened (events), what an attacker can measure about how it happened (leakage),
  what it cost, and how it ended. Internal state, such as a heap, an allocator or a label map,
  is never observed. A certificate that needed it must say what it needed as an event or as
  leakage. S-OBS (`conf-typing/ConfTyping/AddrLeak.lean`) showed the riskiest such move, the
  addresses, is sound for the existing noninterference certificate.
-/
namespace LCore

/-- How a run ended. `fuel` means the fuel ran out.

    Correction of record (2026-10-29, F0). From 30f0720 this said the record then
    ~~is a prefix of a longer run~~. Nothing checked it (there is no fuel law), and
    `ucmdLang` gives an empty record. Fuel laws are item F2; guard (n). -/
inductive Outcome where
  | done
  | abort
  | fuel
  deriving DecidableEq, Repr

/-- The events certificates talk about. A string payload is its character codes. -/
inductive Ev where
  | check   (r : String)
  | read    (r : String)
  | emit    (sink : String) (data : List Nat)
  | release (tag : String)
  | ext     (name : String) (args : List Int)
  deriving DecidableEq, Repr

/-- What a side channel shows: branch directions, addresses, the operands of variable-time
    instructions, and named extensions. -/
inductive Lk where
  | branch (taken : Bool)
  | addr   (a : Int)
  | vtime  (v : Int)
  | ext    (name : String) (v : Int)
  deriving DecidableEq, Repr

/-- **The observation.** All of it is visible to the attacker the certificates are against. -/
structure Beh where
  ev   : List Ev
  lk   : List Lk
  cost : Nat
  out  : Outcome
  deriving DecidableEq, Repr

end LCore
