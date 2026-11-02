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
  /-- A step boundary, with the program position of the instruction that ran (F4). Splits the
      leakage into per-step segments and says which instruction each is, so a compiler pass's
      target observation is a function of its source observation. For programs whose path is
      public (branch bits Low), it reveals nothing the branch bits did not. -/
  | step   (pc : List Nat)
  deriving DecidableEq, Repr

/-- **The observation.** All of it is visible to the attacker the certificates are against. -/
structure Beh where
  ev   : List Ev
  lk   : List Lk
  cost : Nat
  out  : Outcome
  deriving DecidableEq, Repr

/-- Which channel an event is on: its kind and name, without its payload. -/
inductive Chan where
  | check   (r : String)
  | read    (r : String)
  | emit    (sink : String)
  | release (tag : String)
  | ext     (name : String)
  deriving DecidableEq, Repr

def Ev.chan : Ev → Chan
  | .check r    => .check r
  | .read r     => .read r
  | .emit s _   => .emit s
  | .release t  => .release t
  | .ext n _    => .ext n

/-- **An observer**: the channels it reads. It chooses channels, never payloads, by its type, so
    two runs can disagree on which of a step's events it sees only if the step's channels differ. -/
abbrev Observer := Chan → Bool

/-- The observer that reads every channel. -/
def Observer.all : Observer := fun _ => true

/-- **What one observer sees of a run**: the events on its channels, and all of the leakage, cost
    and outcome. Side channels are not partitioned: they are shared hardware, so every observer
    sees them whole. -/
def Beh.view (f : Observer) (b : Beh) : Beh :=
  { b with ev := b.ev.filter (fun e => f e.chan) }

/-- Proved by induction, because the core library's `List.filter_true` uses `propext`, and the
    kernel uses no axioms. -/
theorem filter_all {α} : ∀ l : List α, l.filter (fun _ => true) = l
  | [] => rfl
  | x :: xs => congrArg (x :: ·) (filter_all xs)

/-- The observer that reads everything sees the whole observation. -/
theorem Beh.view_all (b : Beh) : b.view Observer.all = b := by
  cases b with
  | mk ev lk cost out => exact congrArg (fun e => Beh.mk e lk cost out) (filter_all ev)

end LCore
