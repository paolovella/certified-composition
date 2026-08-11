/-
  The composable core, stage 1b: one language, and the embedding that makes the
  earlier bricks transfer rather than fork.

  The security program's structural weakness, measured: sixteen distinct instruction
  types across thirty modules, and **zero** cross-brick composition — not one module
  mentions two brick languages, and the only bridge in the repo is brick 7's
  `embed : Cmd → WCmd`. So thirty-five bricks each prove "for *my* toy language this
  class is excluded", and no program carries two guarantees at once. That undercuts
  the repo's own headline — composition *accumulates* certificates — exactly where
  the goal needs it.

  Stage 1a added the algebra (`GradedAction.prod`, `Bridge.pair_comp_cert`: bundles
  accumulate componentwise). This stage adds the object: **one language** carrying
  the three dimensions that the bricks treat separately —

  * store and control flow, so noninterference applies (bricks 3–10);
  * a **cost** counter, so budgets apply (brick 34);
  * **authorization**, so mediation applies (brick 35).

  `UCmd` is `WCmd` plus `check` and `access`. The state gains `auth`, `reads` and a
  `dead` flag: a refused check aborts, and after that every step is a no-op, which is
  what makes "nothing is read after a refusal" hold definitionally rather than by
  proof.

  The load-bearing theorem is **`uexec_embed_eq`**: on the image of `uembed`, the
  unified machine's store, cost and branch trace are *exactly* `wexec`'s, and `auth`,
  `reads` and `dead` are untouched. One equation, so the earlier While development is
  a fragment of this one rather than a parallel copy — the same standard brick 7 set
  with `wexec_embed_eq`, applied one level up. Two transfers follow immediately:
  `ucost_of_cost` (a brick-34 budget is a budget here) and `uembed_mediated` (a
  program with no `access` reads nothing, so it is mediated for free).

  Honest scope. This stage builds the object and the transfers; it does not yet
  re-derive the *checkers* on it — that is stage 1c, which retargets noninterference,
  cost and mediation onto `UCmd` and proves one program carrying all three composed
  certificates. Nothing here is claimed to supersede the existing bricks: they remain
  the record of what was proved, and the transfers are what make them reusable.
-/
import ConfTyping.CostBound
import ConfTyping.Mediation

namespace ConfTyping

/-! ## The language -/

/-- Heap operations, bundled into one constructor so that every downstream match —
    `uexec`, `ucheck`, `USecTy`, `deadCost`, and the aborted-run lemmas — gains a
    *single* new case rather than three. -/
inductive MemOp where
  | alloc | deref | free
  deriving Repr, DecidableEq

/-! ### Strings (stage 1o)

    A two-symbol alphabet: the **delimiter** that gives injection its power, and
    everything else. That is not a simplification of the problem — it is the problem.
    An injection succeeds by contributing a delimiter the query's author did not
    intend, so a `UCh` is exactly "is this character a delimiter or not", and the
    guarantee below is about how many of them reach the sink. Keeping the alphabet at
    two symbols also keeps every witness a `decide`. -/
inductive UCh where
  | quote   -- the delimiter
  | ord     -- any ordinary character
  deriving Repr, DecidableEq

abbrev UStr := List UCh

/-- How many delimiters a string carries. This is the quantity injection attacks. -/
def qcount : UStr → Nat
  | []            => 0
  | .quote :: cs  => 1 + qcount cs
  | .ord   :: cs  => qcount cs

/-- Sanitisation: drop the delimiters. The only discharge the analysis offers. -/
def sanStr : UStr → UStr
  | []            => []
  | .quote :: cs  => sanStr cs
  | .ord   :: cs  => .ord :: sanStr cs

theorem qcount_sanStr : ∀ (t : UStr), qcount (sanStr t) = 0
  | []           => rfl
  | .quote :: cs => qcount_sanStr cs
  | .ord   :: cs => by simpa [sanStr, qcount] using qcount_sanStr cs

theorem qcount_append : ∀ (t u : UStr), qcount (t ++ u) = qcount t + qcount u
  | [],           _ => by simp [qcount]
  | .quote :: cs, u => by simp [qcount, qcount_append cs u, Nat.add_assoc]
  | .ord   :: cs, u => by simp [qcount, qcount_append cs u]

/-- String expressions: literals, variables, concatenation, and sanitisation. -/
inductive SExpr where
  | lit : UStr → SExpr
  | var : String → SExpr
  | cat : SExpr → SExpr → SExpr
  | san : SExpr → SExpr
  deriving Repr

/-- String operations, bundled into one constructor for the same reason `MemOp` is:
    every downstream match gains one case rather than two. -/
inductive SOp where
  | set    -- assign to a string variable
  | emit   -- send to a sink (the injection point)
  deriving Repr, DecidableEq

/-- Is every string variable in this expression **Low**? Note that `san` does *not*
    declassify: sanitisation removes delimiters, not secrets, so a sanitised secret is
    still a secret. Getting that backwards would be a security bug, so it is worth
    saying out loud. -/
def sexprLow (P : Partition) : SExpr → Bool
  | .lit _   => true
  | .var x   => !P x
  | .cat a b => sexprLow P a && sexprLow P b
  | .san a   => sexprLow P a

/-- `WCmd` plus authorization plus a heap. Everything the earlier While bricks can say
    is still sayable, and three dimensions are added. -/
inductive UCmd where
  | skip   : UCmd
  | assign : String → Expr → UCmd
  | seq    : UCmd → UCmd → UCmd
  | ite    : Expr → UCmd → UCmd → UCmd
  | loop   : Expr → UCmd → UCmd
  | check  : String → UCmd        -- consult the policy; a refusal aborts
  | access : String → UCmd        -- the protected read
  | memop  : MemOp → String → UCmd -- allocate into / dereference / free the pointer in a variable
  | sop    : SOp → String → SExpr → UCmd -- set a string variable, or emit to a named sink

/-- The unified state: the store the While bricks use, plus what the mediation brick
    needs. `dead` records a refused check. -/
structure UState where
  store : Store
  auth  : List String
  reads : List String
  dead  : Bool
  heap  : Int → Int          -- addressed by the pointer values the store holds
  live  : List Int           -- currently-allocated addresses
  fresh : Int                -- next address to hand out
  err   : Bool               -- a memory fault happened (recorded, not conflated with `dead`)
  freed : List Int           -- addresses returned by `free`, available for reuse
  sstore : String → UStr      -- the string store, separate from the integer one
  sink  : List (String × UStr) -- everything emitted, with its destination, newest first

def initU (σ : Store) : UState :=
  ⟨σ, [], [], false, fun _ => 0, [], 0, false, [], fun _ => [], []⟩

/-- **The allocator reuses.** A freed address goes back on the free list and is handed
    out again before the counter advances. Real allocators do this, and it is what makes
    use-after-free *exploitable* rather than merely wrong: the address a stale pointer
    holds can belong to a live object again. -/
def pickAddr : List Int → Int → Int
  | [],     f => f
  | a :: _, _ => a

/-- The counter only advances when the free list was empty. -/
def bumpFresh : List Int → Int → Int
  | [],     f => f + 1
  | _ :: _, f => f

/-- Update in the string store. -/
def updSU (τ : String → UStr) (x : String) (v : UStr) : String → UStr :=
  fun y => if y = x then v else τ y

/-- Evaluating a string expression. `san` is the only way to lower a delimiter count,
    which is what makes the analysis below have exactly one discharge. -/
def evalS (τ : String → UStr) : SExpr → UStr
  | .lit t   => t
  | .var x   => τ x
  | .cat a b => evalS τ a ++ evalS τ b
  | .san a   => sanStr (evalS τ a)

/-- Membership and removal for the live-address list. Defined and proved locally —
    the package is mathlib-free, and guessing core lemma names has cost this project
    several build rounds. -/
def memInt (a : Int) : List Int → Bool
  | []      => false
  | x :: xs => (x == a) || memInt a xs

def dropInt (a : Int) : List Int → List Int
  | []      => []
  | x :: xs => if x == a then dropInt a xs else x :: dropInt a xs

theorem memInt_mem {a : Int} : ∀ {L : List Int}, memInt a L = true → a ∈ L
  | [],      h => by simp [memInt] at h
  | x :: xs, h => by
      simp only [memInt, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (memInt_mem h)

/-- The evaluator. Shaped to mirror `wexec` line for line, so the embedding theorem
    is a structural induction and not a translation. After a refusal every step is a
    no-op: the abort is definitional. -/
def uexec : Nat → UCmd → MedPolicy → UState → Option (UState × Nat × List Bool)
  | 0,     _,            _, _ => none
  | _ + 1, .skip,        _, s => some (s, 1, [])
  | _ + 1, .assign x e,  _, s =>
      some (if s.dead then s else { s with store := upd s.store x (evalE e s.store) }, 1, [])
  | _ + 1, .check r,     π, s =>
      some (if s.dead then s
            else if π r then { s with auth := r :: s.auth }
            else { s with dead := true }, 1, [])
  | _ + 1, .access r,    _, s =>
      some (if s.dead then s else { s with reads := r :: s.reads }, 1, [])
  | _ + 1, .memop op x,  _, s =>
      some (if s.dead then s else
              match op with
              | .alloc => { s with store := upd s.store x (pickAddr s.freed s.fresh),
                                   live := pickAddr s.freed s.fresh :: s.live,
                                   freed := dropInt (pickAddr s.freed s.fresh) s.freed,
                                   fresh := bumpFresh s.freed s.fresh }
              | .deref => if memInt (s.store x) s.live then s
                          else { s with dead := true, err := true }
              | .free  => if memInt (s.store x) s.live
                          then { s with live := dropInt (s.store x) s.live,
                                        freed := s.store x :: s.freed }
                          else { s with dead := true, err := true }, 1, [])
  | _ + 1, .sop op x e,  _, s =>
      some (if s.dead then s else
              match op with
              | .set  => { s with sstore := updSU s.sstore x (evalS s.sstore e) }
              | .emit => { s with sink := (x, evalS s.sstore e) :: s.sink }, 1, [])
  | n + 1, .seq c₁ c₂,   π, s =>
      (uexec n c₁ π s).bind fun r₁ =>
        (uexec n c₂ π r₁.1).map fun r₂ =>
          (r₂.1, r₁.2.1 + r₂.2.1, r₁.2.2 ++ r₂.2.2)
  | n + 1, .ite e c₁ c₂, π, s =>
      if evalE e s.store ≠ 0 then
        (uexec n c₁ π s).map fun r => (r.1, 1 + r.2.1, true :: r.2.2)
      else
        (uexec n c₂ π s).map fun r => (r.1, 1 + r.2.1, false :: r.2.2)
  | n + 1, .loop e c,    π, s =>
      if evalE e s.store ≠ 0 then
        (uexec n c π s).bind fun r₁ =>
          (uexec n (.loop e c) π r₁.1).map fun r₂ =>
            (r₂.1, 1 + r₁.2.1 + r₂.2.1, true :: (r₁.2.2 ++ r₂.2.2))
      else some (s, 1, [false])

/-- Low string variables determine the value of a Low expression. -/
theorem evalS_lowEq {P : Partition} {τ τ' : String → UStr}
    (h : ∀ x, P x = false → τ x = τ' x) :
    ∀ (e : SExpr), sexprLow P e = true → evalS τ e = evalS τ' e
  | .lit _,   _  => rfl
  | .var x,   he => by
      have : P x = false := by simpa [sexprLow] using he
      exact h x this
  | .cat a b, he => by
      simp only [sexprLow, Bool.and_eq_true] at he
      show evalS τ a ++ evalS τ b = evalS τ' a ++ evalS τ' b
      rw [evalS_lowEq h a he.1, evalS_lowEq h b he.2]
  | .san a,   he => by
      simp only [sexprLow] at he
      show sanStr (evalS τ a) = sanStr (evalS τ' a)
      rw [evalS_lowEq h a he]

theorem uexec_seq_eq (n : Nat) (c₁ c₂ : UCmd) (π : MedPolicy) (s : UState) :
    uexec (n+1) (.seq c₁ c₂) π s
      = (uexec n c₁ π s).bind fun r₁ =>
          (uexec n c₂ π r₁.1).map fun r₂ =>
            (r₂.1, r₁.2.1 + r₂.2.1, r₁.2.2 ++ r₂.2.2) := rfl

theorem uexec_ite_eq (n : Nat) (e : Expr) (c₁ c₂ : UCmd) (π : MedPolicy) (s : UState) :
    uexec (n+1) (.ite e c₁ c₂) π s
      = if evalE e s.store ≠ 0 then
          (uexec n c₁ π s).map fun r => (r.1, 1 + r.2.1, true :: r.2.2)
        else (uexec n c₂ π s).map fun r => (r.1, 1 + r.2.1, false :: r.2.2) := rfl

theorem uexec_loop_eq (n : Nat) (e : Expr) (c : UCmd) (π : MedPolicy) (s : UState) :
    uexec (n+1) (.loop e c) π s
      = if evalE e s.store ≠ 0 then
          (uexec n c π s).bind fun r₁ =>
            (uexec n (.loop e c) π r₁.1).map fun r₂ =>
              (r₂.1, 1 + r₁.2.1 + r₂.2.1, true :: (r₁.2.2 ++ r₂.2.2))
        else some (s, 1, [false]) := rfl

/-! ## The embedding -/

/-- The While language sits inside the unified one, structurally. -/
def uembed : WCmd → UCmd
  | .skip       => .skip
  | .assign x e => .assign x e
  | .seq a b    => .seq (uembed a) (uembed b)
  | .ite e a b  => .ite e (uembed a) (uembed b)
  | .loop e a   => .loop e (uembed a)

/-- **The model grew rather than forked.** On the image of `uembed`, started live, the
    unified machine's store, cost and branch trace are *exactly* `wexec`'s, and
    `auth`, `reads` and `dead` are untouched — one equation. Everything the While
    bricks proved therefore holds here, and nothing about the two new dimensions can
    be disturbed by an old program. -/
theorem uexec_embed_eq : ∀ (n : Nat) (c : WCmd) (π : MedPolicy) (s : UState),
    s.dead = false →
    uexec n (uembed c) π s
      = (wexec n c s.store).map (fun o => ({ s with store := o.1 }, o.2.1, o.2.2))
  | 0,     _, _, _, _ => rfl
  | n + 1, c, π, s, hd => by
      cases c with
      | skip =>
          simp only [uembed, uexec, wexec, Option.map_some]
      | assign x e =>
          simp only [uembed, uexec, wexec, Option.map_some, hd, Bool.false_eq_true,
                     if_false]
      | seq c₁ c₂ =>
          rw [uembed, uexec_seq_eq, wexec_seq_eq,
              uexec_embed_eq n c₁ π s hd]
          rcases h₁ : wexec n c₁ s.store with _ | o₁
          · simp
          · simp only [Option.map_some, Option.bind_some]
            have hd' : ({ s with store := o₁.1 } : UState).dead = false := hd
            rw [uexec_embed_eq n c₂ π { s with store := o₁.1 } hd']
            rcases h₂ : wexec n c₂ o₁.1 with _ | o₂
            · simp
            · simp
      | ite e c₁ c₂ =>
          rw [uembed, uexec_ite_eq, wexec_ite_eq]
          by_cases hg : evalE e s.store ≠ 0
          · rw [if_pos hg, if_pos hg, uexec_embed_eq n c₁ π s hd]
            rcases h₁ : wexec n c₁ s.store with _ | o₁ <;> simp
          · rw [if_neg hg, if_neg hg, uexec_embed_eq n c₂ π s hd]
            rcases h₁ : wexec n c₂ s.store with _ | o₁ <;> simp
      | loop e c₀ =>
          rw [uembed, uexec_loop_eq, wexec_loop_eq]
          by_cases hg : evalE e s.store ≠ 0
          · rw [if_pos hg, if_pos hg, uexec_embed_eq n c₀ π s hd]
            rcases h₁ : wexec n c₀ s.store with _ | o₁
            · simp
            · simp only [Option.map_some, Option.bind_some]
              have hd' : ({ s with store := o₁.1 } : UState).dead = false := hd
              have := uexec_embed_eq n (.loop e c₀) π { s with store := o₁.1 } hd'
              rw [uembed] at this
              rw [this]
              rcases h₂ : wexec n (.loop e c₀) o₁.1 with _ | o₂
              · simp
              · simp
          · rw [if_neg hg, if_neg hg]
            simp only [Option.map_some]

/-! ## What transfers -/

/-- A uniform cost budget on the unified machine, started live. -/
def UCostAtMost (c : UCmd) (k : Nat) : Prop :=
  ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    s.dead = false → uexec n c π s = some r → r.2.1 ≤ k

/-- Complete mediation on the unified machine: **started fresh** — nothing authorized,
    nothing read, live — every resource read is one the policy permits. Starting fresh
    rather than merely "live with no reads" is what makes the authorization invariant
    available: an arbitrary state could arrive with `auth` already holding resources
    the policy denies. -/
def UMediated (c : UCmd) : Prop :=
  ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
    uexec n c π (initU σ) = some r → ∀ x ∈ r.1.reads, π x = true

/-- **Brick 34's budgets transfer.** A `CostAtMost` proof about a While program is a
    budget for its image here — no reproof. -/
theorem ucost_of_cost {c : WCmd} {k : Nat} (h : CostAtMost c k) :
    UCostAtMost (uembed c) k := by
  intro n π s r hd hr
  rw [uexec_embed_eq n c π s hd] at hr
  rcases ho : wexec n c s.store with _ | o
  · rw [ho] at hr; simp at hr
  · rw [ho] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    subst hr
    exact h n s.store o ho

/-- **Old programs are mediated for free.** An embedded While program has no `access`,
    so it reads nothing, and mediation holds vacuously — the new dimension cannot be
    violated by code that predates it. -/
theorem uembed_mediated (c : WCmd) : UMediated (uembed c) := by
  intro n π σ r hr x hx
  rw [uexec_embed_eq n c π (initU σ) rfl] at hr
  rcases ho : wexec n c (initU σ).store with _ | o
  · rw [ho] at hr; simp at hr
  · rw [ho] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    subst hr
    exact absurd hx (by simp [initU])

/-! ## The new dimensions are live, not decorative -/

/-- A program that reads without checking: expressible here, and *not* mediated. -/
def uVictim : UCmd := .access "db"

/-- A program that checks first. -/
def uFixed : UCmd := .seq (.check "db") (.access "db")

theorem uVictim_not_mediated : ¬ UMediated uVictim := by
  intro h
  have := h 1 (fun _ => false) (fun _ => 0)
    ({ store := fun _ => 0, auth := [], reads := ["db"], dead := false,
       heap := fun _ => 0, live := [], fresh := 0, err := false, freed := [], sstore := fun _ => [], sink := []  }, 1, []) rfl
    "db" (by simp)
  exact absurd this (by simp)

/-- Under a refusing policy the fixed program aborts and reads nothing — the abort is
    definitional, not proved. -/
theorem uFixed_refused_reads_nothing :
    ((uexec 2 uFixed (fun _ => false) (initU (fun _ => 0))).map (fun r => r.1.reads))
      = some [] := by decide

/-- Under a permitting policy it reads, and the read is permitted. -/
theorem uFixed_permitted_reads :
    ((uexec 2 uFixed (fun _ => true) (initU (fun _ => 0))).map (fun r => r.1.reads))
      = some ["db"] := by decide

end ConfTyping
