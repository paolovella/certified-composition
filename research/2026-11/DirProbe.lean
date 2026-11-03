import ConfTyping.SpecL

open ConfTyping ConfTyping.Spec ConfTyping.Split

/-! Scratch only. A directive machine: the attacker picks each branch. No window, no rollback. -/

inductive Dir where
  | correct
  | force (b : Bool)
  deriving Repr, DecidableEq

/-- The branch taken: the attacker's, or the real one. An empty stream predicts correctly. -/
def pick (ds : List Dir) (g : Bool) : Bool × List Dir :=
  match ds with
  | [] => (g, [])
  | .correct :: r => (g, r)
  | .force b :: r => (b, r)

/-- `urunS` with directives. The state thread needs the rest of the stream, so it is threaded too. -/
def urunD (π : MedPolicy) : Nat → List UFrame → List Dir → UState → List LCore.Lk
  | _, [], _, _ => []
  | 0, _ :: _, _, _ => []
  | n + 1, (c, p) :: k, ds, s =>
    if s.dead then [] else
    match c with
    | .seq a b => urunD π n (push a (p ++ [0]) (push b (p ++ [1]) k)) ds s
    | .ite e a b =>
        let g := decide (evalE e s.store ≠ 0)
        let (t, r) := pick ds g
        .branch t :: urunD π n (push (if t then a else b) (p ++ [if t then 0 else 1]) k) r s
    | .loop e b =>
        let g := decide (evalE e s.store ≠ 0)
        let (t, r) := pick ds g
        .branch t :: (if t then urunD π n (push b (p ++ [0]) ((.loop e b, p) :: k)) r s
                      else urunD π n k r s)
    | c =>
        let a := stepT c π s
        a.lk ++ (if a.out = .done then urunD π n k ds a.st else [])

def π₀ : MedPolicy := fun _ => true
def st (v : Int) : Store := fun x => if x == "s" then v else if x == "p" then 7 else 0

def run (c : UCmd) (ds : List Dir) (σ : Store) : List LCore.Lk :=
  urunD π₀ 200 (push c [] []) ds (initU σ)

/-- What the attacker sees, without step markers: `split` moves those, by a function of the source's. -/
def vis (l : List LCore.Lk) : List LCore.Lk :=
  l.filter fun | .step _ => false | _ => true

/-! ## Probe A: the second window probe. Past the cap the window model broke `det`. -/
def sumN : Nat → Expr
  | 0 => .num 1
  | n + 1 => .add (sumN n) (.num 1)

def ex2 (n : Nat) : UCmd :=
  .ite (.num 0)
    (.seq (.ite (.var "s") (.assign "x" (sumN n)) .skip) (.memop .deref "p"))
    .skip

/-- The attacker forces the outer branch and each choice of the inner one. For each: does the target
    agree across secrets whenever the source does, and is the target's view the source's? -/
def probeA (n : Nat) (inner : Dir) :=
  let ds := [Dir.force true, inner]
  let s1 := vis (run (ex2 n) ds (st 1)); let s0 := vis (run (ex2 n) ds (st 0))
  let t1 := vis (run (split (ex2 n)) ds (st 1)); let t0 := vis (run (split (ex2 n)) ds (st 0))
  (n, repr inner, s1 == s0, t1 == t0, s1 == t1, s0 == t0)

#eval [29, 30, 40].map fun n => [probeA n .correct, probeA n (.force true), probeA n (.force false)]

/-! ## Probe B: Spectector's Example 6 shape. A correct inner prediction reaches the leak; the fix I
    proposed (end the window at a nested branch) would not see it. -/
def ex6 : UCmd :=
  .ite (.num 0)
    (.seq (.ite (.num 1) .skip .skip) (.memop .deref "s"))
    .skip

#eval (vis (run ex6 [.force true, .correct] (st 1)), vis (run ex6 [.force true, .correct] (st 2)))

/-- The window machine today, on the same program. -/
def lkW (w : Nat) (c : UCmd) (σ : Store) : List Int :=
  (((ucmdLangW (fun x => x == "s") π₀ w).run 60 c σ).lk).filterMap fun | .addr a => some a | _ => none
#eval (List.range 4).map fun w => (w, lkW w ex6 (st 1), lkW w ex6 (st 2))

/-! ## Probe C: a program `bcheck` accepts, and the two refused ones, under every forced pair. -/
def dirs : List (List Dir) :=
  [[], [.force true], [.force false], [.force true, .force true], [.force true, .force false],
   [.force false, .force true], [.force false, .force false]]

def agree (c : UCmd) (σ σ' : Store) : List Bool :=
  dirs.map fun ds => vis (run c ds σ) == vis (run c ds σ')

def psec : Partition := fun x => x == "secret"
def lo : Store := fun x => if x == "secret" then 11 else 0
def hi : Store := fun x => if x == "secret" then 77 else 0

#eval (agree brWitness lo hi, agree (split brWitness) lo hi)
#eval (agree transientUse (st 1) (st 2), agree gadget (st 1) (st 2))
