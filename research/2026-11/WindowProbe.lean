import ConfTyping.SpecL

open ConfTyping ConfTyping.Spec ConfTyping.Split

def π₀ : MedPolicy := fun _ => true
def P₀ : Partition := fun x => x == "s"
def st (v : Int) : Store := fun x => if x == "s" then v else if x == "p" then 7 else 0

def lkOf (w : Nat) (c : UCmd) (σ : Store) : List LCore.Lk :=
  ((ucmdLangW P₀ π₀ w).run 60 c σ).lk

def addrs (l : List LCore.Lk) : List Int :=
  l.filterMap fun | .addr a => some a | _ => none

/-! ## Probe 1: my earlier example. Is the target's leakage a prefix of the source's at each window? -/
def ex1 : UCmd :=
  .ite (.num 0)
    (.seq (.assign "x" (.add (.add (.var "a") (.var "b")) (.var "c"))) (.memop .deref "s"))
    .skip

#eval (List.range 5).map fun w => (w, addrs (lkOf w ex1 (st 9)), addrs (lkOf w (split ex1) (st 9)))

/-! ## Probe 2: the inner fuel cap. A nested branch on the secret, whose split form needs more than
    uexec's 30 fuel on one path. -/
def sumN : Nat → Expr
  | 0 => .num 1
  | n + 1 => .add (sumN n) (.num 1)

def ex2 (n : Nat) : UCmd :=
  .ite (.num 0)
    (.seq (.ite (.var "s") (.assign "x" (sumN n)) .skip) (.memop .deref "p"))
    .skip

/-- Source and target leakage on the two secrets, at window 2. -/
def probe2 (n : Nat) :=
  (n, addrs (lkOf 2 (ex2 n) (st 1)), addrs (lkOf 2 (ex2 n) (st 0)),
      addrs (lkOf 2 (split (ex2 n)) (st 1)), addrs (lkOf 2 (split (ex2 n)) (st 0)))

#eval [5, 25, 28, 29, 30, 31, 35, 40].map probe2
