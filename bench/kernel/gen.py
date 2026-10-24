#!/usr/bin/env python3
"""S-KERNEL: generate one Lean file per (case, task, mode) for timing kernel evaluation.

Imported by bench/kernel/run.py, which drives it.

Each generated file imports ConfTyping and proves exactly one equation about a program given as
source text, by `decide` (elaborator evaluates the Decidable instance, then the kernel re-checks
the proof) or by `decide +kernel` (the kernel alone). Neither adds an axiom; every file ends with
`#print axioms` so run.sh can check that. The expected right-hand sides come from probe.lean,
which run.sh evaluates first (with #eval, which is not trusted and only picks the RHS).
"""
import glob
import json
import os
import sys

HEAD = """import ConfTyping
open ConfTyping ConfTyping.Src
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

deriving instance Repr for ConfTyping.UCmd
namespace Bench
def P : Partition := fun x => ["pw", "scopy"].contains x
"""

# The P1 sketch (scratchpad compiler-sketch/Compile.lean), only what `compile` needs.
SKETCH = """
def slotOf : List String → String → Nat
  | [],      _ => 0
  | y :: ys, x => if y = x then 0 else slotOf ys x + 1
inductive TExpr where
  | num  : Int → TExpr
  | slot : Nat → TExpr
  | add  : TExpr → TExpr → TExpr
inductive TCmd where
  | skip   : TCmd
  | set    : Nat → TExpr → TCmd
  | seq    : TCmd → TCmd → TCmd
  | ite    : TExpr → TCmd → TCmd → TCmd
  | loop   : TExpr → TCmd → TCmd
  | check  : String → TCmd
  | access : String → TCmd
  | memop  : MemOp → Nat → TCmd
  | sop    : SOp → String → SExpr → TCmd
  | hop    : HOp → Nat → Nat → TCmd
def compileE (T : List String) : Expr → TExpr
  | .num n   => .num n
  | .var x   => .slot (slotOf T x)
  | .add a b => .add (compileE T a) (compileE T b)
def compile (T : List String) : UCmd → TCmd
  | .skip         => .skip
  | .assign x e   => .set (slotOf T x) (compileE T e)
  | .seq c₁ c₂    => .seq (compile T c₁) (compile T c₂)
  | .ite e c₁ c₂  => .ite (compileE T e) (compile T c₁) (compile T c₂)
  | .loop e c     => .loop (compileE T e) (compile T c)
  | .check r      => .check r
  | .access r     => .access r
  | .memop op x   => .memop op (slotOf T x)
  | .sop op x e   => .sop op x e
  | .hop op x y   => .hop op (slotOf T x) (slotOf T y)
def varsE : Expr → List String
  | .num _   => []
  | .var x   => [x]
  | .add a b => varsE a ++ varsE b
def uvars : UCmd → List String
  | .skip         => []
  | .assign x e   => x :: varsE e
  | .seq c₁ c₂    => uvars c₁ ++ uvars c₂
  | .ite e c₁ c₂  => varsE e ++ uvars c₁ ++ uvars c₂
  | .loop e c     => varsE e ++ uvars c
  | .check _      => []
  | .access _     => []
  | .memop _ x    => [x]
  | .sop _ _ _    => []
  | .hop _ x y    => [x, y]
/-- The target-side digest compared by the equation: forces the whole compiled tree,
    every slot number included. -/
def tdigE : TExpr → Nat
  | .num _   => 1
  | .slot i  => 2 + i
  | .add a b => 1 + tdigE a + tdigE b
def tdig : TCmd → Nat
  | .skip        => 1
  | .set i e     => 1 + i + tdigE e
  | .seq a b     => 1 + tdig a + tdig b
  | .ite e a b   => 1 + tdigE e + tdig a + tdig b
  | .loop e a    => 1 + tdigE e + tdig a
  | .check _     => 1
  | .access _    => 1
  | .memop _ i   => 1 + i
  | .sop _ _ _   => 1
  | .hop _ i j   => 1 + i + j
def usizeE : Expr → Nat
  | .num _ | .var _ => 1
  | .add a b => 1 + usizeE a + usizeE b
def usize : UCmd → Nat
  | .seq a b     => 1 + usize a + usize b
  | .ite e a b   => 1 + usizeE e + usize a + usize b
  | .loop e a    => 1 + usizeE e + usize a
  | .assign _ e  => 1 + usizeE e
  | _            => 1
"""

TASKS = {
    # from the source string (the T1 statement over text, before Wire exists)
    "parse":    ("(parseSource src).isSome", "Bool"),
    "bcheck":   ("((parseSource src).bind fun c => bcheck P [] [] c).map (fun r => r.2.2)", "Option Nat"),
    "compile":  ("(parseSource src).map fun c => tdig (compile (uvars c) c)", "Option Nat"),
    # from an elaborated UCmd term (what a Wire decoder, or a generated Artifact file, hands over)
    "elabT":    ("usize prog", "Nat"),
    "bcheckT":  ("(bcheck P [] [] prog).map (fun r => r.2.2)", "Option Nat"),
    "compileT": ("tdig (compile (uvars prog) prog)", "Nat"),
}
TERM_TASKS = ("elabT", "bcheckT", "compileT")


def lean_str(s):
    return json.dumps(s, ensure_ascii=False)


def body(i):
    # one handler: mediated read, a heap cell, a sanitized emission, the cell freed
    return (f"access db ; alloc t{i} ; store t{i} z ; let x{i} = ( x{i} + 1 ) ; "
            f"emit db ( \"'\" ++ ( san ( input ) ++ \"'\" ) ) ; free t{i}")


def scaled(n):
    return "check db ; " + " ; ".join(body(i) for i in range(n)) + " ; for k = 3 { access db }"


def cases():
    out = []
    for f in sorted(glob.glob("conf-typing/corpus/ext/b*.uc")) + sorted(glob.glob("conf-typing/corpus/p/*.uc")):
        name = f.split("corpus/")[1].replace("/", "_").replace(".uc", "")
        out.append((name, open(f).read().strip(), ["parse", "bcheck", "bcheckT"]))
    # text parsing is superlinear in the kernel (run 1), so the string tasks stop at 16 copies
    for n in (2, 4, 8, 16, 32, 64, 128, 256):
        tasks = (["parse", "bcheck", "compile"] if n <= 16 else []) + list(TERM_TASKS)
        out.append((f"scale{n:03d}", scaled(n), tasks))
    return out


def probe(outdir, cs):
    """Untrusted #eval picks each equation's right-hand side and the node count."""
    with open(os.path.join(outdir, "probe.lean"), "w") as f:
        f.write(HEAD + SKETCH)
        for name, src, tasks in cs:
            f.write(f"\ndef src_{name} : String := {lean_str(src)}\n")
            parts = [f"(reprStr ((parseSource src_{name}).map usize))",
                     f"(((parseSource src_{name}).map reprStr).getD \"none\" |>.replace \"\\n\" \" \")"]
            parts += [f"(reprStr (let src := src_{name}; ({TASKS[t][0]} : {TASKS[t][1]})))"
                      for t in tasks if t not in TERM_TASKS]
            f.write(f"#eval IO.println (\"PROBE\\t{name}\\t\" ++ " + " ++ \"\\t\" ++ ".join(parts) + ")\n")
        f.write("end Bench\n")


def emit(outdir, name, src, task, mode, rhs, term=None):
    expr, ty = TASKS[task]
    tac = "decide" if mode == "decide" else "decide +kernel"
    fn = os.path.join(outdir, f"{name}__{task}__{mode}.lean")
    with open(fn, "w") as f:
        f.write(HEAD + SKETCH)
        f.write(f"\ndef src : String := {lean_str(src)}\n")
        if term is not None:
            f.write(f"def prog : UCmd := {term}\n")
        f.write(f"theorem t : ({expr} : {ty}) = {rhs} := by {tac}\n")
        f.write("#print axioms t\nend Bench\n")
    return fn


def baseline(outdir):
    fn = os.path.join(outdir, "baseline.lean")
    with open(fn, "w") as f:
        f.write(HEAD + SKETCH + "end Bench\n")
    return fn
