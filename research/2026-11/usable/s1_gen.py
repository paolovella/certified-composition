#!/usr/bin/env python3
"""S-USABLE S1: kernel cost against program size, on synthetic Slice2 programs.

Not part of any library. For each program it writes two Lean files under OUT:
  <name>_bytes.lean  prints the compiled image's bytes (run first; compiled code, not believed)
  <name>_kernel.lean states and proves, as CTBytes does, each with its own profiler line:
      ok      fits p = true ∧ okP (compile p) = true             by decide
      ct      ctCheck secX p = true                              by decide
      lit     code (genP (compile p)) = <literal>                by decide
      bytes   relView on the literal image, by relView_transfer  (term)
      counted Budget.counted p = true                            by decide   (loop shapes only)

Shapes, each at several sizes:
  line k    k assignments mixing ^ | & - over 4 secret inputs, through 8 temporaries
  loop k    forN 16 with a k-statement body of the same kind
  verify n  crypto_verify_16's shape on two n-byte arrays (n = 8, 16, 32, 64; 64 is loadB's mask cap)

Usage, from l-core/: python3 ../research/2026-11/usable/s1_gen.py OUT shape:size ...
"""
import sys
from pathlib import Path

OPS = ["xor", "or", "and", "sub"]


def stmt(j):
    """Statement j: t_{j%8} := (t_{(j+7)%8} op x_{j%4}) op' t_{(j+3)%8}."""
    a, b = OPS[j % 4], OPS[(j + 1) % 4]
    return (f'(.assign "t{j % 8}" (.bin .{b} (.bin .{a} (.var "t{(j + 7) % 8}") (.var "x{j % 4}")) '
            f'(.var "t{(j + 3) % 8}")))')


def seq(cmds):
    out = cmds[-1]
    for c in reversed(cmds[:-1]):
        out = f"(.seq {c}\n    {out})"
    return out


def init():
    return [f'(.assign "t{i}" (lit 0))' for i in range(8)]


def prog(shape, size):
    if shape == "line":
        body = seq(init() + [stmt(j) for j in range(size)])
        return '["x0", "x1", "x2", "x3"]', body, '.var "t0"'
    if shape == "loop":
        inner = seq([stmt(j) for j in range(size)])
        body = seq(init() + [f'(For.forN "c" (lit 16) {inner})'])
        return '["x0", "x1", "x2", "x3"]', body, '.var "t0"'
    if shape == "verify":
        w = size // 8
        xs = ", ".join(f'"x{i}"' for i in range(w))
        ys = ", ".join(f'"y{i}"' for i in range(w))
        inputs = "[" + ", ".join(f'"x{i}"' for i in range(w)) + ", " + ", ".join(f'"y{i}"' for i in range(w)) + "]"
        inner = seq([f'(.assign "i" (.bin .sub (lit {size}) (.var "c")))',
                     f'(.loadB "tx" [{xs}] (.var "i"))',
                     f'(.loadB "ty" [{ys}] (.var "i"))',
                     '(.assign "d" (.bin .or (.var "d") (.bin .xor (.var "tx") (.var "ty"))))'])
        body = seq(['(.assign "d" (lit 0))', f'(For.forN "c" (lit {size}) {inner})',
                    '(.assign "r" (tailE (.var "d")))'])
        return inputs, body, '.var "r"'
    raise SystemExit(f"unknown shape {shape}")


HEAD = """import LCore.Slice2.CTBytes
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler.threshold 0
open LCore LCore.Slice2 LCore.Slice2.Slots LCore.Slice2.Lower LCore.Slice2.Ops LCore.Slice.Rv
open LCore.Slice (W64)
"""


def secret(shape, size):
    # every input word is secret
    return 4 if shape in ("line", "loop") else 2 * (size // 8)


def main():
    out = Path(sys.argv[1])
    out.mkdir(parents=True, exist_ok=True)
    for spec in sys.argv[2:]:
        shape, size = spec.split(":")
        size = int(size)
        name = f"{shape}{size}"
        inputs, body, ret = prog(shape, size)
        nsec = secret(shape, size)
        pdef = (f"def P : Prog where\n  inputs := {inputs}\n  body := {body}\n  ret := {ret}\n\n"
                f"def S (k : Nat) : Bool := decide (k < {nsec})\n")
        (out / f"{name}_prog.lean").write_text(HEAD + pdef)
        (out / f"{name}_bytes.lean").write_text(
            HEAD + pdef + '\n#eval IO.println (toString (((code (genP (compile P))).map (·.val))))\n'
            '#eval IO.println s!"ok {fits P && okP (compile P)} ct {CT.ctCheck S P} fits {fits P} okP {okP (compile P)}"\n')
    print("wrote", out)


if __name__ == "__main__":
    main()
