/-
  VS-1: machine words, for the slice. Not Ring 0 yet: nothing in the kernel needs them
  (`research/2026-11/VS-1-KERNEL.md`). They move with the RV `Lang` if F6 locks it.
-/

namespace LCore.Slice

/-- A 64-bit word. -/
abbrev W64 := Fin (2 ^ 64)

namespace W64

def ofNat (n : Nat) : W64 := ⟨n % 2 ^ 64, Nat.mod_lt _ (Nat.two_pow_pos 64)⟩

/-- Wrapping addition, as RV64's `add`. -/
def add (a b : W64) : W64 := ofNat (a.val + b.val)

/-- Bitwise and, as RV64's `andi`. -/
def and (a b : W64) : W64 := ofNat (a.val &&& b.val)

/-- Wrapping subtraction, as RV64's `sub` (RC-01). -/
def sub (a b : W64) : W64 := ofNat (a.val + (2 ^ 64 - b.val))

/-- Bitwise exclusive or, as RV64's `xor` (RC-01). -/
def xor (a b : W64) : W64 := ofNat (a.val ^^^ b.val)

/-- Bitwise or, as RV64's `or` (RC-01). -/
def or (a b : W64) : W64 := ofNat (a.val ||| b.val)

/-- Logical shift right by `k`, as RV64's `srli` (RC-01). -/
def shr (a : W64) (k : Nat) : W64 := ofNat (a.val >>> k)

/-- **It wraps**, so it is not addition on unbounded integers. -/
theorem add_wraps : add (ofNat (2 ^ 64 - 1)) (ofNat 1) = ofNat 0 := by decide

end W64

/-- **The binary operators beyond `add`** (RC-01): what `crypto_verify_16` needs. -/
inductive Op where
  | sub | xor | or | and
  deriving DecidableEq, Repr

/-- An operator's meaning on words, the machine's. -/
def Op.w : Op → W64 → W64 → W64
  | .sub => W64.sub
  | .xor => W64.xor
  | .or => W64.or
  | .and => W64.and

end LCore.Slice
