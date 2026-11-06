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

/-- **It wraps**, so it is not addition on unbounded integers. -/
theorem add_wraps : add (ofNat (2 ^ 64 - 1)) (ofNat 1) = ofNat 0 := by decide

end W64

end LCore.Slice
