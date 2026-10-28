import ConfTyping.AliasFix
import ConfTyping.AliasLoop
import ConfTyping.AllFive
import ConfTyping.CostBound
import ConfTyping.CountedLoop
import ConfTyping.DbInjection
import ConfTyping.HeapFlow
import ConfTyping.HeapWiden
import ConfTyping.LeakCert
import ConfTyping.MemCert
import ConfTyping.ParseSource
import ConfTyping.PathTraversal
import ConfTyping.Pleak
import ConfTyping.SecTyD
import ConfTyping.SecTyT
import ConfTyping.SpecFused
import ConfTyping.StringLoop
import ConfTyping.TaintCert
import ConfTyping.UnifiedNI
import ConfTyping.WhileImp

/-!
# The missing witnesses (P0-04)

Every checker needs a program it accepts and one it refuses: a refusal alone is satisfied by a
checker that refuses everything, an acceptance alone by one that accepts everything. The witness
registry (`WitnessRegistry.lean`) found 17 of the 37 checkers with only one side, or neither.
This file supplies the missing sides, each verdict by kernel `decide`. Where a checker already
had a witness, the new one reuses its arguments, so the pair differs only in the program.
-/

namespace ConfTyping

/-! ### Refused: the checkers that had only acceptances -/

/-- The fixed alias checker still refuses the use-after-free loop the first one refuses. -/
theorem alcheck2_refuses_uaf_loop : alcheck2 [] AliasUAFLoop = none := by
  -- `alcheck2` does not reduce under bare `decide`; unfolded as for `nested_checks`.
  simp only [AliasUAFLoop, alcheck2, loopFix2, copyImg, purge, preservedB, clsInB, sameElemsB,
    subOf, findMerge, mergeOne, collapse, Option.bind, List.length, List.any, List.all,
    List.filter, List.map, List.flatten]
  decide

/-- A dereference of a pointer nobody allocated. -/
theorem bcheck_refuses_wild_deref : bcheck Psec [] [] (.memop .deref "p") = none := by decide

/-- Emitting a tainted location: even the naive checker refuses this much. -/
theorem dbcheckNaive_refuses_tainted_emit :
    dbcheckNaive ([], []) (.seq (.input 0) (.emitC 0)) = none := by decide

theorem jcheckW_refuses_wild_deref : jcheckW Psec 10 [] (.memop .deref "p") = none := by decide

/-- The escaping literal `pcheck` refuses, through the loop-aware variant. -/
theorem pcheckW_refuses_escaping_literal :
    pcheckW "fs" 8 [] (.sop .emit "fs" (.lit [.ord, .quote, .quote])) = none := by decide

/-- The injectable query `tcheck` refuses, through the loop-aware variant. -/
theorem tcheckW_refuses_injection : tcheckW 12 [] vulnQuery = none := by decide

theorem xcheck_refuses_wild_deref : xcheck Psec [] [] [] (.memop .deref "p") = none := by decide

/-! ### Accepted: the checkers that had only refusals -/

theorem dbcheck_accepts_input : (dbcheck ([], []) (.input 0)).isSome = true := by decide

theorem hcheck_accepts_skip : hcheck Pall Qsecret false .skip = true := by decide

theorem pathCheck_accepts_down : pathCheck [.down 3] = true := by decide

theorem secCheckT_accepts_skip : secCheckT Phigh .skip = true := by decide

/-- `umcheck` has no rule for `free` (`free_has_no_rule`), so the accepted program allocates
    and dereferences. -/
theorem umcheck_accepts_alloc_deref :
    umcheck [] (.seq (.memop .alloc "p") (.memop .deref "p")) = some ["p"] := by decide

theorem wcheck_accepts_skip : wcheck Phigh .skip = true := by decide

/-! ### Both sides: the checkers that had neither -/

theorem costCheck_accepts_skip : (costCheck .skip).isSome = true := by decide

/-- A loop whose guard never changes has no bound. -/
theorem costCheck_refuses_unbounded_loop : costCheck (.loop (.num 1) .skip) = none := by decide

theorem jcheckList_accepts_empty : jcheckList Psec [] [] = some [] := by decide

theorem jcheckList_refuses_wild_deref : jcheckList Psec [] [.memop .deref "p"] = none := by decide

theorem lcheck_accepts_alloc_free :
    (lcheck [] (.seq (.memop .alloc "p") (.memop .free "p"))).isSome = true := by decide

/-- `lcheck` tracks what must still be freed; freeing what was never allocated is refused. -/
theorem lcheck_refuses_free_unallocated : lcheck [] (.memop .free "p") = none := by decide

theorem scheckA_accepts_const : (scheckA [] (.const 2)).isSome = true := by decide

/-- Emitting a location that holds untrusted input. -/
theorem scheckA_refuses_tainted_emit : scheckA [2] (.emit 2) = none := by decide

/-! ### Killing the P0-05 survivors

The mechanical mutants (`tools/mutants.py`) found three rules no theorem constrained: each could
refuse and every proof still went through. One accepting witness each kills them. -/

/-- `secCheckD` could refuse `skip`. -/
theorem secCheckD_accepts_skip : secCheckD Phigh [] false .skip = true := by decide

/-- `ucheckNI` could refuse `skip`. -/
theorem ucheckNI_accepts_skip : ucheckNI Psec .skip = true := by decide

/-- The naive database checker could refuse a parameterised emit. -/
theorem dbcheckNaive_accepts_emitP : (dbcheckNaive ([], []) (.emitP [] [] 0)).isSome = true := by
  decide

/-! ## EXPR-02: counted loops nest

    The pre-EXPR-02 `bcheck` refused every nested counted loop: its loop rule checked the body
    with `allcheck`, which has no loop rule. S-EXPR's blind programs 11 and 20 and the August
    corpus's 24 hit it. The body now goes to the fuelled checker itself. -/

/-- A loop inside a loop, allocating and freeing each turn, is accepted: budget 34. -/
theorem bcheck_accepts_nested_loops :
    bcheck Psec [] [] (forU "i" 2 (forU "j" 3 (.seq (.memop .alloc "t") (.memop .free "t"))))
      = some ([], [], 34) := by decide

/-- Nesting is not a hole: freeing one pointer on every inner turn is still a double free. -/
theorem bcheck_refuses_nested_double_free :
    bcheck Psec [] [] (.seq (.memop .alloc "p") (forU "i" 2 (forU "j" 2 (.memop .free "p"))))
      = none := by decide

/-- The fuelled checker's own pair. -/
theorem bcheckF_accepts_skip : (bcheckF Psec 1 [] [] .skip).isSome = true := by decide
theorem bcheckF_refuses_wild_deref : bcheckF Psec 4 [] [] (.memop .deref "p") = none := by decide

end ConfTyping
