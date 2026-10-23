/-
  The axiom manifest: every theorem of the two mathlib-free packages, with the exact set of
  axioms its proof depends on.

  Why it exists. The docs make about 235 claims of the form "`thm` is axiom-free /
  choice-free". Each was checked once, by hand, with `#print axioms`, when it was written, and
  never again. A proof that later picks up `Classical.choice` through a lemma it calls would
  keep its "choice-free" sentence forever. The manifest makes the footprint of every theorem a
  committed artifact (`tools/axioms.expected`) that CI regenerates and diffs. The doc claims are
  resolved against it by `tools/axiom-claims.py`.

  Run:  cd conf-typing && lake env lean AxiomManifest.lean
  Not part of the `ConfTyping` library; it only reads the environment.
-/
import ConfTyping
import Lean

open Lean Elab Command

/-- The modules whose theorems are audited: both mathlib-free packages. -/
def auditedRoots : List Name := [`ConfTyping, `TransportCalculus]

run_cmd do
  let env ← getEnv
  let inAudited (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | none => false
    | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        auditedRoots.any (·.isPrefixOf m)
  -- Lemmas the compiler generates for every inductive or definition (injectivity, `sizeOf`,
  -- equation lemmas) are not what any document makes claims about; leaving them out keeps the
  -- manifest to theorems somebody wrote.
  let generated (n : Name) : Bool :=
    match n with
    | .str _ s => s == "inj" || s == "injEq" || s == "sizeOf_spec" || s.startsWith "eq_"
                  || s.startsWith "match_" || s.startsWith "proof_" || s == "_sunfold"
    | _ => false
  let mut rows : Array String := #[]
  -- Theorems *and* definitions: "the checker `wcheck` is axiom-free" is a claim about a
  -- definition's term, and is checked the same way.
  let audited (ci : ConstantInfo) : Bool :=
    match ci with
    | .thmInfo _ | .defnInfo _ => true
    | _ => false
  for (n, ci) in env.constants.toList do
    if audited ci then
      if inAudited n && !n.isInternal && !generated n then
        let axs ← liftCoreM <| collectAxioms n
        let sorted := (axs.map toString).qsort (· < ·)
        -- the defining module, so claims about a whole module ("`X.lean`, choice-free") check
        let m := match env.getModuleIdxFor? n with
          | some idx => env.header.moduleNames[idx.toNat]!
          | none => Name.anonymous
        rows := rows.push s!"{n}\t{m}\t{",".intercalate sorted.toList}"
  for r in rows.qsort (· < ·) do
    IO.println r
