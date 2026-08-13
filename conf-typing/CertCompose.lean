/-
  `certcompose` — the ledger combinator of stage D.

  Input: certificate files **emitted by Jasmin's SCT checker** (`pp_funty` output,
  as produced by `compiler/tests/sct-checker/accept.ml` and checked into that
  project as `accept.expected`). Output: the accumulated guarantee for a pair of
  functions and the trusted base it rests on.

  This is deliberately *not* `certcheck`. `certcheck` is a checker for this repo's
  own toy language and is frozen; this reads a foreign tool's output and composes
  it. The parsing and the accumulation law both live in
  `ConfTyping/JasminCert.lean`, where they are machine-checked on real bytes.

  Usage:
      certcompose <emission-file> [<emission-file>]
      certcompose <emission-file> --assembly     (charge compiler preservation)

  With one file, the first two certificates carrying a receivable level are
  composed. With two files, the first receivable certificate of each.
-/
import ConfTyping.JasminCert

open ConfTyping

/-- `List Char` back to something printable. -/
def show' (cs : List Char) : String := String.ofList cs

def showLvl : SLvl → String
  | ⟨.pub, .pub⟩ => "#public"
  | ⟨.pub, .sec⟩ => "#transient"
  | ⟨.sec, .sec⟩ => "#secret"
  | ⟨.sec, .pub⟩ => "#<H,L> (not a Jasmin level)"

/-- The certificates whose output level this model receives. -/
def received (cs : List JasminCert) : List JasminCert :=
  cs.filter (fun c => c.outLvl.isSome)

def summarise (name : String) (cs : List JasminCert) : IO Unit := do
  IO.println s!"{name}: {cs.length} certificates, {(received cs).length} with a receivable level"
  for c in cs do
    match c.outLvl with
    | some l => IO.println s!"    {show' c.fn} : -> {showLvl l}  (modmsf {c.modmsf})"
    | none   => IO.println s!"    {show' c.fn} : -> (polymorphic/compound - not received)"

def emit (a b : JasminCert) (asm : Bool) : IO Unit := do
  let comp := compose a b [] []
  IO.println ""
  IO.println "=== composite certificate ==="
  IO.println s!"  functions:  {show' a.fn} ; {show' b.fn}"
  match comp.lvl with
  | some l => IO.println s!"  SCT level:  {showLvl l}   (join of {showLvl (a.outLvl.getD SLvl.public)} and {showLvl (b.outLvl.getD SLvl.public)})"
  | none   => IO.println "  SCT level:  not received"
  IO.println s!"  msf killed: {comp.modmsf}   (disjunction)"
  IO.println ""
  IO.println "=== trusted base ==="
  for l in baseLabels asm do
    IO.println s!"  - {l}"
  IO.println ""
  IO.println "Accumulation law: ConfTyping.compose_lvl_is_sctLvlGA (join),"
  IO.println "                  ConfTyping.compose_modmsf (disjunction),"
  IO.println "                  ConfTyping.compose_ledger (union)."
  IO.println "Reception is a hand encoding, unchecked against the Jasmin checker."

def main (args : List String) : IO UInt32 := do
  let asm := args.contains "--assembly"
  let files := args.filter (fun a => a != "--assembly")
  match files with
  | [f] => do
      let cs := parseEmission (← IO.FS.readFile f)
      summarise f cs
      match received cs with
      | a :: b :: _ => emit a b asm; return 0
      | _ => IO.eprintln "certcompose: fewer than two receivable certificates"; return 2
  | [f, g] => do
      let cf := parseEmission (← IO.FS.readFile f)
      let cg := parseEmission (← IO.FS.readFile g)
      summarise f cf
      summarise g cg
      match received cf, received cg with
      | a :: _, b :: _ => emit a b asm; return 0
      | _, _ => IO.eprintln "certcompose: a file had no receivable certificate"; return 2
  | _ => do
      IO.eprintln "usage: certcompose <emission-file> [<emission-file>] [--assembly]"
      return 1
