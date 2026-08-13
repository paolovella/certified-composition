/-
  The tool.

  `certcheck FILE` parses a source file into a `UCmd` and runs the certificate checker
  on it. What it prints on success is not a summary of an analysis: it is the certificate
  the Lean theorems consume. `bcheck_sound` turns the accepted result into `FullCert`,
  and `loopHandler_five` is the pattern for what that yields — a budget over every input
  and every fuel, mediated reads, noninterference, memory safety — while `tcheckW_sound`
  yields the structural-integrity bound on every emitted string.
-/
import ConfTyping

open ConfTyping ConfTyping.Src

def usage : String :=
  "usage: certcheck FILE [--secret name,name,...]\n\
   \n\
   exit 0  accepted, certificate printed\n\
   exit 1  usage error\n\
   exit 2  the file does not parse\n\
   exit 3  rejected by the checker"

/-- The confidentiality partition: the names given on the command line are High. -/
def partitionOf (names : List String) : Partition := fun x => names.contains x

def splitCommas (s : String) : List String :=
  (s.splitOn ",").filter (fun w => !w.isEmpty)

def parseArgs : List String → Option (String × List String)
  | [path]                            => some (path, [])
  | [path, "--secret", names]         => some (path, splitCommas names)
  | _                                 => none

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | none => IO.eprintln usage; return 1
  | some (path, secrets) =>
      let src ← IO.FS.readFile path
      match parseSource src with
      | none =>
          IO.eprintln s!"{path}: parse error"
          return 2
      | some c =>
          let P := partitionOf secrets
          match bcheck P [] [] c, tcheckW 64 [] c with
          | some (auth, tracked, budget), some (_, counts) =>
              IO.println s!"{path}: ACCEPTED"
              IO.println ""
              IO.println s!"  cost budget          {budget}   (over every input and every fuel)"
              IO.println s!"  requires authority   {auth}"
              IO.println s!"  pointers still held  {tracked}"
              IO.println s!"  emitted delimiters   {counts}"
              IO.println s!"  secret variables     {secrets}"
              IO.println ""
              IO.println "  certified: bounded cost, mediated reads, noninterference,"
              IO.println "             memory safety, injection-free emission."
              return 0
          | none, _ =>
              IO.eprintln s!"{path}: REJECTED by the certificate checker"
              IO.eprintln "  (budget / mediation / flow / memory safety)"
              return 3
          | _, none =>
              IO.eprintln s!"{path}: REJECTED by the string-integrity checker"
              return 3
