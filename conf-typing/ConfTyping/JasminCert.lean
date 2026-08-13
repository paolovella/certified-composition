/-
  Stage D, first pass — consuming a certificate a real tool actually emitted.

  Stages B and C received CN's and Jasmin's guarantees by **hand encoding**: I read
  a spec, wrote down what it asserts, and took it as a hypothesis. Stage D's kill
  criterion is aimed exactly there — *if no external tool emits a machine-readable
  certificate we can consume (rather than prose in a paper), this reduces to a
  manual encoding exercise and should be scoped as such rather than sold as a
  pipeline.*

  So the first thing this stage owes is an **empirical answer**, not a design.
  `corpus/jasmin/EMISSION.md` records it for both tools, with evidence. In short:

  * **Jasmin: yes.** Its SCT checker prints, per function, the inferred signature —
    MSF-clobber flag, input type, output type, output corruption, constraints —
    and the project is confident enough in that text to diff against it in CI
    (`compiler/tests/sct-checker/accept.expected`). That is a statement of *what
    was established*, in a stable machine-readable form. This module parses it.
  * **CN: no.** Its JSON output is a **timing log** — its own reader
    (`tools/scan_cn_json.py`) is commented "for reading the JSON (ish) timing
    output" and "this next bit is a total hack". Its Coq export (`-pf`) emits proof
    *obligations* plus a supporting library, which is the opposite direction: work
    to be discharged, not a guarantee to be received. Success is an exit code and
    console prose.

  **So the kill criterion half-fires, and the honest scope is: a pipeline for one
  tool, a manual encoding exercise for the other.** That is written down rather
  than smoothed over, because "consumes certificates from real tools" would be a
  materially false description of the CN half.

  ── What is checked, and on what ──
  The parser runs on `List Char`, not `String`. That is not a style choice:
  `String.startsWith` and `String.splitOn` **do not reduce in the kernel**, so
  `decide` cannot see through them and every test over them would have to be
  `native_decide` — which this repo does not use anywhere, because it adds
  `Lean.ofReduceBool` to the axiom set. `String.toList` does reduce, so it is the
  boundary: `parseEmission` takes a `String` for the tool's benefit and converts
  once, and everything proved below is proved by kernel reduction on real bytes.

  `compose_lvl_is_sctLvlGA` ties the consumed artifact back to stage C: the level
  this combinator computes is exactly `sctLvlGA`'s `mul`.

  **Levels the model cannot receive are recorded, not guessed.** Jasmin's
  polymorphic (`#poly = { n = k, s = k}`) and compound (`#[ptr = …, val = …]`)
  types have no image in `SLvl`, so `outLvl` is `none` for them. Adapting them
  until they fit would be the corpus-rigging failure this repo already has a name
  for.
-/
import ConfTyping.JasminSCT

namespace ConfTyping

/-! ## Character-level helpers

Everything the parser needs, over `List Char` so that `decide` can reduce it. -/

/-- Does `hay` begin with `needle`? -/
def startsWithL : List Char → List Char → Bool
  | _,      []      => true
  | [],     _ :: _  => false
  | c :: cs, d :: ds => if c == d then startsWithL cs ds else false

/-- Split on a separator character, keeping empty fields. -/
def splitOnChar (sep : Char) : List Char → List (List Char)
  | []      => [[]]
  | c :: cs =>
      let rest := splitOnChar sep cs
      if c == sep then [] :: rest
      else match rest with
        | r :: rs => (c :: r) :: rs
        | []      => [[c]]

/-- Drop leading and trailing whitespace. -/
def trimL (l : List Char) : List Char :=
  let f := fun (x : List Char) => x.dropWhile Char.isWhitespace
  (f (f l).reverse).reverse

/-- The non-empty whitespace-separated tokens of a line. -/
def tokens (l : List Char) : List (List Char) :=
  (splitOnChar ' ' l).filter (fun t => !t.isEmpty)

/-! ## The emitted certificate

One entry of Jasmin's `pp_funty` output:

```
modmsf f : #transient ->
#secret
output corruption: #public
 constraints:
```
-/

/-- A certificate as Jasmin emits it, reduced to the parts that accumulate. -/
structure JasminCert where
  /-- The function's name, as printed. -/
  fn         : List Char
  /-- Whether the function clobbers the misspeculation flag. Jasmin prints this
      first because a caller must know it; it accumulates by **disjunction**. -/
  modmsf     : Bool
  /-- The output SCT level, when it is one of the three ground levels. `none`
      records a polymorphic or compound type this model does not receive. -/
  outLvl     : Option SLvl
  /-- The `output corruption` level. -/
  corruption : Option SLvl
deriving Repr, DecidableEq

/-- Jasmin's three ground level names, as printed. -/
def parseLvl (s : List Char) : Option SLvl :=
  let t := trimL s
  if t == "#public".toList then some SLvl.public
  else if t == "#transient".toList then some SLvl.transient
  else if t == "#secret".toList then some SLvl.secret
  else none

/-- A certificate entry begins with the MSF-clobber flag. -/
def headerFlag (l : List Char) : Option Bool :=
  if startsWithL l "nomodmsf ".toList then some false
  else if startsWithL l "modmsf ".toList then some true
  else none

/-- The function name is the second token of the header line. -/
def headerName (l : List Char) : Option (List Char) :=
  match tokens l with
  | _ :: name :: _ => some name
  | _              => none

/-- Walk forward to the `output corruption:` line, carrying the previous line.
    The output type is always the line immediately before it — input types may
    span several lines, and their continuations are indented. -/
def findOut : List Char → List (List Char) →
    Option (List Char × List Char × List (List Char))
  | _,    []        => none
  | prev, l :: rest =>
      if startsWithL l "output corruption:".toList then some (prev, l, rest)
      else findOut l rest

/-- Parse one entry, given its header line and the lines after it. -/
def parseEntry (hdr : List Char) (rest : List (List Char)) :
    Option (JasminCert × List (List Char)) :=
  match headerFlag hdr, headerName hdr, findOut hdr rest with
  | some flag, some name, some (outLine, corrLine, rest') =>
      let corrTok := (tokens corrLine).getLast?
      some ({ fn := name, modmsf := flag,
              outLvl := parseLvl outLine,
              corruption := corrTok.bind parseLvl }, rest')
  | _, _, _ => none

/-- Scan a whole emission. Fuel-indexed rather than well-founded, so that the
    measurements below stay `decide`-able — the same reason `bcheck` is. -/
def scanCerts : Nat → List (List Char) → List JasminCert
  | 0,   _         => []
  | _+1, []        => []
  | n+1, l :: rest =>
      match headerFlag l with
      | none   => scanCerts n rest
      | some _ =>
          match parseEntry l rest with
          | some (c, rest') => c :: scanCerts n rest'
          | none            => scanCerts n rest

/-- Parse an emission. `String.toList` is the boundary described in the header:
    it reduces, so everything downstream is checkable by `decide`. -/
def parseEmission (s : String) : List JasminCert :=
  let ls := splitOnChar '\n' s.toList
  scanCerts (ls.length + 1) ls

/-! ## Checked against the real bytes

Verbatim entries from `corpus/jasmin/accept.expected` — what the Jasmin SCT
checker printed, not what I would have written. -/

-- Kernel reduction over character lists is deep: each `decide` below walks the
-- whole sample one character at a time. The default depth is not enough, and
-- raising it is the price of not using `native_decide`.
set_option maxRecDepth 20000

/-- `annot.jazz`'s `f`, exactly as emitted. -/
def sample_f : String :=
  "modmsf f : #transient ->\n#secret\noutput corruption: #public\n constraints:\n"

/-- `annot.jazz`'s `id3` — the fully public identity. -/
def sample_id3 : String :=
  "nomodmsf id3 : #public ->\n#public\noutput corruption: #public\n constraints:\n"

/-- `annot.jazz`'s `id`, whose type is **polymorphic**. The model has no image for
    it, and it is recorded as such rather than adapted. -/
def sample_id : String :=
  "modmsf id : #poly = { n = k, s = k} ->\n#poly = { n = k, s = k}\noutput corruption: #public\n constraints:\nk <= k, \n"

/-- `arrays.jazz`'s `transient_read`, whose **input type spans two lines** — the
    case that makes "the output is the line before `output corruption:`" the rule
    rather than "the output is the second line". -/
def sample_multiline : String :=
  "modmsf transient_read : #[ptr = transient, val = { n = d, s = secret}] *\n                        #transient ->\n#poly = { n = d, s = secret}\noutput corruption: #public\n constraints:\n"

example : parseEmission sample_f =
    [{ fn := "f".toList, modmsf := true,
       outLvl := some SLvl.secret, corruption := some SLvl.public }] := by
  decide

example : parseEmission sample_id3 =
    [{ fn := "id3".toList, modmsf := false,
       outLvl := some SLvl.public, corruption := some SLvl.public }] := by
  decide

/-- The polymorphic entry parses, and its level is **not received**. -/
example : parseEmission sample_id =
    [{ fn := "id".toList, modmsf := true,
       outLvl := none, corruption := some SLvl.public }] := by
  decide

/-- The multi-line entry: the continuation line is not mistaken for the output. -/
example : parseEmission sample_multiline =
    [{ fn := "transient_read".toList, modmsf := true,
       outLvl := none, corruption := some SLvl.public }] := by
  decide

/-- Two entries in one emission are both found. -/
example : (parseEmission (sample_f ++ "\n\n" ++ sample_id3)).length = 2 := by
  decide

/-! ## Accumulation, tied back to stage C -/

/-- The composite of two consumed certificates. -/
structure Composite where
  fns    : List (List Char)
  modmsf : Bool
  lvl    : Option SLvl
  ledger : Ledger

/-- Compose two emitted certificates: levels **join**, the MSF-clobber flag
    **ors**, and the trusted bases append. -/
def compose (a b : JasminCert) (Γa Γb : Ledger) : Composite where
  fns    := [a.fn, b.fn]
  modmsf := a.modmsf || b.modmsf
  lvl    := match a.outLvl, b.outLvl with
            | some x, some y => some (SLvl.join x y)
            | _, _           => none
  ledger := Γa ++ Γb

/-- **The consumed certificate composes by the stage-C law.** The level this
    combinator computes on real emitted input is exactly `sctLvlGA.mul` — the
    parser feeds the algebra rather than sitting beside it. -/
theorem compose_lvl_is_sctLvlGA (a b : JasminCert) (x y : SLvl)
    (ha : a.outLvl = some x) (hb : b.outLvl = some y) (Γa Γb : Ledger) :
    (compose a b Γa Γb).lvl = some (sctLvlGA.mul x y) := by
  simp only [compose, ha, hb]
  rfl

/-- The trusted base of the composite is the union of the parts', by the same
    append `LedgerBridge` uses. -/
theorem compose_ledger (a b : JasminCert) (Γa Γb : Ledger) :
    (compose a b Γa Γb).ledger = Γa ++ Γb := rfl

/-- MSF clobbering accumulates by disjunction: a caller must assume the flag is
    dead if *either* callee killed it. -/
theorem compose_modmsf (a b : JasminCert) (Γa Γb : Ledger) :
    (compose a b Γa Γb).modmsf = (a.modmsf || b.modmsf) := rfl

/-- **End to end, on real bytes.** Two certificates Jasmin printed, parsed and
    composed: a `#secret` output joined with a `#public` one is `#secret`, and the
    MSF flag is dead because one of the two killed it. -/
example :
    ((parseEmission sample_f).head?.bind fun a =>
      (parseEmission sample_id3).head?.map fun b =>
        ((compose a b [] []).lvl, (compose a b [] []).modmsf))
      = some (some SLvl.secret, true) := by
  decide

/-! ## Jasmin's trusted base, computed

What an SCT verdict rests on. As in `CNReceive.lean` these are parameters, not
axioms: this module asserts none of them, it only tracks which a claim needs. -/

/-- The assumptions behind a Jasmin SCT result. -/
structure JasminTrust where
  /-- The SCT type system is sound (S&P 2023). -/
  typeSystem   : Prop
  /-- The speculative semantics models the hardware's misprediction behaviour. -/
  specSem      : Prop
  /-- SCT is preserved by compilation (POPL 2025) — needed **only** if the claim
      is about the compiled artifact rather than the Jasmin source. -/
  preservation : Prop

/-- The fixed base: everything, charged whether or not it is used. -/
def JasminTrust.fixedBase (T : JasminTrust) : Ledger :=
  [T.typeSystem, T.specSem, T.preservation]

/-- **The base read off the claim.** A source-level SCT statement does not depend
    on the compiler-preservation theorem; a statement about the emitted assembly
    does. -/
def JasminTrust.needs (T : JasminTrust) (aboutAssembly : Bool) : Ledger :=
  [T.typeSystem, T.specSem] ++ (if aboutAssembly then [T.preservation] else [])

/-- **The computed base is strictly smaller for a source-level claim** — witnessed
    in a world where the preservation theorem is false and the source-level
    guarantee stands anyway. The same shape as `cn_base_strictly_smaller`, for the
    other tool. -/
theorem jasmin_base_strictly_smaller :
    ∃ T : JasminTrust, Sat (T.needs false) ∧ ¬ Sat T.fixedBase := by
  refine ⟨{ typeSystem := True, specSem := True, preservation := False }, ?_, ?_⟩
  · simp [JasminTrust.needs, Sat]
  · rintro ⟨-, -, h, -⟩
    exact h

/-- And a claim about the assembly is charged for it. -/
theorem jasmin_assembly_charges_preservation (T : JasminTrust) :
    T.preservation ∈ T.needs true := by
  simp [JasminTrust.needs]

/-- The printable audit trail the tool emits for a base. A `Ledger` is `List Prop`
    and cannot be printed, so the tool prints these instead. -/
def baseLabels (aboutAssembly : Bool) : List String :=
  ["Jasmin SCT type system is sound (S&P 2023)",
   "the speculative semantics models the hardware's misprediction behaviour"]
  ++ (if aboutAssembly then ["SCT is preserved by compilation (POPL 2025)"] else [])

/-- **What is printed and what is proved agree.** The audit trail the tool emits
    has an entry for each assumption the computed ledger carries — so the
    human-readable output is not a separate, driftable story about the trusted
    base. -/
theorem baseLabels_length (T : JasminTrust) (b : Bool) :
    (baseLabels b).length = (T.needs b).length := by
  cases b <;> rfl

end ConfTyping
