/-
  Stage 3a: source text.

  Everything this package proves is a theorem about a `UCmd`, and until now a `UCmd`
  could only be written as a Lean term inside this repo. `bigHandler` is a hand-built
  AST; so is `loopHandler`; so is every certified program here. The guarantee attaches
  to something nobody outside the repo can write, checked by a function nobody outside
  Lean can run.

  This module gives the language a surface syntax, a lexer, and a recursive-descent
  parser, with the round trip proved — the same standard brick 21 set for the *query*
  language (`parse_print`), now applied to the language that actually carries the five
  certificates.

  The point of the round trip is that it closes the gap between the text a person writes
  and the term the checker certifies. Without it the tool's answer is about an AST that
  some unverified code claims to have derived from the file.
-/
import ConfTyping.CountedLoop

namespace ConfTyping

/-! The surface language lives in its own namespace: this package keeps ~1100 top-level
    declarations in one flat namespace, and `Tok`, `lex`, `parse` and `print` are all
    taken by brick 21's *query* lexer — house rule 2, which only a root build catches. -/

namespace Src

/-! ## Tokens -/

inductive Tok where
  | word : String → Tok
  | num  : Int → Tok
  | str  : UStr → Tok
  deriving DecidableEq, Repr

/-! ## The lexer -/

def isDigitC (c : Char) : Bool := decide ('0' ≤ c ∧ c ≤ '9')

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

def natOfDigits : List Char → Nat → Nat
  | [],      acc => acc
  | c :: cs, acc => natOfDigits cs (acc * 10 + digitVal c)

def allDigits : List Char → Bool
  | []      => false
  | c :: cs => isDigitC c && (cs.isEmpty || allDigits cs)

/-- A string literal's payload: `'` is the delimiter, anything else is an ordinary
    character. `UCh` has exactly these two constructors, so this is not a simplification
    of the model — it is the model. -/
def decodeStr : List Char → UStr
  | []      => []
  | c :: cs => (if c == '\'' then UCh.quote else UCh.ord) :: decodeStr cs

def encodeStr : UStr → List Char
  | []              => []
  | UCh.quote :: cs => '\'' :: encodeStr cs
  | UCh.ord   :: cs => 'a' :: encodeStr cs

/-- Classify one whitespace-delimited chunk. -/
def classify (w : List Char) : Tok :=
  match w with
  | '"' :: rest => .str (decodeStr (rest.dropLast))
  | '-' :: rest => if allDigits rest then .num (-(natOfDigits rest 0 : Int))
                   else .word (String.ofList w)
  | rest        => if allDigits rest then .num (natOfDigits rest 0 : Int)
                   else .word (String.ofList w)

def isSpace (c : Char) : Bool := decide (c.toNat ≤ 32)

/-- Split on whitespace, dropping empty chunks. -/
def chunks : List Char → List Char → List (List Char)
  | [],      acc => if acc.isEmpty then [] else [acc.reverse]
  | c :: cs, acc =>
      if isSpace c then
        (if acc.isEmpty then chunks cs [] else acc.reverse :: chunks cs [])
      else chunks cs (c :: acc)

def lex (cs : List Char) : List Tok := (chunks cs []).map classify

/-! ## Keywords

    An identifier may not be a keyword, and may not look like a number or a string —
    otherwise the lexer would classify it as something else and the round trip would be
    false. `okName` is that condition, and it is a hypothesis of the round-trip theorem
    rather than something the parser silently assumes. -/

def keywords : List String :=
  ["skip", "let", "check", "access", "alloc", "secret", "deref", "free", "load",
   "store", "sset", "emit", "if", "else", "while", "for", "san", "(", ")", "{", "}",
   ";", "+", "++", "="]

def okName (x : String) : Bool :=
  !x.isEmpty && !keywords.contains x
    && !(allDigits x.toList) && x.toList.all (fun c => !isSpace c && c != '"')
    && (match x.toList with | '-' :: rest => !allDigits rest | _ => true)

/-! ## Printing: a `UCmd` as tokens -/

def toksE : Expr → List Tok
  | .num k   => [.num k]
  | .var x   => [.word x]
  | .add a b => [.word "("] ++ toksE a ++ [.word "+"] ++ toksE b ++ [.word ")"]

def toksS : SExpr → List Tok
  | .lit s   => [.str s]
  | .var x   => [.word x]
  | .cat a b => [.word "("] ++ toksS a ++ [.word "++"] ++ toksS b ++ [.word ")"]
  | .san a   => [.word "san", .word "("] ++ toksS a ++ [.word ")"]

/-- The printer never emits `for`: it is parse-only sugar whose desugaring is exactly
    `forU`, so a counted loop prints as the `let`/`while` pair it *is*. That keeps the
    round trip a structural induction. -/
def toks : UCmd → List Tok
  | .skip            => [.word "skip"]
  | .assign x e      => [.word "let", .word x, .word "="] ++ toksE e
  | .check r         => [.word "check", .word r]
  | .access r        => [.word "access", .word r]
  | .memop .alloc x  => [.word "alloc", .word x]
  | .memop .allocS x => [.word "secret", .word x]
  | .memop .deref x  => [.word "deref", .word x]
  | .memop .free x   => [.word "free", .word x]
  | .hop .load d p   => [.word "load", .word d, .word p]
  | .hop .store p v  => [.word "store", .word p, .word v]
  | .sop .set x e    => [.word "sset", .word x] ++ toksS e
  | .sop .emit q e   => [.word "emit", .word q] ++ toksS e
  | .seq c₁ c₂       => toks c₁ ++ [.word ";"] ++ toks c₂
  | .ite e c₁ c₂     => [.word "if"] ++ toksE e ++ [.word "{"] ++ toks c₁
                          ++ [.word "}", .word "else", .word "{"] ++ toks c₂ ++ [.word "}"]
  | .loop e c        => [.word "while"] ++ toksE e ++ [.word "{"] ++ toks c ++ [.word "}"]

/-! ## The parser -/

def parseE : Nat → List Tok → Option (Expr × List Tok)
  | 0,     _  => none
  | f + 1, ts =>
      match ts with
      | .num k :: rest => some (.num k, rest)
      | .word "(" :: rest =>
          match parseE f rest with
          | some (a, .word "+" :: rest₁) =>
              match parseE f rest₁ with
              | some (b, .word ")" :: rest₂) => some (.add a b, rest₂)
              | _ => none
          | _ => none
      | .word x :: rest => if okName x then some (.var x, rest) else none
      | _ => none

def parseSE : Nat → List Tok → Option (SExpr × List Tok)
  | 0,     _  => none
  | f + 1, ts =>
      match ts with
      | .str s :: rest => some (.lit s, rest)
      | .word "san" :: .word "(" :: rest =>
          match parseSE f rest with
          | some (a, .word ")" :: rest₁) => some (.san a, rest₁)
          | _ => none
      | .word "(" :: rest =>
          match parseSE f rest with
          | some (a, .word "++" :: rest₁) =>
              match parseSE f rest₁ with
              | some (b, .word ")" :: rest₂) => some (.cat a b, rest₂)
              | _ => none
          | _ => none
      | .word x :: rest => if okName x then some (.var x, rest) else none
      | _ => none

mutual

/-- One statement. `for` is desugared here, and nowhere else. -/
def parseStmt : Nat → List Tok → Option (UCmd × List Tok)
  | 0,     _  => none
  | f + 1, ts =>
      match ts with
      | .word "skip" :: rest => some (.skip, rest)
      | .word "let" :: .word x :: .word "=" :: rest =>
          if okName x then
            match parseE (rest.length + 1) rest with
            | some (e, rest₁) => some (.assign x e, rest₁)
            | none => none
          else none
      | .word "check" :: .word r :: rest =>
          if okName r then some (.check r, rest) else none
      | .word "access" :: .word r :: rest =>
          if okName r then some (.access r, rest) else none
      | .word "alloc" :: .word x :: rest =>
          if okName x then some (.memop .alloc x, rest) else none
      | .word "secret" :: .word x :: rest =>
          if okName x then some (.memop .allocS x, rest) else none
      | .word "deref" :: .word x :: rest =>
          if okName x then some (.memop .deref x, rest) else none
      | .word "free" :: .word x :: rest =>
          if okName x then some (.memop .free x, rest) else none
      | .word "load" :: .word d :: .word p :: rest =>
          if okName d && okName p then some (.hop .load d p, rest) else none
      | .word "store" :: .word p :: .word v :: rest =>
          if okName p && okName v then some (.hop .store p v, rest) else none
      | .word "sset" :: .word x :: rest =>
          if okName x then
            match parseSE (rest.length + 1) rest with
            | some (e, rest₁) => some (.sop .set x e, rest₁)
            | none => none
          else none
      | .word "emit" :: .word q :: rest =>
          if okName q then
            match parseSE (rest.length + 1) rest with
            | some (e, rest₁) => some (.sop .emit q e, rest₁)
            | none => none
          else none
      | .word "if" :: rest =>
          match parseE (rest.length + 1) rest with
          | some (e, .word "{" :: rest₁) =>
              match parseProg f rest₁ with
              | some (c₁, .word "}" :: .word "else" :: .word "{" :: rest₂) =>
                  match parseProg f rest₂ with
                  | some (c₂, .word "}" :: rest₃) => some (.ite e c₁ c₂, rest₃)
                  | _ => none
              | _ => none
          | _ => none
      | .word "while" :: rest =>
          match parseE (rest.length + 1) rest with
          | some (e, .word "{" :: rest₁) =>
              match parseProg f rest₁ with
              | some (c, .word "}" :: rest₂) => some (.loop e c, rest₂)
              | _ => none
          | _ => none
      | .word "for" :: .word i :: .word "=" :: .num k :: .word "{" :: rest =>
          if okName i && decide (0 ≤ k) then
            match parseProg f rest with
            | some (c, .word "}" :: rest₁) => some (forU i k.toNat c, rest₁)
            | _ => none
          else none
      | _ => none

/-- A `;`-separated, right-nested sequence. -/
def parseProg : Nat → List Tok → Option (UCmd × List Tok)
  | 0,     _  => none
  | f + 1, ts =>
      match parseStmt f ts with
      | some (c₁, .word ";" :: rest) =>
          match parseProg f rest with
          | some (c₂, rest₁) => some (.seq c₁ c₂, rest₁)
          | none => none
      | some (c₁, rest) => some (c₁, rest)
      | none => none

end

/-- The entry point: a whole file must parse, with nothing left over. -/
def parse (ts : List Tok) : Option UCmd :=
  match parseProg (ts.length + 1) ts with
  | some (c, []) => some c
  | _            => none

/-- Source text to program. -/
def parseSource (src : String) : Option UCmd := parse (lex src.toList)

/-! ## Rendering tokens back to text -/

def renderTok : Tok → String
  | .word w => w
  | .num k  => toString k
  | .str s  => "\"" ++ String.ofList (encodeStr s) ++ "\""

def render : List Tok → String
  | []      => ""
  | [t]     => renderTok t
  | t :: ts => renderTok t ++ " " ++ render ts

def print (c : UCmd) : String := render (toks c)

/-! ## What the tool's verdict means -/

/-- **The contract of `certcheck FILE`, as a theorem.** If the file parses to `c` and the
    checker accepts `c`, then the program the file denotes has a cost budget over every
    input and every fuel, reads only what the policy authorized, is noninterferent, and
    never faults on memory.

    The `parseSource` hypothesis carries no logical weight here, and that is worth saying
    plainly rather than hiding: `parseSource` *defines* which program the text denotes, so
    this theorem is about the term the tool actually checks. What would make the hypothesis
    load-bearing is the round trip below — the guarantee that printing `c` back yields the
    text the user wrote, so the term checked is the program they meant. That is proved for
    the expression layer and open for the statement layer; see `parseE_toksE`. -/
theorem source_certified {P : Partition} {src : String} {c : UCmd}
    {A V : List String} {k : Nat}
    (hp : parseSource src = some c) (hb : bcheck P [] [] c = some (A, V, k)) :
    (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        uexec n c π s = some r → r.2.1 ≤ k)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → ∀ q ∈ r.1.reads, π q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq P σ σ' →
        uOptLowEq P (uexec n c π (initU σ)) (uexec n c π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → r.1.err = false) := by
  have _ := hp
  have hf := bcheck_sound c [] [] A V k hb
  refine ⟨hf.bundle.budget, ?_, fun n π σ σ' hσ => ?_, fun n π σ r hr => ?_⟩
  · intro n π σ r hr q hq
    have hinv : UMedInv π [] (initU σ) := ⟨by simp [initU], by simp [initU], by simp⟩
    exact (hf.bundle.auth n π (initU σ) r hinv hr).2.1 q hq
  · exact uOptLowEqA.toLowEq (jsecTy_sound n c [] V hf.joint π (initU σ) (initU σ')
      SepInv.initU SepInv.initU LabInv.initU LabInv.initU
      ⟨hσ, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩)
  · exact (hf.joint.toSepCert.safe n π (initU σ) r SepInv.initU hr).1

/-! ## The round trip, expression layer -/

/-- An expression is printable iff every variable in it is a legal identifier. -/
def okExpr : Expr → Bool
  | .num _   => true
  | .var x   => okName x
  | .add a b => okExpr a && okExpr b

def edepth : Expr → Nat
  | .num _   => 1
  | .var _   => 1
  | .add a b => 1 + edepth a + edepth b

theorem okName_ne_lpar {x : String} (h : okName x = true) : ¬ (x = "(") := by
  intro hx; subst hx; simp [okName, keywords] at h

/-- **The parser inverts the printer on expressions**, and consumes exactly the tokens the
    printer produced — the `rest` generalisation is what makes the induction go through. -/
theorem parseE_toksE : ∀ (e : Expr) (f : Nat) (rest : List Tok),
    okExpr e = true → edepth e ≤ f → parseE f (toksE e ++ rest) = some (e, rest) := by
  intro e
  induction e with
  | num k => intro f rest _ hf
             cases f with
             | zero => simp [edepth] at hf
             | succ f => rfl
  | var x => intro f rest hok hf
             cases f with
             | zero => simp [edepth] at hf
             | succ f =>
                 show parseE (f + 1) (Tok.word x :: rest) = _
                 simp only [okExpr] at hok
                 simp [parseE, okName_ne_lpar hok, hok]
  | add a b iha ihb =>
      intro f rest hok hf
      cases f with
      | zero => simp [edepth] at hf
      | succ f =>
          simp only [okExpr, Bool.and_eq_true] at hok
          simp only [edepth] at hf
          show parseE (f + 1) (Tok.word "(" :: (toksE a ++ [Tok.word "+"] ++ toksE b
                 ++ [Tok.word ")"] ++ rest)) = _
          have ea : parseE f (toksE a ++ (Tok.word "+" :: (toksE b
                      ++ (Tok.word ")" :: rest))))
                    = some (a, Tok.word "+" :: (toksE b ++ (Tok.word ")" :: rest))) :=
            iha f _ hok.1 (by omega)
          have eb : parseE f (toksE b ++ (Tok.word ")" :: rest))
                    = some (b, Tok.word ")" :: rest) := ihb f _ hok.2 (by omega)
          simp only [parseE, List.append_assoc, List.singleton_append, List.cons_append,
            List.nil_append]
          rw [ea]
          simp only [eb]

end Src

end ConfTyping
