/-
  RC-01 step 5: the front end. A subset of C, read into L, by functions the kernel evaluates.

  The reading is `RC-01-READING` §3 and §5, as code. It is a **trust assumption**, believed only by testing against clang (step 6), and it says
  no rather than guessing: every stage returns `none` on anything outside the subset.

  1. `lex`: characters to tokens. Hex and suffixes other than `U` are refused.
  2. `pFuns`: a recursive-descent parser, into a small syntax tree: functions, declarations, the counted `for`, `|=`, `return`, and the
     operators `| ^ & >> + -` with C's precedence, array reads, casts, and calls with plain arguments.
  3. `readC`: the entry function must be `return g(args);` for a `static inline` `g` in the same text, which is read by substitution. Then:
     - a `const unsigned char *` parameter of the stated length is a byte array, named by the entry's parameter, and a local pointer
       initialised from one, through a qualifier-only cast, is the same array;
     - `uint_fast16_t`, `unsigned long` and `uint64_t` locals are words; an `int` local only as a loop index;
     - `for (i = 0; i < N; i++)` with `N` a literal under `2^31` is `forN` with `i := N - c`, and nothing in the body writes `i`;
     - each array read is hoisted into a temporary `t` plus the array's name, at most one read per array per statement, at the loop index
       with `N` at most the length, or at an index `e & m` with `m` under the length;
     - `return e` is `r := e`, returning `r`.
     Names the reading makes (`c`, `r`, `t…`, and the array words `x0 x1 …`) cannot be a C local's name: locals with a digit, starting with
     `t`, or named `c` or `r` are refused.

  **What this is not:** a C compiler. The preprocessor is not run (the branch and the defines are stated, `RC-01-READING` §1), and the
  subset is one function's worth.
-/
import LCore.Slice2.CT
import LCore.Slice2.CSrc

namespace LCore.Slice2.CFront

open Slice (W64 Expr Op)
open Ops (lit)

/-! ## Tokens -/

inductive P where
  | lp | rp | lb | rb | lc | rc | semi | comma | star | eq | orEq | caret | amp | bar | minus | plus | lt | inc | shr
  /-- `+=` and `>>=` (RC-02), each one token, so `+ =` is not read as `+=`. -/
  | plusEq | shrEq
  /-- Lexed, so that the text is read, and read by no rule: `/ ! > # % != ==`. -/
  | other
  deriving DecidableEq

inductive Tok where
  | id  : List Nat → Tok
  | num : Nat → Tok
  | sym : P → Tok
  deriving DecidableEq

def isAlpha (c : Nat) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def isIdc (c : Nat) : Bool := isAlpha c || isDigit c
def isSpace (c : Nat) : Bool := c == 32 || c == 10 || c == 9 || c == 13

def sym1 (c : Nat) : Option P :=
  if c == 40 then some .lp else if c == 41 then some .rp else if c == 91 then some .lb else if c == 93 then some .rb
  else if c == 123 then some .lc else if c == 125 then some .rc else if c == 59 then some .semi else if c == 44 then some .comma
  else if c == 42 then some .star else if c == 61 then some .eq else if c == 94 then some .caret else if c == 38 then some .amp
  else if c == 124 then some .bar else if c == 45 then some .minus else if c == 43 then some .plus else if c == 60 then some .lt
  else if c == 47 || c == 33 || c == 62 || c == 35 || c == 37 then some .other
  else none

def sym2 (c d : Nat) : Option P :=
  if c == 124 && d == 61 then some .orEq else if c == 43 && d == 43 then some .inc else if c == 43 && d == 61 then some .plusEq
  else if c == 62 && d == 62 then some .shr
  else if (c == 33 || c == 61) && d == 61 then some .other else none

def spanW (p : Nat → Bool) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | c :: r => if p c then ((c :: (spanW p r).1), (spanW p r).2) else ([], c :: r)

def digits : List Nat → Nat → Nat
  | [], n => n
  | d :: r, n => digits r (10 * n + (d - 48))

/-- An optional `U` or `u` suffix. -/
def dropU : List Nat → List Nat
  | 85 :: t => t
  | 117 :: t => t
  | t => t

def startsIdc : List Nat → Bool
  | c :: _ => isIdc c
  | [] => false

def lexF : Nat → List Nat → Option (List Tok)
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, c :: r =>
    if isSpace c then lexF f r
    else if isAlpha c then
      (lexF f (spanW isIdc (c :: r)).2).map (Tok.id (spanW isIdc (c :: r)).1 :: ·)
    else if isDigit c then
      if startsIdc (dropU (spanW isDigit (c :: r)).2) then none
      else (lexF f (dropU (spanW isDigit (c :: r)).2)).map (Tok.num (digits (spanW isDigit (c :: r)).1 0) :: ·)
    else match r with
      | d :: e :: r'' =>
        if c == 62 && d == 62 && e == 61 then (lexF f r'').map (Tok.sym .shrEq :: ·)
        else match sym2 c d with
          | some p => (lexF f (e :: r'')).map (Tok.sym p :: ·)
          | none => (sym1 c).bind fun p => (lexF f r).map (Tok.sym p :: ·)
      | d :: r' => match sym2 c d with
        | some p => (lexF f r').map (Tok.sym p :: ·)
        | none => (sym1 c).bind fun p => (lexF f r).map (Tok.sym p :: ·)
      | [] => (sym1 c).bind fun p => (lexF f r).map (Tok.sym p :: ·)

def lex (cs : List Nat) : Option (List Tok) := lexF (cs.length + 1) cs

/-! ## Keywords, as codes -/

def kw (s : List Char) : List Nat := s.map Char.toNat

def kConst := kw ['c','o','n','s','t']
def kVolatile := kw ['v','o','l','a','t','i','l','e']
def kStatic := kw ['s','t','a','t','i','c']
def kInline := kw ['i','n','l','i','n','e']
def kUnsigned := kw ['u','n','s','i','g','n','e','d']
def kChar := kw ['c','h','a','r']
def kInt := kw ['i','n','t']
def kLong := kw ['l','o','n','g']
def kFast16 := kw ['u','i','n','t','_','f','a','s','t','1','6','_','t']
def kU64 := kw ['u','i','n','t','6','4','_','t']
def kReturn := kw ['r','e','t','u','r','n']
def kFor := kw ['f','o','r']
def kSizeT := kw ['s','i','z','e','_','t']
def kVoid := kw ['v','o','i','d']

def isQual (w : List Nat) : Bool := w == kConst || w == kVolatile
def isTyWord (w : List Nat) : Bool :=
  isQual w || w == kUnsigned || w == kChar || w == kInt || w == kLong || w == kFast16 || w == kU64 || w == kSizeT

/-! ## The syntax tree -/

inductive Ty where
  | ptr | word | int
  /-- RC-02: a pointer to `unsigned char` without `const`, an array the function writes; and `unsigned char` itself, for a cast. -/
  | wptr | byte
  deriving DecidableEq

inductive COp where
  | or | xor | and | shr | add | sub
  deriving DecidableEq

inductive CArg where
  | v : List Nat → CArg
  | n : Nat → CArg

inductive CE where
  | num  : Nat → CE
  | var  : List Nat → CE
  | idx  : List Nat → CE → CE
  | bin  : COp → CE → CE → CE
  | cast : Ty → CE → CE
  | call : List Nat → List CArg → CE

inductive CS where
  | decl : Ty → List Nat → Option CE → CS
  | forN : List Nat → Nat → List Nat → CE → List Nat → List CS → CS
  | orEq : List Nat → CE → CS
  | ret  : CE → CS
  /-- RC-02: `x += e`, `x >>= k`, `a[e] = e'`. -/
  | addEq : List Nat → CE → CS
  | shrEq : List Nat → Nat → CS
  | store : List Nat → CE → CE → CS

structure CFun where
  inline : Bool
  name   : List Nat
  params : List (Ty × List Nat)
  body   : List CS
  /-- RC-02: a `void` function, which returns no value. -/
  isVoid : Bool

/-! ## The parser -/

/-- The words of a type, without qualifiers, and its stars. -/
def takeTy : List Tok → List (List Nat) × Nat × List Tok
  | .id w :: r =>
    if isTyWord w then
      (if isQual w then (takeTy r).1 else w :: (takeTy r).1, (takeTy r).2.1, (takeTy r).2.2)
    else ([], 0, .id w :: r)
  | .sym .star :: r => ((takeTy r).1, (takeTy r).2.1 + 1, (takeTy r).2.2)
  | r => ([], 0, r)

/-- Whether a type's words, before its name, include `const`. -/
def constIn : List Tok → Bool
  | .id w :: r => if w == kConst then true else if isTyWord w then constIn r else false
  | .sym .star :: r => constIn r
  | _ => false

/-- A type, from its words without qualifiers, its stars, and whether `const` was among them: a pointer to `unsigned char` is read-only
    with `const` and written without it (RC-02). -/
def classify (ws : List (List Nat)) (stars : Nat) (cst : Bool) : Option Ty :=
  if stars == 1 && ws == [kUnsigned, kChar] then some (if cst then .ptr else .wptr)
  else if stars == 0 && (ws == [kFast16] || ws == [kUnsigned, kLong] || ws == [kU64] || ws == [kSizeT]) then some .word
  else if stars == 0 && ws == [kInt] then some .int
  else if stars == 0 && ws == [kUnsigned, kChar] then some .byte
  else none

/-- C's binary operators by level, loosest first: `|`, `^`, `&`, `>>`, `+ -`. -/
def opAt (lvl : Nat) (t : Tok) : Option COp :=
  match t with
  | .sym .bar => if lvl == 0 then some .or else none
  | .sym .caret => if lvl == 1 then some .xor else none
  | .sym .amp => if lvl == 2 then some .and else none
  | .sym .shr => if lvl == 3 then some .shr else none
  | .sym .plus => if lvl == 4 then some .add else none
  | .sym .minus => if lvl == 4 then some .sub else none
  | _ => none

def pArgs : List Tok → Option (List CArg × List Tok)
  | .id x :: .sym .comma :: r => (pArgs r).map fun q => (.v x :: q.1, q.2)
  | .num k :: .sym .comma :: r => (pArgs r).map fun q => (.n k :: q.1, q.2)
  | .id x :: .sym .rp :: r => some ([.v x], r)
  | .num k :: .sym .rp :: r => some ([.n k], r)
  | _ => none

def closing (p : P) : List Tok → Option (List Tok)
  | .sym q :: r => if q == p then some r else none
  | _ => none

mutual
/-- An expression at level `lvl`; level 5 is a primary. -/
def pE : Nat → Nat → List Tok → Option (CE × List Tok)
  | 0, _, _ => none
  | f + 1, lvl, ts =>
    if lvl < 5 then (pE f (lvl + 1) ts).bind fun q => pL f lvl q.1 q.2 else pP f ts
/-- The rest of a left-associative chain at level `lvl`. -/
def pL : Nat → Nat → CE → List Tok → Option (CE × List Tok)
  | 0, _, _, _ => none
  | _ + 1, _, a, [] => some (a, [])
  | f + 1, lvl, a, t :: r =>
    match opAt lvl t with
    | some o => (pE f (lvl + 1) r).bind fun q => pL f lvl (.bin o a q.1) q.2
    | none => some (a, t :: r)
def pP : Nat → List Tok → Option (CE × List Tok)
  | 0, _ => none
  | _ + 1, .num k :: r => some (.num k, r)
  | f + 1, .id x :: .sym .lb :: r => (pE f 0 r).bind fun q => (closing .rb q.2).map fun r' => (.idx x q.1, r')
  | _ + 1, .id x :: .sym .lp :: r => (pArgs r).map fun q => (.call x q.1, q.2)
  | _ + 1, .id x :: r => some (.var x, r)
  | f + 1, .sym .lp :: r =>
    match takeTy r with
    | ([], 0, _) => (pE f 0 r).bind fun q => (closing .rp q.2).map fun r' => (q.1, r')
    | (ws, n, .sym .rp :: r') => (classify ws n (constIn r)).bind fun t => (pP f r').map fun q => (.cast t q.1, q.2)
    | _ => none
  | _, _ => none
end

mutual
def pS : Nat → List Tok → Option (CS × List Tok)
  | 0, _ => none
  | f + 1, .id w :: r =>
    if w == kReturn then
      (pE f 0 r).bind fun q => (closing .semi q.2).map fun r' => (.ret q.1, r')
    else if w == kFor then
      match r with
      | .sym .lp :: .id i :: .sym .eq :: .num k :: .sym .semi :: .id i2 :: .sym .lt :: r1 =>
        (pE f 0 r1).bind fun q =>
          match q.2 with
          | .sym .semi :: .id i3 :: .sym .inc :: .sym .rp :: .sym .lc :: r3 =>
            (pSs f r3).map fun q' => (.forN i k i2 q.1 i3 q'.1, q'.2)
          | _ => none
      | _ => none
    else if isTyWord w then
      match takeTy (.id w :: r) with
      | (ws, n, .id x :: .sym .semi :: r') => (classify ws n (constIn (.id w :: r))).map fun t => (.decl t x none, r')
      | (ws, n, .id x :: .sym .eq :: r') =>
        (classify ws n (constIn (.id w :: r))).bind fun t => (pE f 0 r').bind fun q =>
          (closing .semi q.2).map fun r'' => (.decl t x (some q.1), r'')
      | _ => none
    else
      match r with
      | .sym .orEq :: r' => (pE f 0 r').bind fun q => (closing .semi q.2).map fun r'' => (.orEq w q.1, r'')
      | .sym .plusEq :: r' => (pE f 0 r').bind fun q => (closing .semi q.2).map fun r'' => (.addEq w q.1, r'')
      | .sym .shrEq :: .num k :: .sym .semi :: r' => some (.shrEq w k, r')
      | .sym .lb :: r' => (pE f 0 r').bind fun q =>
        match q.2 with
        | .sym .rb :: .sym .eq :: r2 => (pE f 0 r2).bind fun q2 => (closing .semi q2.2).map fun r3 => (.store w q.1 q2.1, r3)
        | _ => none
      | _ => none
  | _, _ => none
/-- Statements up to and including the closing brace. -/
def pSs : Nat → List Tok → Option (List CS × List Tok)
  | 0, _ => none
  | _ + 1, .sym .rc :: r => some ([], r)
  | f + 1, ts => (pS f ts).bind fun q => (pSs f q.2).map fun q' => (q.1 :: q'.1, q'.2)
end

def pParams : Nat → List Tok → Option (List (Ty × List Nat) × List Tok)
  | 0, _ => none
  | f + 1, ts =>
    match takeTy ts with
    | (ws, n, .id x :: .sym .comma :: r) => (classify ws n (constIn ts)).bind fun t => (pParams f r).map fun q => ((t, x) :: q.1, q.2)
    | (ws, n, .id x :: .sym .rp :: r) => (classify ws n (constIn ts)).map fun t => ([(t, x)], r)
    | _ => none

/-- `[static inline] int name(params) { body }`, or `void name(params) { body }` (RC-02). -/
def pFun (f : Nat) : List Tok → Option (CFun × List Tok)
  | .id s :: .id i :: .id t :: .id nm :: .sym .lp :: r =>
    if s == kStatic && i == kInline && t == kInt then
      (pParams f r).bind fun q => (closing .lc q.2).bind fun r' => (pSs f r').map fun q' => (⟨true, nm, q.1, q'.1, false⟩, q'.2)
    else none
  | .id t :: .id nm :: .sym .lp :: r =>
    if t == kInt || t == kVoid then
      (pParams f r).bind fun q => (closing .lc q.2).bind fun r' => (pSs f r').map fun q' => (⟨false, nm, q.1, q'.1, t == kVoid⟩, q'.2)
    else none
  | _ => none

def pFuns : Nat → Nat → List Tok → Option (List CFun)
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | g + 1, f, ts => (pFun f ts).bind fun q => (pFuns g f q.2).map (q.1 :: ·)

def parse (cs : List Nat) : Option (List CFun) :=
  (lex cs).bind fun ts => pFuns (ts.length + 1) (ts.length + 1) ts

/-! ## The reading -/

/-- What a C name is bound to: a byte array (the entry's name for it, and its length), a literal, a word local, or an `int` index. -/
inductive Bd where
  | arr  : List Nat → Nat → Bd
  /-- RC-02: an array the function writes, the entry's name for it, and its length. -/
  | warr : List Nat → Nat → Bd
  | lit  : Nat → Bd
  | word : Bd
  | int  : Bd

abbrev Env := List (List Nat × Bd)

def look : Env → List Nat → Option Bd
  | [], _ => none
  | (y, b) :: e, x => if x == y then some b else look e x

def str (x : List Nat) : String := String.ofList (x.map Char.ofNat)

/-- The words of an array: `x0 x1 …`, one per 8 bytes. -/
def words (base : List Nat) (len : Nat) : List String := (List.range (len / 8)).map fun k => str (base ++ [48 + k])

def tmp (base : List Nat) : String := str (116 :: base)

/-- A name the reading may give to a C local: no digit, not starting with `t`, not `c` or `r`. -/
def okLocal (x : List Nat) : Bool := !x.any isDigit && x.head? != some 116 && x != [99] && x != [114]

def seqAll : List Cmd → Cmd
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqAll cs)

/-- An index that stays inside an array of `len` bytes: the loop index, with `N ≤ len`, or `e & m` with `m < len`. -/
def inRange (loop : Option (List Nat × Nat)) (len : Nat) : CE → Bool
  | .var x => match loop with
    | some (i, N) => x == i && N ≤ len
    | none => false
  | .bin .and _ (.num m) => m < len
  | _ => false

/-- An expression, with the loads it needs hoisted before it, and the arrays read so far in the statement. -/
def rdE (env : Env) (loop : Option (List Nat × Nat)) : CE → List (List Nat) → Option (List Cmd × Expr × List (List Nat))
  | .num k, u => if k < 2 ^ 64 then some ([], lit k, u) else none
  | .var x, u => match look env x with
    | some (.lit k) => if k < 2 ^ 64 then some ([], lit k, u) else none
    | some .word => some ([], .var (str x), u)
    | some .int => some ([], .var (str x), u)
    | _ => none
  | .idx a i, u => match look env a with
    | some (.arr base len) | some (.warr base len) =>
      if u.contains base || !inRange loop len i then none
      else (rdE env loop i u).map fun q => (q.1 ++ [.loadB (tmp base) (words base len) q.2.1], .var (tmp base), base :: q.2.2)
    | _ => none
  | .bin .shr a (.num k), u =>
    if k < 64 then (rdE env loop a u).map fun q => (q.1, .shr q.2.1 k, q.2.2) else none
  | .bin .shr _ _, _ => none
  | .bin o a b, u =>
    (rdE env loop a u).bind fun qa => (rdE env loop b qa.2.2).bind fun qb =>
      let e := match o with
        | .or => some (Expr.bin .or qa.2.1 qb.2.1)
        | .xor => some (.bin .xor qa.2.1 qb.2.1)
        | .and => some (.bin .and qa.2.1 qb.2.1)
        | .sub => some (.bin .sub qa.2.1 qb.2.1)
        | .add => some (.add qa.2.1 qb.2.1)
        | .shr => none
      e.map fun e => (qa.1 ++ qb.1, e, qb.2.2)
  -- RC-02 (RC-02-READING section 3): a cast to a word is the identity on these values, and one to `unsigned char` keeps the low byte.
  | .cast .word e, u => rdE env loop e u
  | .cast .byte e, u => (rdE env loop e u).map fun q => (q.1, .bin .and q.2.1 (lit 255), q.2.2)
  | .cast _ _, _ => none
  | .call _ _, _ => none

/-- A literal loop bound, under `2^31` so `int` and word arithmetic agree on the index. -/
def bound (env : Env) : CE → Option Nat
  | .num k => if k < 2 ^ 31 then some k else none
  | .var x => match look env x with
    | some (.lit k) => if k < 2 ^ 31 then some k else none
    | _ => none
  | _ => none

/-- A loop body: `|=` statements only, none writing the index. -/
def rdBody (env : Env) (loop : List Nat × Nat) : List CS → Option (List Cmd)
  | [] => some []
  | .orEq x e :: r =>
    match look env x with
    | some .word =>
      (rdE env (some loop) e []).bind fun q =>
        (rdBody env loop r).map fun cs => q.1 ++ [.assign (str x) (.bin .or (.var (str x)) q.2.1)] ++ cs
    | _ => none
  | _ => none

/-- The inlined function's body; the last statement is the `return`. -/
def rdS : Env → List CS → Option (List Cmd)
  | _, [] => none
  | env, [.ret e] => (rdE env none e []).map fun q => q.1 ++ [.assign "r" q.2.1]
  | env, .decl .ptr x (some (.cast .ptr (.var y))) :: r
  | env, .decl .ptr x (some (.var y)) :: r =>
    match look env y with
    | some (.arr base len) => if okLocal x then rdS ((x, .arr base len) :: env) r else none
    | _ => none
  | env, .decl .word x (some e) :: r =>
    if !okLocal x then none
    else (rdE env none e []).bind fun q => (rdS ((x, .word) :: env) r).map fun cs => q.1 ++ [.assign (str x) q.2.1] ++ cs
  | env, .decl .int x none :: r => if okLocal x then rdS ((x, .int) :: env) r else none
  | env, .forN i k i2 b i3 body :: r =>
    if k == 0 && i2 == i && i3 == i && (match look env i with | some .int => true | _ => false) then
      (bound env b).bind fun N => (rdBody env (i, N) body).bind fun cs => (rdS env r).map fun rest =>
        For.forN "c" (lit N) (seqAll (.assign (str i) (.bin .sub (lit N) (.var "c")) :: cs)) :: rest
    else none
  | env, .orEq x e :: r =>
    match look env x with
    | some .word =>
      (rdE env none e []).bind fun q => (rdS env r).map fun cs => q.1 ++ [.assign (str x) (.bin .or (.var (str x)) q.2.1)] ++ cs
    | _ => none
  | _, _ => none

def findFun (fs : List CFun) (nm : List Nat) : Option CFun := fs.find? fun g => g.name == nm

/-- Bind the inlined function's parameters to the call's arguments. -/
def bindArgs (outer : List (Ty × List Nat)) (len : Nat) (defs : List (List Nat × Nat)) :
    List (Ty × List Nat) → List CArg → Option Env
  | [], [] => some []
  | (.ptr, x) :: ps, .v y :: as =>
    if outer.contains (.ptr, y) then (bindArgs outer len defs ps as).map ((x, .arr y len) :: ·) else none
  | (.int, x) :: ps, .v y :: as =>
    match defs.find? (·.1 == y) with
    | some (_, k) => (bindArgs outer len defs ps as).map ((x, .lit k) :: ·)
    | none => none
  | (.int, x) :: ps, .n k :: as => (bindArgs outer len defs ps as).map ((x, .lit k) :: ·)
  | _, _ => none

/-- **The front end**: the C text, the entry function, the length of its arrays, and the defines it needs, to an L program. -/
def readC (src : List Nat) (entry : List Nat) (len : Nat) (defs : List (List Nat × Nat)) : Option Prog :=
  (parse src).bind fun fs => (findFun fs entry).bind fun F =>
    if F.inline || !(len == 8 || len == 16 || len == 32 || len == 64) ||
       !F.params.all (fun p => p.1 == .ptr && okLocal p.2) then none
    else match F.body with
    | [.ret (.call g args)] =>
      (findFun fs g).bind fun G =>
        if !G.inline || G.name == F.name then none
        else (bindArgs F.params len defs G.params args).bind fun env => (rdS env G.body).map fun cs =>
          { inputs := F.params.flatMap (fun p => words p.2 len), body := seqAll cs, ret := .var "r" }
    | _ => none

/-! ## `crypto_verify_16`, read from libsodium's text -/

def kV16 := kw ['c','r','y','p','t','o','_','v','e','r','i','f','y','_','1','6']
def kB16 := kw ['c','r','y','p','t','o','_','v','e','r','i','f','y','_','1','6','_','B','Y','T','E','S']
def kV32 := kw ['c','r','y','p','t','o','_','v','e','r','i','f','y','_','3','2']
def kB32 := kw ['c','r','y','p','t','o','_','v','e','r','i','f','y','_','3','2','_','B','Y','T','E','S']

def read16 (src : List Nat) : Option Prog := readC src kV16 16 [(kB16, 16)]

/-- **The program certified is the one read from the C text**: the front end, run on lines 60 to 75 and 79 to 83 of libsodium 1.0.20's
    `verify.c` (pinned by `CSrc`), gives `Bytes.verify16`, by `decide`. -/
theorem read_verify16 : read16 CSrc.verify16C = some Bytes.verify16 := by decide +kernel

/-- **So `crypto_verify_16`, as read from its text, is constant time on the source.** -/
theorem verify16C_ct (E : Type) :
    ∃ p, read16 CSrc.verify16C = some p ∧ Cert.relView (sliceLang E Bytes.secX) (sliceLang E Bytes.secX).lowIn CT.noRet p :=
  ⟨_, read_verify16, CT.verify16_ct E⟩

/-! ## Accepted: `crypto_verify_32`, from the same file -/

def verify32 : Prog := (readC CSrc.verify32C kV32 32 [(kB32, 32)]).getD { inputs := [], body := .skip, ret := lit 0 }

/-- The 32-byte arrays are the eight input words. -/
def sec8 (k : Nat) : Bool := decide (k < 8)

theorem read_verify32 : (readC CSrc.verify32C kV32 32 [(kB32, 32)]).isSome = true ∧
    verify32.inputs = ["x0", "x1", "x2", "x3", "y0", "y1", "y2", "y3"] := by decide +kernel

theorem verify32_ct_checks : CT.ctCheck sec8 verify32 = true ∧ Slots.fits verify32 = true ∧ Lower.okP (Slots.compile verify32) = true := by
  decide +kernel

theorem verify32_ct (E : Type) : Cert.relView (sliceLang E sec8) (sliceLang E sec8).lowIn CT.noRet verify32 :=
  CT.ctCheck_relView verify32_ct_checks.1

/-! ## Refused, each for its own reason -/

/-- **Read, and refused by the certificate, not the parser**: a read at a secret index, `x[y[i] & 15]`. -/
theorem secretIndex_read_refused :
    (read16 CSrc.secretIndexC).isSome = true ∧ (read16 CSrc.secretIndexC).map (CT.ctCheck Bytes.secX) = some false := by
  decide +kernel

/-- **Refused by the front end**: the early exit (`if`, `!=`, an early `return`), a division, an uncounted loop, and an index past the end. -/
theorem refused_by_front :
    read16 CSrc.earlyExitC = none ∧ read16 CSrc.divisionC = none ∧ read16 CSrc.uncountedC = none ∧ read16 CSrc.pastEndC = none := by
  decide +kernel

/-- **Where each refusal falls**: the early exit, the division and the uncounted loop fail to parse; the index past the end parses, and the
    reading refuses it. -/
theorem refusal_stages :
    parse CSrc.earlyExitC = none ∧ parse CSrc.divisionC = none ∧ parse CSrc.uncountedC = none ∧ (parse CSrc.pastEndC).isSome = true := by
  decide +kernel

/-- **Refused by the reading, after parsing**: one array read twice in a statement, a local named `c`, a loop starting at 1. -/
theorem refused_by_reading :
    (parse CSrc.twiceC).isSome = true ∧ read16 CSrc.twiceC = none ∧
    (parse CSrc.reservedNameC).isSome = true ∧ read16 CSrc.reservedNameC = none ∧
    (parse CSrc.startAt1C).isSome = true ∧ read16 CSrc.startAt1C = none := by
  decide +kernel

/-- **More refusals after parsing**: a mask reaching the end, an update naming another variable, a callee not `static inline`, a shift by 64. -/
theorem refused_by_reading' :
    read16 CSrc.maskPastC = none ∧ (read16 CSrc.secretIndexC).isSome = true ∧
    read16 CSrc.updateOtherC = none ∧ read16 CSrc.notInlineC = none ∧ (parse CSrc.notInlineC).isSome = true ∧
    read16 CSrc.shift64C = none := by
  decide +kernel

/-- **The loop bound must fit an `int`**: with the index masked, the bound is tied to nothing else, and `2^31` is refused where `16` is read. -/
theorem int_bound :
    (readC CSrc.maskedLoopC kV16 16 [(kB16, 16)]).isSome = true ∧ readC CSrc.maskedLoopC kV16 16 [(kB16, 2 ^ 31)] = none ∧
    (readC CSrc.maskedLoopC kV16 16 [(kB16, 2 ^ 31 - 1)]).isSome = true := by
  decide +kernel

/-- **C's precedence**: `x[i] ^ y[i] & 15` reads as `x[i] ^ (y[i] & 15)`, and not as `(x[i] ^ y[i]) & 15`. -/
theorem precedence : read16 CSrc.precC = read16 CSrc.precRightC ∧ read16 CSrc.precC ≠ read16 CSrc.precLeftC ∧
    (read16 CSrc.precC).isSome = true := by
  decide +kernel

/-- **Only the lengths L's byte read can mask**: 24-byte arrays are refused, though the loop would fit them. -/
theorem odd_length_refused : readC CSrc.verify16C kV16 24 [(kB16, 16)] = none ∧ (readC CSrc.verify16C kV16 32 [(kB16, 16)]).isSome = true := by
  decide +kernel

/-- **The stated length matters**: read as 8-byte arrays, the 16-step loop would pass the end, and is refused. -/
theorem wrong_length_refused : readC CSrc.verify16C kV16 8 [(kB16, 16)] = none := by decide +kernel

/-- **And the define matters**: without `crypto_verify_16_BYTES`, the call has an argument the reading cannot bind. -/
theorem missing_define_refused : readC CSrc.verify16C kV16 16 [] = none := by decide +kernel

/-! ## RC-02: a direct `void` entry, whose arrays are read and written

  `sodium_add` is not a wrapper around a `static inline` function: it is the entry itself. `readD` reads such an entry
  (`RC-02-READING` §3 and §6):
  - a `const unsigned char *` parameter is a read-only array, and one without `const` an array the function writes;
  - a word parameter, such as `const size_t len`, is bound to its stated value;
  - `size_t`, `uint_fast16_t` and the other word types are words, and the loop index may be one;
  - in the loop body, `x |= e`, `x += e` and `x >>= k` on a word local other than the index, and `a[i] = e` into a written array at an index in range;
  - at the end, each written array is emitted, in parameter order, and the result is 0.

  Its own names start with `#`, which a C identifier cannot: the loop counter is `#c`, so a C local may be named `c`, as `sodium_add`'s
  carry is. Temporaries are still `t` plus an array's name, so a C local may not start with `t`, nor contain a digit, as the array words do. -/

/-- A name `readD` may give to a C local: no digit, not starting with `t`. -/
def okLocalD (x : List Nat) : Bool := !x.any isDigit && x.head? != some 116

def wordLocal (env : Env) (x i : List Nat) : Bool :=
  x != i && (match look env x with | some .word => true | _ => false)

/-- A loop body for `readD`. -/
def rdBodyD (env : Env) (loop : List Nat × Nat) : List CS → Option (List Cmd)
  | [] => some []
  | .orEq x e :: r =>
    if wordLocal env x loop.1 then (rdE env (some loop) e []).bind fun q =>
      (rdBodyD env loop r).map fun cs => q.1 ++ [.assign (str x) (.bin .or (.var (str x)) q.2.1)] ++ cs
    else none
  | .addEq x e :: r =>
    if wordLocal env x loop.1 then (rdE env (some loop) e []).bind fun q =>
      (rdBodyD env loop r).map fun cs => q.1 ++ [.assign (str x) (.add (.var (str x)) q.2.1)] ++ cs
    else none
  | .shrEq x k :: r =>
    if wordLocal env x loop.1 && k < 64 then (rdBodyD env loop r).map fun cs => .assign (str x) (.shr (.var (str x)) k) :: cs
    else none
  | .store a ix e :: r =>
    match look env a with
    | some (.warr base len) =>
      if !inRange (some loop) len ix then none
      else (rdE env (some loop) ix []).bind fun qi => (rdE env (some loop) e qi.2.2).bind fun qe =>
        (rdBodyD env loop r).map fun cs => qi.1 ++ qe.1 ++ [.storeB (words base len) qi.2.1 qe.2.1] ++ cs
    | _ => none
  | _ => none

def isIdx (env : Env) (i : List Nat) : Bool :=
  match look env i with | some .word | some .int => true | _ => false

/-- A `void` entry's body: declarations and counted loops, and no `return`. -/
def rdSD : Env → List CS → Option (List Cmd)
  | _, [] => some []
  | env, .decl .word x none :: r => if okLocalD x then rdSD ((x, .word) :: env) r else none
  | env, .decl .word x (some e) :: r =>
    if !okLocalD x then none
    else (rdE env none e []).bind fun q => (rdSD ((x, .word) :: env) r).map fun cs => q.1 ++ [.assign (str x) q.2.1] ++ cs
  | env, .forN i k i2 b i3 body :: r =>
    if k == 0 && i2 == i && i3 == i && isIdx env i then
      (bound env b).bind fun N => (rdBodyD env (i, N) body).bind fun cs => (rdSD env r).map fun rest =>
        For.forN "#c" (lit N) (seqAll (.assign (str i) (.bin .sub (lit N) (.var "#c")) :: cs)) :: rest
    else none
  | _, _ => none

/-- Bind a direct entry's parameters: arrays of the stated length, and word parameters to their stated values. -/
def bindD (len : Nat) (defs : List (List Nat × Nat)) : List (Ty × List Nat) → Option Env
  | [] => some []
  | (.ptr, x) :: ps => if okLocalD x then (bindD len defs ps).map ((x, .arr x len) :: ·) else none
  | (.wptr, x) :: ps => if okLocalD x then (bindD len defs ps).map ((x, .warr x len) :: ·) else none
  | (.word, x) :: ps =>
    match defs.find? (·.1 == x) with
    | some (_, k) => (bindD len defs ps).map ((x, .lit k) :: ·)
    | none => none
  | _ => none

def isArr (p : Ty × List Nat) : Bool := p.1 == .ptr || p.1 == .wptr

/-- **The front end, for a direct `void` entry**: its arrays of length `len`, its word parameters' stated values, to an L program. -/
def readD (src : List Nat) (entry : List Nat) (len : Nat) (defs : List (List Nat × Nat)) : Option Prog :=
  (parse src).bind fun fs => (findFun fs entry).bind fun F =>
    if F.inline || !F.isVoid || !(len == 8 || len == 16 || len == 32 || len == 64) then none
    else (bindD len defs F.params).bind fun env => (rdSD env F.body).map fun cs =>
      { inputs := (F.params.filter isArr).flatMap (fun p => words p.2 len),
        body := seqAll (cs ++ (F.params.filter (·.1 == .wptr)).map (fun p => .emitB (words p.2 len))),
        ret := lit 0 }

def kAdd := kw ['s','o','d','i','u','m','_','a','d','d']
def kLen := kw ['l','e','n']

/-- `sodium_add` at the length of its call in `crypto_core_ed25519_scalar_add`, `crypto_core_ed25519_SCALARBYTES`, 32. -/
def readAdd (src : List Nat) : Option Prog := readD src kAdd 32 [(kLen, 32)]

end LCore.Slice2.CFront
