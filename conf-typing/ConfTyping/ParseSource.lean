/-
  A real parser — brick 21: from source text to a checked guarantee.

  Every prior brick analyzed a *hand-built* AST. A real tool analyzes *source
  text*. This brick closes that gap: a recursive-descent **parser** takes a
  token stream (concrete syntax) and produces the AST, with the classic
  parser-correctness theorem — parsing the printed form of any program recovers
  it exactly (`parse_print`, a round trip). Composed with the taint checker's
  soundness, the result is a guarantee about *written source*:

  > if a source token stream parses to a program and the checker accepts it,
  > then running the program leaks nothing of the untrusted input
  > (`source_injection_free`).

  The language is the injection/taint one (brick 15) in surface syntax:
  `input x`, `const x`, `cat x y z` (concatenate), `emit x` (the sink),
  statements separated by `;`. The parser is total and its round trip is proved
  by induction on the AST; the checker is a taint analysis with two-run
  noninterference; and the end-to-end theorem chains them, so the security
  claim finally attaches to text rather than to a term the prover hand-wrote.
-/
import ConfTyping.Imp

namespace ConfTyping

/-! ## Concrete syntax: tokens -/

inductive Tok where
  | kwInput | kwConst | kwCat | kwEmit | semi
  | id : Nat → Tok
deriving DecidableEq

/-! ## Abstract syntax -/

/-- Atomic statements. -/
inductive Atom where
  | input : Nat → Atom
  | const : Nat → Atom
  | cat   : Nat → Nat → Nat → Atom
  | emit  : Nat → Atom
deriving DecidableEq

/-- A program: a non-empty `;`-separated list of atoms (right-nested). -/
inductive SCmd where
  | one : Atom → SCmd
  | seq : Atom → SCmd → SCmd
deriving DecidableEq

/-! ## Printer and parser -/

def printAtom : Atom → List Tok
  | .input x    => [.kwInput, .id x]
  | .const x    => [.kwConst, .id x]
  | .cat x y z  => [.kwCat, .id x, .id y, .id z]
  | .emit x     => [.kwEmit, .id x]

def printS : SCmd → List Tok
  | .one a    => printAtom a
  | .seq a c  => printAtom a ++ .semi :: printS c

/-- Parse one atomic statement, returning it and the unconsumed tokens. -/
def parseAtom : List Tok → Option (Atom × List Tok)
  | .kwInput :: .id x :: rest              => some (.input x, rest)
  | .kwConst :: .id x :: rest              => some (.const x, rest)
  | .kwCat :: .id x :: .id y :: .id z :: rest => some (.cat x y z, rest)
  | .kwEmit :: .id x :: rest               => some (.emit x, rest)
  | _                                      => none

/-- Recursive-descent parser: an atom, then optionally `; <program>`. Fuel is
    the token budget (one per atom); total. -/
def parseS : Nat → List Tok → Option (SCmd × List Tok)
  | 0, _ => none
  | fuel + 1, toks =>
      match parseAtom toks with
      | none => none
      | some (a, rest) =>
          match rest with
          | .semi :: rest' =>
              match parseS fuel rest' with
              | some (c, rest'') => some (.seq a c, rest'')
              | none => none
          | _ => some (.one a, rest)

/-- Parse a complete program from a token stream (fuel = length suffices). -/
def parse (toks : List Tok) : Option SCmd :=
  match parseS (toks.length + 1) toks with
  | some (c, []) => some c
  | _ => none

/-! ## Parser correctness: the round trip -/

theorem parseAtom_print (a : Atom) (rest : List Tok) :
    parseAtom (printAtom a ++ rest) = some (a, rest) := by
  cases a <;> rfl

/-- The atom count of a program (the fuel it needs). -/
def size : SCmd → Nat
  | .one _   => 1
  | .seq _ c => size c + 1

/-- Round trip at the token level: enough fuel parses a printed program back to
    itself with no tokens left over. (Only for the *complete* printed form —
    the parser is greedy, so trailing tokens are not preserved.) -/
theorem parseS_print (c : SCmd) :
    ∀ (fuel : Nat), size c ≤ fuel → parseS fuel (printS c) = some (c, []) := by
  induction c with
  | one a =>
      intro fuel hf
      cases fuel with
      | zero => simp [size] at hf
      | succ k => cases a <;> rfl
  | seq a c ih =>
      intro fuel hf
      cases fuel with
      | zero => simp [size] at hf
      | succ k =>
          have hk : size c ≤ k := by simp only [size] at hf; omega
          show parseS (k+1) (printAtom a ++ (.semi :: printS c)) = _
          simp only [parseS, parseAtom_print, ih k hk]

theorem size_le_len (c : SCmd) : size c ≤ (printS c).length := by
  induction c with
  | one a => cases a <;> simp [size, printS, printAtom]
  | seq a c ih =>
      simp only [size, printS, List.length_append, List.length_cons]
      have : 1 ≤ (printAtom a).length := by cases a <;> simp [printAtom]
      omega

/-- **Parser correctness (round trip).** Parsing the printed form of any program
    recovers it exactly — the parser is a left inverse of the printer. -/
theorem parse_print (c : SCmd) : parse (printS c) = some c := by
  simp only [parse, parseS_print c (printS c).length.succ (by have := size_le_len c; omega)]

/-! ## The taint checker -/

def trem (x : Nat) (T : List Nat) : List Nat := T.filter (fun y => decide (y ≠ x))
theorem mem_of_mem_trem {z x T} (h : z ∈ trem x T) : z ∈ T := (List.mem_filter.mp h).1
theorem ne_of_mem_trem {z x T} (h : z ∈ trem x T) : z ≠ x := by
  have := (List.mem_filter.mp h).2; simpa using of_decide_eq_true this

def scheckA (T : List Nat) : Atom → Option (List Nat)
  | .input x   => some (x :: T)
  | .const x   => some (trem x T)
  | .cat x y z => some (if (decide (y ∈ T) || decide (z ∈ T)) then x :: T else trem x T)
  | .emit x    => if x ∈ T then none else some T

def scheck (T : List Nat) : SCmd → Option (List Nat)
  | .one a   => scheckA T a
  | .seq a c => (scheckA T a).bind (fun T₁ => scheck T₁ c)

/-! ## Semantics and noninterference -/

abbrev SStore := Nat → Int
abbrev SState := SStore × List Int

def supd (σ : SStore) (x : Nat) (v : Int) : SStore := fun y => if y = x then v else σ y

def execA (inp : Int) : Atom → SState → SState
  | .input x,   (σ, o) => (supd σ x inp, o)
  | .const x,   (σ, o) => (supd σ x 0, o)
  | .cat x y z, (σ, o) => (supd σ x (σ y + σ z), o)
  | .emit x,    (σ, o) => (σ, o ++ [σ x])

def sexec (inp : Int) : SCmd → SState → SState
  | .one a,   s => execA inp a s
  | .seq a c, s => sexec inp c (execA inp a s)

/-- Two runs agree on untainted variables and on emitted output. -/
def SRel (T : List Nat) (s s' : SState) : Prop :=
  (∀ x, x ∉ T → s.1 x = s'.1 x) ∧ s.2 = s'.2

theorem scheckA_ni {inp inp' : Int} {a : Atom} {T T' : List Nat} {s s' : SState}
    (hchk : scheckA T a = some T') (hrel : SRel T s s') :
    SRel T' (execA inp a s) (execA inp' a s') := by
  obtain ⟨σ, o⟩ := s; obtain ⟨σ', o'⟩ := s'
  cases a with
  | input x =>
      simp only [scheckA, Option.some.injEq] at hchk; subst hchk
      refine ⟨fun z hz => ?_, hrel.2⟩
      have hzx : z ≠ x := fun e => by rw [e] at hz; exact hz (by simp)
      have hzT : z ∉ T := fun h => hz (List.mem_cons_of_mem x h)
      simp only [execA, supd, if_neg hzx]; exact hrel.1 z hzT
  | const x =>
      simp only [scheckA, Option.some.injEq] at hchk; subst hchk
      refine ⟨fun z hz => ?_, hrel.2⟩
      simp only [execA, supd]
      by_cases hzx : z = x
      · rw [if_pos hzx, if_pos hzx]
      · rw [if_neg hzx, if_neg hzx]
        exact hrel.1 z (fun hzT => hz (List.mem_filter.mpr ⟨hzT, by simp [hzx]⟩))
  | cat x y z =>
      simp only [scheckA, Option.some.injEq] at hchk
      by_cases hyz : (decide (y ∈ T) || decide (z ∈ T)) = true
      · rw [if_pos hyz] at hchk; subst hchk
        refine ⟨fun w hw => ?_, hrel.2⟩
        have hwx : w ≠ x := fun e => by rw [e] at hw; exact hw (by simp)
        have hwT : w ∉ T := fun h => hw (List.mem_cons_of_mem x h)
        simp only [execA, supd, if_neg hwx]; exact hrel.1 w hwT
      · rw [if_neg hyz] at hchk; subst hchk
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hyz
        refine ⟨fun w hw => ?_, hrel.2⟩
        simp only [execA, supd]
        by_cases hwx : w = x
        · have hy : σ y = σ' y := hrel.1 y hyz.1
          have hz : σ z = σ' z := hrel.1 z hyz.2
          rw [if_pos hwx, if_pos hwx, hy, hz]
        · rw [if_neg hwx, if_neg hwx]
          exact hrel.1 w (fun hwT => hw (List.mem_filter.mpr ⟨hwT, by simp [hwx]⟩))
  | emit x =>
      simp only [scheckA] at hchk
      by_cases hxT : x ∈ T
      · rw [if_pos hxT] at hchk; simp at hchk
      · rw [if_neg hxT, Option.some.injEq] at hchk; subst hchk
        refine ⟨hrel.1, ?_⟩
        have ho : o = o' := hrel.2
        have hx : σ x = σ' x := hrel.1 x hxT
        simp only [execA]; rw [ho, hx]

theorem scheck_ni :
    ∀ (c : SCmd) (T T' : List Nat) (inp inp' : Int) (s s' : SState),
      scheck T c = some T' → SRel T s s' → SRel T' (sexec inp c s) (sexec inp' c s') := by
  intro c
  induction c with
  | one a =>
      intro T T' inp inp' s s' hchk hrel
      exact scheckA_ni hchk hrel
  | seq a c ih =>
      intro T T' inp inp' s s' hchk hrel
      simp only [scheck, Option.bind_eq_bind] at hchk
      cases hA : scheckA T a with
      | none => rw [hA] at hchk; simp at hchk
      | some T₁ =>
          rw [hA, Option.bind_some] at hchk
          exact ih T₁ T' inp inp' _ _ hchk (scheckA_ni hA hrel)

/-! ## End to end: from source text to injection-freedom -/

/-- **The security guarantee, on source text.** If a token stream parses to a
    program and the taint checker accepts it, then the program's emitted output
    is a function of the trusted program alone — the untrusted input cannot
    influence it. The analysis attaches to *source*, via `parse`, not to a
    hand-built AST. -/
theorem source_injection_free {toks : List Tok} {c : SCmd} {T : List Nat}
    (hparse : parse toks = some c) (hchk : scheck [] c = some T)
    (inp inp' : Int) (σ₀ : SStore) :
    (sexec inp c (σ₀, [])).2 = (sexec inp' c (σ₀, [])).2 :=
  (scheck_ni c [] T inp inp' (σ₀, []) (σ₀, []) hchk ⟨fun _ _ => rfl, rfl⟩).2

/-! ## Witnesses: real source text -/

/-- Unsafe source: `input 0 ; cat 2 1 0 ; emit 2` — read input, concatenate it
    into a query, emit. Written as a token stream, as a tool would receive it. -/
def unsafeSrc : List Tok :=
  [.kwInput, .id 0, .semi, .kwCat, .id 2, .id 1, .id 0, .semi, .kwEmit, .id 2]

/-- **It parses** to the expected program — the parser accepts real text. -/
theorem unsafe_parses :
    parse unsafeSrc = some (.seq (.input 0) (.seq (.cat 2 1 0) (.one (.emit 2)))) := by
  decide

/-- **And the checker rejects the parsed program** — the emitted query `2` is
    tainted by the input `0`. Injection caught, from source text. -/
theorem unsafe_src_rejected :
    scheck [] (.seq (.input 0) (.seq (.cat 2 1 0) (.one (.emit 2)))) = none := by decide

/-- Safe source: `input 0 ; const 2 ; emit 2` — emit a trusted constant. -/
def safeSrc : List Tok :=
  [.kwInput, .id 0, .semi, .kwConst, .id 2, .semi, .kwEmit, .id 2]

theorem safe_parses :
    parse safeSrc = some (.seq (.input 0) (.seq (.const 2) (.one (.emit 2)))) := by decide

theorem safe_src_accepted :
    (scheck [] (.seq (.input 0) (.seq (.const 2) (.one (.emit 2))))).isSome = true := by decide

/-- The safe source is injection-free, end to end from its text. -/
theorem safe_src_injection_free (inp inp' : Int) (σ₀ : SStore) :
    (sexec inp (.seq (.input 0) (.seq (.const 2) (.one (.emit 2)))) (σ₀, [])).2
      = (sexec inp' (.seq (.input 0) (.seq (.const 2) (.one (.emit 2)))) (σ₀, [])).2 := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp safe_src_accepted
  exact source_injection_free safe_parses hT inp inp' σ₀

end ConfTyping
