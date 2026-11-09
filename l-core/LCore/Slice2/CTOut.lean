/-
  RC-02 step 4: constant time for a program that writes its result. `sodium_add`'s output depends on the secrets by design, as
  `crypto_verify_16`'s result did, so `ctCheck` refuses it. The certificate is `relView` with `noOut`, an observer that reads neither the
  result nor the output.

  **The proof reuses RC-01's.** `eraseP p` is `p` with every `emitB` replaced by `skip`. The two have the same `noOut` view at every fuel:
  both commands tick once and leak nothing, and `noOut` drops the only difference, the output event. So `ctCheck` of `eraseP p` gives
  `relView noRet` for `eraseP p`, and `noOut` reads less than `noRet`.

  **What `noOut` still sees** of an output: that a step ran, and where, in the leakage, and on the machine the `write`'s PCs and the addresses
  it reads. It does not see the bytes, nor, through events, that an output happened. An observer chooses channels, never payloads.
-/
import LCore.Slice2.Out

namespace LCore.Slice2.CT

open Slice (W64 Expr Store tick highInit highE)
open Bytes (secX words4 src)
open Ops (lit)

/-- **The observer for constant time with an output**: every channel but the result's and the output's. -/
def noOut : Observer := fun c => decide (c ≠ .ext "ret" ∧ c ≠ .emit "out")

/-- Every `emitB`, as `skip`. -/
def eraseC : Cmd → Cmd
  | .emitB _ => .skip
  | .seq a b => .seq (eraseC a) (eraseC b)
  | .ite e a b => .ite e (eraseC a) (eraseC b)
  | .loop e b => .loop e (eraseC b)
  | .skip => .skip
  | .assign x e => .assign x e
  | .load x e => .load x e
  | .loadB x ns e => .loadB x ns e
  | .store e v => .store e v
  | .storeB ns e v => .storeB ns e v

def eraseP (p : Prog) : Prog := { p with body := eraseC p.body }

def eF (f : Frame) : Frame := (eraseC f.1, f.2)

theorem push_erase : ∀ (c : Cmd) (q : List Nat) (k : List Frame), push (eraseC c) q (k.map eF) = (push c q k).map eF
  | .seq a b, q, k => by simp only [eraseC, push]; rw [push_erase b, push_erase a]
  | .skip, _, _ | .assign _ _, _, _ | .ite _ _ _, _, _ | .loop _ _, _, _ | .load _ _, _, _ | .loadB _ _ _, _, _
  | .store _ _, _, _ | .storeB _ _ _, _, _ | .emitB _, _, _ => rfl

theorem tick_viewE (f : Observer) (l : List Lk) (q : List Nat) {r r' : Beh} (h : r.view f = r'.view f) :
    (tick l q r).view f = (tick l q r').view f := by
  rw [tick_view, tick_view, h]

/-- **`noOut` sees the same of a program and of it with its outputs erased**, at every fuel. -/
theorem run_view_erase (ret : Expr) : ∀ (n : Nat) (k : List Frame) (s : Store) (a : Arr),
    (run ret n (k.map eF) s a).view noOut = (run ret n k s a).view noOut := by
  intro n
  induction n with
  | zero =>
    intro k s a
    cases k with
    | nil => rfl
    | cons _ _ => rfl
  | succ m ih =>
    intro k s a
    cases k with
    | nil => rfl
    | cons f k =>
      obtain ⟨c, q⟩ := f
      cases c with
      | skip | assign _ _ | load _ _ | loadB _ _ _ | store _ _ | storeB _ _ _ =>
        simp only [List.map, eF, eraseC, run]; exact tick_viewE _ _ _ (ih _ _ _)
      | emitB ns =>
        simp only [List.map, eF, eraseC, run]
        have hv : noOut (Ev.emit "out" (outBytes s ns)).chan = false := rfl
        have h := ih k s a
        have he := congrArg Beh.ev h
        have hl := congrArg Beh.lk h
        have hc := congrArg Beh.cost h
        have ho := congrArg Beh.out h
        simp only [Beh.view] at he hl hc ho
        simp only [etick, tick, Beh.view, List.filter_cons, hv, Bool.false_eq_true, ↓reduceIte, he, hl, hc, ho]
      | seq c₁ c₂ =>
        simp only [List.map, eF, eraseC, run]
        rw [push_erase c₂ _ k, push_erase c₁ _ _]
        exact ih _ _ _
      | ite e c₁ c₂ =>
        simp only [List.map, eF, eraseC, run]
        split
        · rw [push_erase c₁ _ k]; exact tick_viewE _ _ _ (ih _ _ _)
        · rw [push_erase c₂ _ k]; exact tick_viewE _ _ _ (ih _ _ _)
      | loop e b =>
        simp only [List.map, eF, eraseC, run]
        split
        · have : (eraseC (.loop e b), q) :: k.map eF = ((Cmd.loop e b, q) :: k).map eF := rfl
          simp only [eraseC] at this
          rw [this, push_erase b _ _]; exact tick_viewE _ _ _ (ih _ _ _)
        · exact tick_viewE _ _ _ (ih _ _ _)

/-- `noOut` reads less than `noRet`, so what `noRet` sees the same of, `noOut` does. -/
theorem view_noOut {b b' : Beh} (h : b.view noRet = b'.view noRet) : b.view noOut = b'.view noOut := by
  have he := congrArg Beh.ev h
  have hl := congrArg Beh.lk h
  have hc := congrArg Beh.cost h
  have ho := congrArg Beh.out h
  simp only [Beh.view] at he hl hc ho
  have key : ∀ l : List Ev, (l.filter fun e => noRet e.chan).filter (fun e => noOut e.chan) = l.filter fun e => noOut e.chan := by
    intro l
    rw [List.filter_filter]
    congr 1
    funext e
    simp only [noRet, noOut]
    by_cases h1 : e.chan = .ext "ret" <;> by_cases h2 : e.chan = .emit "out" <;> simp [h1, h2]
  have := congrArg (fun l : List Ev => l.filter fun e => noOut e.chan) he
  simp only [key] at this
  simp only [Beh.view, this, hl, hc, ho]

/-- **The constant-time checker for a program with an output**: `ctCheck` of the program with its outputs erased. -/
def ctOutCheck (P : Nat → Bool) (p : Prog) : Bool := ctCheck P (eraseP p)

/-- **`ctOutCheck` gives constant time on the source with an output**: on inputs agreeing on the public positions, at every fuel, the leakage,
    cost and outcome are the same, and the other events, whatever the output and the result. -/
theorem ctOutCheck_relView {E : Type} {P : Nat → Bool} {p : Prog} (h : ctOutCheck P p = true) :
    Cert.relView (sliceLang E P) (sliceLang E P).lowIn noOut p := by
  intro n i i' hi hi' hl
  have hr := ctCheck_relView (E := E) h n i i' hi hi' hl
  have e1 := run_view_erase p.ret n (push p.body [] []) (Slice.initFrom i.1 p.inputs 0) zeroA
  have e2 := run_view_erase p.ret n (push p.body [] []) (Slice.initFrom i'.1 p.inputs 0) zeroA
  have hp : push (eraseC p.body) [] [] = (push p.body [] []).map eF := push_erase p.body [] []
  show (run p.ret n (push p.body [] []) _ zeroA).view noOut = (run p.ret n (push p.body [] []) _ zeroA).view noOut
  rw [← e1, ← e2, ← hp]
  exact view_noOut hr

/-- `ctOutCheck` accepts everything `ctCheck` accepts that has no output. -/
theorem ctOutCheck_put1 : ctOutCheck secX Out.put1 = true ∧ ctCheck secX Out.put1 = false := by decide

/-- **`relView noOut` says something `relView noRet` cannot**: `put1` on two secrets writes two outputs, which `noRet` sees and `noOut` does not. -/
theorem put1_ct_out (E : Type) : Cert.relView (sliceLang E secX) (sliceLang E secX).lowIn noOut Out.put1 :=
  ctOutCheck_relView ctOutCheck_put1.1

theorem put1_not_noRet : ¬ Cert.relView (sliceLang Unit secX) (sliceLang Unit secX).lowIn noRet Out.put1 := by
  intro h
  have hadm : ∀ (a b c d : Nat), (sliceLang Unit secX).Adm (words4 a b c d, ()) := by
    intro a b c d k hk
    have : ¬ k < 4 := by simp only [Slice.cap] at hk; omega
    simp only [words4]
    repeat' split
    all_goals first | omega | rfl
  have hlow : (sliceLang Unit secX).lowIn (words4 1 0 0 0, ()) (words4 2 0 0 0, ()) := by
    intro k hk
    have : ¬ k < 4 := by simpa [secX] using hk
    simp only [words4]
    repeat' split
    all_goals first | omega | rfl
  have := h 10 _ _ (hadm 1 0 0 0) (hadm 2 0 0 0) hlow
  revert this
  decide

/-- **Refused**: the output's index rule holds still. A store at a secret index is refused by `ctOutCheck`. -/
theorem ctOut_secretIndex_refused :
    ctOutCheck secX { inputs := ["x0", "x1"], body := .seq (.storeB ["x1"] (.var "x0") (lit 1)) (.emitB ["x1"]), ret := lit 0 } = false := by
  decide

end LCore.Slice2.CT
