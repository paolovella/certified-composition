/-
  Path traversal — brick 17: the method generalizes to a second real class.

  Bricks 14–16 made injection real. Injection is one instance of a general
  shape — *untrusted data changing the meaning of a structured sink* — and the
  defenses are instances of a general method (bind data as a leaf; never let it
  reach the structure). This brick shows the method is not injection-specific by
  applying it to **path traversal** (CWE-22): an untrusted filename containing
  `..` escapes the intended base directory (`open(base + "/" + userinput)` with
  `userinput = "../../etc/passwd"`).

  A path input is a list of steps — `down n` (enter a subdirectory) or `up`
  (`..`). Resolving it against a base directory either stays under the base
  (**contained** — safe) or pops above it (**escape** — traversal). The results,
  mirroring the injection line:

  * `traversal_escapes` — a `..`-bearing input escapes the base (the attack, a
    theorem);
  * `flat_contained` — a `..`-free input always stays contained (safe when the
    structure is fixed);
  * `openLeaf` / `openLeaf_contained` — the by-construction fix: an API that
    takes a *leaf name* (not a path) can never traverse, whatever the name;
  * `pathCheck_sound` — the runtime check "reject inputs containing `..`" is
    sound: accepted inputs are always contained.

  Same pattern as parameterized queries: keep the untrusted value in a data
  position (a leaf), never a structural one (a `..`), and containment is a
  theorem.
-/
import ConfTyping.Imp

namespace ConfTyping

/-! ## Paths and resolution -/

/-- A step in a path: descend into a named subdirectory, or `..`. -/
inductive PStep where
  | down : Nat → PStep
  | up   : PStep
deriving DecidableEq

/-- Resolve one step against the current position *relative to the base*
    (`[]` = at the base). `up` at the base escapes — the traversal. -/
def stepRel : Option (List Nat) → PStep → Option (List Nat)
  | none,      _        => none
  | some rel,  .down n  => some (rel ++ [n])
  | some rel,  .up      => match rel with
                            | []     => none          -- escape above base
                            | _ :: _ => some rel.dropLast

/-- Resolve a full path relative to the base; `none` means it escaped. -/
def resolveRel (steps : List PStep) : Option (List Nat) :=
  steps.foldl stepRel (some [])

/-- Resolve against a concrete base directory. `none` = escaped the base
    (path traversal); `some p` = the accessed directory, always under `base`. -/
def resolve (base : List Nat) (steps : List PStep) : Option (List Nat) :=
  (resolveRel steps).map (fun rel => base ++ rel)

/-- **Containment**: the resolved path stays under the base — witnessed by a
    relative remainder. -/
def Contained (base : List Nat) (steps : List PStep) : Prop :=
  ∃ rel, resolve base steps = some (base ++ rel)

/-! ## The traversal attack -/

/-- **Path traversal, as a theorem.** From the base, `foo/../../` (descend once,
    then `..` twice) escapes above the base — the resolver returns `none`. This
    is `../../etc/passwd` reaching outside the intended directory. -/
theorem traversal_escapes (base : List Nat) :
    resolve base [.down 3, .up, .up] = none := by
  simp [resolve, resolveRel, stepRel, List.foldl]

/-- A bare `..` escapes immediately. -/
theorem dotdot_escapes (base : List Nat) : resolve base [.up] = none := by
  simp [resolve, resolveRel, stepRel, List.foldl]

/-! ## Safe by construction: no `..` stays contained -/

/-- A path input is *flat* if it never uses `..`. -/
def flat (steps : List PStep) : Bool := steps.all (fun s => s ≠ .up)

/-- A flat path never escapes: folding `stepRel` from any `some` stays `some`. -/
theorem flat_resolveRel_aux :
    ∀ (steps : List PStep), flat steps = true → ∀ rel : List Nat,
      ∃ rel', steps.foldl stepRel (some rel) = some rel'
  | [], _, rel => ⟨rel, rfl⟩
  | .down n :: rest, hf, rel => by
      have hrest : flat rest = true := by
        simpa [flat, List.all_cons] using hf
      simpa [List.foldl, stepRel] using flat_resolveRel_aux rest hrest (rel ++ [n])
  | .up :: _, hf, _ => by simp [flat, List.all_cons] at hf

/-- **Flat inputs are contained.** A filename with no `..` always resolves to a
    path under the base — untrusted *names* cannot escape, only untrusted
    *structure* (`..`) can. -/
theorem flat_contained (base : List Nat) (steps : List PStep)
    (h : flat steps = true) : Contained base steps := by
  obtain ⟨rel', hrel'⟩ := flat_resolveRel_aux steps h []
  exact ⟨rel', by simp [resolve, resolveRel, hrel']⟩

/-! ## The by-construction fix: a leaf-name API -/

/-- The safe API: open a *leaf name* under the base — the value is a single
    name, structurally incapable of traversal (the path-analog of a bound query
    parameter). -/
def openLeaf (base : List Nat) (name : Nat) : List Nat := base ++ [name]

/-- **The leaf API never traverses**, for any name — containment by
    construction, no check required. -/
theorem openLeaf_contained (base : List Nat) (name : Nat) :
    ∃ rel, openLeaf base name = base ++ rel :=
  ⟨[name], rfl⟩

/-! ## The runtime check is sound -/

/-- The path check: reject any input containing `..`. -/
def pathCheck (steps : List PStep) : Bool := flat steps

/-- **Soundness.** An accepted input (no `..`) is contained — it accesses only
    files under the base. The check rules out exactly the traversal structure. -/
theorem pathCheck_sound (base : List Nat) (steps : List PStep)
    (h : pathCheck steps = true) : Contained base steps :=
  flat_contained base steps h

/-- **The check rejects the traversal witness** — checker and resolver agree the
    `..`-bearing path is unsafe. -/
theorem pathCheck_rejects : pathCheck [.down 3, .up, .up] = false := by decide

/-- **Non-vacuity: a safe path passes and is contained.** -/
theorem safe_path_contained (base : List Nat) :
    pathCheck [.down 1, .down 2] = true ∧ Contained base [.down 1, .down 2] :=
  ⟨by decide, pathCheck_sound base _ (by decide)⟩

end ConfTyping
