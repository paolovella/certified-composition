/-
  One observer's view through expression splitting, by the kernel's transfer alone (F6).

  A consumer of the pass, not part of it: `Split.lean` holds no certificate knowledge beyond
  `split_carries` (check-claims guard (p)), and nothing here proves a certificate about the pass.
  These two theorems apply `relView_transfer`, whose one premise about the pass, `det` for every
  observer, `splitPass` proved once.
-/
import ConfTyping.Split

namespace ConfTyping.Split

/-- **One observer's view through a one-to-many pass**: any `relView` certificate of a program
    reaches its split, by the transfer alone. -/
theorem split_carries_view {P : Partition} {π : MedPolicy} {c : UCmd} {R : Store → Store → Prop}
    {g : LCore.Observer} (h : LCore.Cert.relView (ucmdLangS P π) R g c) :
    LCore.Cert.relView (ucmdLangS P π) R g (split c) :=
  (splitPass P π).relView_transfer (p := c) rfl
    (fun u u' _ _ hr => ⟨u, u', trivial, trivial, hr, rfl, rfl⟩) h

/-- A program `bcheck` accepts carries every observer's view to its split: a certificate that
    exists (`exProg_checks`), so `split_carries_view` is not vacuous. -/
theorem split_carries_every_view {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) (g : LCore.Observer) :
    LCore.Cert.relView (ucmdLangS P π) (ucmdLangS P π).lowIn g (split c) :=
  split_carries_view (LCore.Cert.rel_relView (bcheck_lcoreS h π).2.2.2 g)

end ConfTyping.Split
