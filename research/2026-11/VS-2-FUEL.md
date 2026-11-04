# VS-2 step 2: fuel, `det` and addresses, on paper (2026-11-04)

**Result: on paper, loops and input-dependent addresses force no kernel change, and the plan needs three corrections.** Nothing here is proved. The obligations below are what step 6 has to
prove, and the kill rule stays unjudged until then. "No kernel change" was an easy conclusion to want last time too, so §5 says where this design is most likely to be wrong.

## 1. Corrections to the plan

**The array cannot start with the inputs.** `VS-2.md` makes the array's first words the positional inputs. Input variables live at slots 0 to 63, so `a[0] := y` would silently change an input variable on the
machine and not in the source, and the simulation would be false. The array gets its own region: **64 words from slot 64, zero at the start, with locals from slot 128.** The index still depends on input. Reading the
array no longer reads inputs directly, which the program does by name.

**The array's label is flow-sensitive and only rises.** The checker tracks one bit: it starts low, and rises at a store of a high value. A load makes its target high if the bit is. A loop's body must not change the checker's state beyond its entry (below).

**The loop rule needs a fixed point.** `highC` is flow-sensitive, so a body can make a variable high that the guard reads on the next iteration. The rule: the state after the body must be contained in the state at the
head. Otherwise refuse. A witness is required: `x := 0; while (b) { if (x) {...}; x := s }` branches on a secret only on the second iteration, and a checker that looks once would accept it.

## 2. The machine's shape

| Source | Instructions |
|---|---|
| `x := a[e]` | `e` into `r`; `andi r, r, 63`; `add r, r, r` three times; `add r, r, x7`; `ld r, 512(r)`; `sd r, slot(x7)` |
| `a[e] := y` | the same address into `r`; `y` into `r'`; `sd r', 512(r)` |
| `while e { b }` | `e`; `beq r, x0, end`; `b`; `beq x0, x0, head` |

**The source must show the index.** `Lk.addr` of the masked index joins the source's leakage at each array access. The target's address is `dataBase + 512 + 8 * i`, a function of it. Without this, two source runs with equal leakage could
have different target addresses, and `det` is false. Slot addresses stay constants and stay out of the source's leakage.

## 3. The obligations

`Xform`: **`fuel m = m`**, and `cost c = L * c + L`, with `L` the code's length. Both are ordinary, and the constant fuel of VS-1 is gone.

Why `fuel m = m` works: frames carry no `seq`, as `push` flattens them, so every source step is one tick and at least one instruction. So the source at fuel `m` is never behind the target at fuel `m`.

| Obligation | What it says here | Template |
|---|---|---|
| `ev_sim` | Target events at `m` are a prefix of the source's at `m`. Only the exit emits, and the target reaching it means the source has | `behind` |
| `cost_sim` | Target cost at `m` is at most `L * source cost + L`. Each source step is at most `L` instructions. A pending jump belongs to no source step, so the `+ L` must bound how many are pending | `behind`, VS-1's `walk_len` |
| `det` | Equal source views at `m` give equal target views at `m` | `det_split`, `eq_mono` |
| `progress`, `catch_up` | After about `L * n + L` instructions, the target has passed `n` source steps | `ahead` |
| `reflect` | What the target finishes at `m`, the source finished by `m`, alike | `behind` |

**`run_eq` needs replacing.** VS-1's `walk` computes a finite list, and a run that never finishes has none. Its replacement is **an intermediate machine, `runX`**: the same frames and slots as the source, the same PCs and addresses as the target, but
no registers, no memory and no environment. It spends one fuel per instruction, with a pending list of micro-steps it fills from the next frame.
- **`T.run m = runX m ...` at every fuel.** `Exec` and `playApp` carry over, since they are already per-fuel, and so do `genE_exec` and the entry and exit lemmas. So `compiled_ignores_env` holds at every fuel, for the same reason as before: `runX` has nothing to read it from.
- **`det` then has no machine in it**, only two runs of `runX` against two runs of the source. It splits off one source step at a time. The target needs the first step's segment of the source's leakage, and the rest at less fuel, which needs `eq_mono`: equal views at `m` are equal at any `m' ≤ m`.
  That holds because each source step starts with a step marker, so the first `n` markers cut the list at the same place in both runs.

## 4. What should need no kernel change

- `enc` is still the identity for this pass, and positional for the slot pass.
- `Xform` and `PassCert` already allow all of the above. `det`, `progress`, `catch_up` and `reflect` are stated per fuel.
- `Lang.Lawful`'s `diverge` holds with `d = 0`: each fuel spent on a source step costs one, and flattening keeps `seq` out of frames.
- The result stays an event, and a program that never finishes simply never emits it, so `live` and `trace` still mean what they should.

**`bound` loses its generality.** `costOf` has no value for a `while`, so `slice_bound` becomes a theorem about programs with no loop. That is a source-language change, and not a kernel one. The pass's `cost_sim` still holds for every program, loops included.

**VS-1 stays intact.** `Slice2` is a new source, slot pass and lowering, so VS-1's theorems remain evidence. `Rv.lean` is shared and grows by `andi` and signed `beq`, with VS-1's proofs and `rv_diff.py` re-run on it.

## 5. Where this is most likely wrong

1. **`eq_mono` on the source, with a view that hides channels.** `f` may hide the result, so two views can agree when the runs differ in `ev`. Only leakage, cost and outcome cut the list, and they are all in every view, so I expect it to hold. `Split.lean` proves its version for one language.
2. **Pending jumps in `cost_sim` and `ahead`.** A jump belongs to no source step, and in a loop inside a loop several are pending. `+ L` works only if pending jumps never exceed the code's length. They are bounded by nesting depth, which needs its own invariant.
3. **Registers across a loop.** VS-1 proved expression code leaves lower registers alone, and only `x7` must survive a statement. A statement's own temporaries must not be read across a back-edge. I expect the invariant to carry, since it never mentions temporaries.
4. **The array proof's arithmetic.** `andi` and three doublings must equal `8 * (v mod 64)`, on wrapping words, with the result in range. It needs new `Good` lemmas for `andi` and a signed `beq`. Tedious, not deep, but those lemmas hit `omega`'s limits in VS-1.
5. **Kernel budgets.** `Lower.lean` is already long, and `lean4lean` has a per-theorem limit. Step 1's lessons apply: no `decide` on `Lk` or `Beh` over unevaluated values, and split large proofs.

**What this design does not test.** A masked index cannot go out of bounds, so the source never aborts on an access. Real input-dependent addresses are mostly heap pointers, with aliasing and lifetimes. So even a clean result here leaves "no kernel change" open for the heap.

## 6. Decisions

1. **The three corrections in §1.** They change the plan, so they are the user's to accept.
2. **Whether to start on the code.** Steps 3 to 6 are the expensive part of this item: most of a new `Lower`, on the order of VS-1's 1,500 lines.
