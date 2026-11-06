# VS-2: the account (2026-11-06)

The question was the one VS-1 could not answer: **does the kernel survive loops, and addresses that depend on public input, down to a machine?**
For this slice, yes, with no change, and `git diff` shows `l-core/LCore/Kernel/` untouched since VS-1 ended (`c3ae7e1`). **But over loops only one
of VS-1's two guarantees reaches the bytes**, and that is the first thing to read before using this result.

## 1. What now exists

Two programs, as literal RV64 images, through the same three languages as VS-1, each extended:

| Stage | Language | What is new | File |
|---|---|---|---|
| Source | `sliceLang` | `loop`, which may never finish; one 64-word array, read and written at a masked index; the address leaks | `Slice2/Source.lean` |
| After `slotPass` | `slotLang` | the array in its own slots, 64 to 127; still one step per step | `Slice2/Slots.lean` |
| After `rvPass` | `rvLang` | `andi`, backward `beq`, negative `addi` immediates; **one step becomes many** | `Slice2/{Lower,Chunk,Pass}.lean` |
| The bytes | literals | `scan`, 136 bytes; `spin`, 36 bytes | `Slice2/Image.lean` |

- `scan` loops over the array at a public index. `scan_carries`: its literal image has `rel` on `rvLang`, for every byte pattern in the secret word
  and in every environment, by `rel_transfer` alone. `scan_fuel_tracks`: `t.fuel m = m`, where VS-1's was a constant.
- `spin` never finishes. `spin_carries`, and `spin_image_never_finishes` at every fuel and in every environment, with `spin_image_runs` beside it.
- Under QEMU (`test/image2_diff.py`): 117 runs of `scan`, 108,108 instructions and 48,048 addresses, equal to the model's, PCs and addresses both.
  `spin`'s first 300 instructions equal the model at fuel 300, in 39 runs stopped by the harness. The public word moves the array addresses and the
  index wraps at 64. 144 comparisons differing only in the secret show nothing.
- Teeth (`Slice2/Teeth.lean`, `test/refused2_diff.py`): all six refused programs compile, and each one's bytes fail `rel` through the channel its
  refusal names. That means an address, the PCs, the result, or **when and whether it finishes**. QEMU agrees, and the accepted `scan` shows nothing.

All six kernels accept. It is about 3,100 lines of Lean and 450 of test harness, over four days.

## 2. What the kernel needed

**No kernel change was forced.** The three things VS-1 left untested, and what happened to each:

| VS-1's doubt | What happened |
|---|---|
| Fuel alignment, when a run may never finish | `t.fuel m = m`, `t.cost c = L * c + L`. `behind` gives `ev_sim`, `cost_sim` and `reflect`; `ahead`, on the measure `2n + pending jumps`, gives `progress` and `catch_up`. A jump belongs to no source step, so it is charged to the step that pushed it, and no bound on nesting is needed |
| `det`, with addresses that depend on input | `det_run` runs two machines in different environments side by side. It rests on `same_step`: what the source leaks fixes the next chunk of machine steps and the next frames, on both sides |
| A pass over loops at all | `chunk_exec`, one lemma on the machine: from a good state, a frame's micro-steps take it to the next good state. No pass proof is about a certificate, and the kill rule did not fire |

**One design fact the kernel imposes, now confirmed:** the source must leak the masked index. Without `Lk.addr` in the source's observation, `det` has
nothing to follow on the target. So the source's observation has to anticipate the machine's, and every future source construct that touches memory
will have to do the same.

**Do not read this as "the kernel is right".** What it still has not met:

- **A budget over loops.** `Cert.bound` takes one number for every input. `scan` runs `27n + 9` instructions on public input `n`, and no single number
  bounds that, so `bound` is not claimed. **Over loops, VS-2 carries `rel` and nothing about running time.** A certified loop program may run as long as
  its public input says, or forever, like `spin`. A budget as a function of public input is a shape the kernel does not have. Adding it would be adding
  ~~a sixth shape~~ a seventh shape (*correction of record, the same day:* the kernel already had six, `relView` being the sixth).
- **`enc` with a program-dependent layout.** It is still the identity in `rvPass` and positional in `slotPass`. Unchanged since VS-1.
- **Source-level abort.** The index is masked, so nothing aborts. A language with a real out-of-bounds error has not been lowered.
- **Heap, functions, I/O, mediation, speculation.** None is in either slice.

## 3. What went wrong, and what it teaches

Each item here is in `backlog/VS-2.md`'s log, with its correction of record.

1. **The compiled language could not count a loop down** (step 6). Literals had to be below 2048 and expressions have only `add`, so a guard could reach 0
   only by wrapping past `2^64`. `scan` and the refused programs passed the source and slot layers and then failed `okP`. Nothing had checked that step 4's
   witnesses compile. Negative `addi` immediates fixed it, in VS-1's shared lowering, with VS-1's literal unchanged. **Lesson: a witness is not a witness
   for the bytes until it has been compiled.** Every VS-2 witness now is.
2. **The mutant harness reported 19 of 19 killed when it had checked nothing** (step 6). Its address-space cap stops Lean creating threads, so every build
   aborted before a proof, and any nonzero exit counted as a kill. Now a kill needs a Lean error at a line. **Lesson: VS-2's own rule, a refusal alone is
   satisfied by a checker that rejects everything, applies to the harness too.**
3. **Step 7's concrete trace witnesses compared addresses only, while saying "trace"** (corrected in step 9). Inside `namespace LCore.Slice2`, a bare
   `lkCode` is the source's, which sends every PC to 0, and it wins over an `open`. `scan_carries` was unaffected, and step 8's QEMU comparison covered
   full traces. It surfaced only when two PC leaks would not refute. **Lesson: in a codebase with two languages, a coding of observations needs its own
   name and its own witness** (`mCode`, `mCode_pc_addr`).
4. **Two kernels ran out of fuel comparing two runs' results** (step 9). Deciding `=` on `Ev` lists runs the derived `DecidableEq` over unevaluated values,
   the trap step 1 found for `Lk`. Comparing against a literal is fine (`scan_runs`), and comparing two runs is not. Plain numbers (`evCode`) fixed it.
   **For T2:** this is now the second derived equality to bite, so any kernel-evaluated witness should compare `Nat`s.
5. **An out-of-memory incident** (step 1). A timed-out harness orphaned a 21 GB `lean`, and the OOM killer hit the user's other projects. Every harness
   since runs each child in its own process group, killed as a group, with a memory watchdog.

## 4. The trust base of `scan_carries`, for a real run

As VS-1's, unchanged:
1. The Lean kernels, and the six that re-check them.
2. `rvLang`, compared with QEMU and not proved against anything. `andi`, backward `beq` and negative `addi` are now among the compared cases.
3. The ELF wrapper and the loader.
4. QEMU, as the only machine run on.
5. The kernel's `PassCert` and `Cert`, which F6 has not locked.

## 5. Proposals, for the user's key

VS-1's four are all still open, and two of them bit again:

| # | Change | Why, with what VS-2 adds |
|---|---|---|
| 1 | Extend `tools/mutants.py` and the witness registry to `l-core` | VS-2 ran 32 hand mutants through a harness that once lied (§3.2). `sliceCheck` is still outside both |
| 2 | Extend guard (m) to `LCore/Slice2` | Nothing keeps "no certificate-specific pass proof" true for `rvPass` |
| 3 | Run the QEMU tests on the heavy runner | Five scripts now, none in CI. A model change is not re-tested |
| 4 | Make CI's kernel step print each verdict | **It hid the failure again in step 9.** The verdicts were in the script's output and CI discarded them |

## 6. Recommendation

**On F6. The kernel's part of the condition is met, and the lock should still wait, for two decisions that are not about the kernel.**
- The kernel survived both slices unchanged. The case for waiting on more slices is weak, and the lock does not stop later changes; it puts them behind
  the user's key, which is its purpose.
- **What the lock covers is undecided.** F6's log has it waiting on L-UNIFY, which is held until the L-BYTES route is chosen. A lock now would cover
  `UCmd`'s languages, which do not compile, and not `sliceLang`, which does.
- **REL-01 is still open** in F6's log.

So: **choose the L-BYTES route first, then lock.** And when the lock is judged, read §2's first point: over loops, only `rel` was tested to the bytes.

**On the L-BYTES route, VS-2 strengthens VS-1's preference for growing `sliceLang`.** Loops, an array, and negative immediates now reach bytes, and each
cost one step. ~~`UCmd`'s unbounded integers still cannot reach a machine.~~ *Correction of record, the same day* ([`VS-2-RESEARCH`](VS-2-RESEARCH.md) §1): false as stated, since CakeML compiles them through a verified bignum runtime. The reason that holds: for secret data a bignum's size shows in its time and addresses, so `UCmd` needs a constant-time bignum runtime or bounded integers, and `sliceLang` has the second. The cost is the same as before: every row of the map is re-proved, one at a time,
each real when it lands.

**On a budget over loops, a decision the user owns, independent of the lock.** Either accept that L's certificates say nothing about running time over
loops, or add a shape whose budget is a function of the public input, with its transfer. I would add it, before growing the language further, because
every row the map adds that involves a loop will otherwise be silent on time. It would be ~~a sixth shape~~ a seventh shape (corrected as above), and a G-0 change.

**What I would not claim from this.** Not that L is close, and not that the kernel is final. Two slices, each too small to be useful, have now met loops,
arrays, input-dependent addresses and non-termination, with no kernel change. They have not met a heap, a function, I/O, or any of the map's rows.

*Note, 2026-11-06:* §2's first limit, that over loops only `rel` reaches the bytes, is closed for counted loops by BOUND-01 ([`BOUND-01-ACCOUNT`](BOUND-01-ACCOUNT.md)). It was true when written, and a `while` still has no budget.
