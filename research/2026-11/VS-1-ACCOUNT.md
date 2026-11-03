# VS-1: the account (2026-11-03)

The question was: **does the kernel survive contact with a real machine?** For the slice it tried, yes. What it tried is small, and the
kernel's hardest cases are still ahead, so this does not settle the question.

## 1. What now exists

One program, 76 bytes of RV64, through this path:

| Stage | Language | Input | File |
|---|---|---|---|
| Source | `sliceLang`: `W64`, `add`, `seq`, `ite`, a result | words by position, and a passive environment | `Source.lean` |
| After `slotPass` | `slotLang`: numbered slots | the data segment's bytes | `Slots.lean` |
| After `rvPass` | `rvLang`: an RV64 subset | those bytes, and the machine's environment | `Rv.lean`, `Lower.lean` |
| The bytes | a literal | | `Image.lean` |

- `compile_is_literal`: the pipeline produces those bytes, by kernel evaluation.
- `image_carries`: they have `rel` and a budget of 95 instructions on `rvLang`, on every byte pattern in the secret word and in every
  environment. All through the kernel's transfers, with no proof about either certificate in either pass.
- Under QEMU: 204 inputs, 3,604 instructions and 1,785 addresses match the model. 192 comparisons of inputs differing only in the secret,
  across environments and `argv`, are identical. The refused programs, compiled anyway, are seen to leak, and `clean` is not.

All six kernels accept. It is about 3,400 lines of Lean, and took one long session.

## 2. What the kernel needed

**No kernel change was forced.** `PassCert`, `Lang`, `Beh` and `Ev` all stood, and that includes three things they were doubted on:

| Doubt | What happened |
|---|---|
| A pass whose input changes (F3's kill rule) | `slotPass` goes from words to bytes and meets `cover` and `low_cover`. `no_pass_drops_a_word` shows `cover` has teeth |
| The machine's environment, which `det` must not see | `compiled_ignores_env`. `no_pass_pins_env` shows pinning it, the tempting fix, cannot be a certified pass |
| A result, which `Beh` does not have | An `Ev.ext "ret"` event. `progress` and `reflect` then give result correctness, with no new obligation |

**Do not read this as "the kernel is right".** It is an easy result to want, and these limits are why it is weak:

- **No loops.** `t.fuel` is a constant, the fuel at which the source has finished. That is impossible with loops, so aligning fuel across a
  real lowering is **untested**.
- **Constant addresses.** Every address the slice touches is a constant, 3 of them in the image. `det` is at its easiest there. Addresses
  that depend on public input are **untested**.
- **`enc` still has no program.** Positional inputs avoided the question, and it is still open for a layout that depends on the program,
  and for passes that change branches once directives are in the input (`SPECULATION-PASSES.md`).
- **The passive `E`** sits in every language's input. Weakening `cover` to hold per compiled program might be cleaner.

## 3. What stays wrong

**The slice is not L.** It is a new language. `UCmd` does not compile, so none of F5's rows reach bytes: not injection, isolation, speculation,
leaks, or mediation. The map's "through a pass" column is unchanged. What compiles has no loops, heap, strings, functions, or mediation.

**The model is believed by testing.** `rvLang` is compared with QEMU on chosen cases, and QEMU is not hardware. It is not linked to Sail, though
S-SAIL's proof route is open. It says nothing about timing, caches, speculation, or residue: registers and memory keep their values at exit.

**Known holes, each stated in the code:**
- `rvLang` aborts on what it does not model, where a real machine may carry on. `image_decodes`, `image_not_compressed` and `image_one_exit` show this
  image avoids that. Other programs need the same check.
- Leaked addresses are checked for this image only. `rv_diff.py` cannot see them.
- A literal budget of 95, for a program that runs 18.
- Input by data segment means a new image per input. That is not usable I/O.
- `comp` refuses literals of 2048 or more: there is no shift instruction.

**Not understood.** The kernels' budgets bit twice:
- `lean4lean` timed out on `run_eq`, and splitting the proof fixed it.
- Three kernels exhaust their budgets on `decide` over the compiled `secretBranch`'s leakage at fuel 4, on 44 bytes. Lean, the paranoid checker and
  nanoda accept. `tampered_leaks` looks similar and passes. Three hypotheses failed: the compile, the fuel, and an integer power in the model. The
  theorem was dropped and the gate left alone. The leak stays shown on the source and on the real binary. **So the cost of kernel evaluation is not
  understood, and PLAN-2026-10's T2, compiling by kernel evaluation, is at risk at any real size.** 76 bytes says nothing about 76 KB.

## 4. The trust base of `image_carries`, for a real run

1. The Lean kernels, and the six that re-check them.
2. `rvLang`, tested and not proved against anything.
3. The ELF wrapper and the loader: that the bytes land where `init` says, and that the rest of the data segment is zero.
4. QEMU, as the only machine it has run on.
5. The kernel's `PassCert` and `Cert` definitions, which F6 has not locked.

## 5. Proposals, for the user's key

All of these are Ring 0.

| # | Change | Why |
|---|---|---|
| 1 | Extend `tools/mutants.py` and the witness registry to `l-core` | `sliceCheck` is outside both. CI's "39 checkers, 0 missing" never sees it |
| 2 | Extend guard (m) to `LCore/Slice` | Nothing keeps "no certificate-specific pass proof" true |
| 3 | Run `rv_diff.py`, `image_diff.py` and `refused_diff.py` on the heavy runner | None is in CI, so a model change is not re-tested |
| 4 | Make CI's kernel step print each verdict | It hid which kernel failed |

## 6. Recommendation

**Do not lock F6 yet.** The lock would freeze `PassCert` and `Beh` before the two hardest cases have been tried.

**Next: a second slice on the same language, with loops and addresses that depend on public input.** It tests exactly what this one avoided, and it
would show whether `t.fuel`'s alignment or `det` forces a kernel change. Its kill rule: if either does, the change happens before the lock, which is why it
comes first.

**Decision the user owns, once that slice is in: is `sliceLang` the seed of L's core?** Two routes:
- **Grow the slice** into PLAN-2026-10's Core, adding heap, strings and mediation one at a time, each through to the bytes. Every row re-proved, but
  each is real when it lands. I would take this, because `UCmd`'s unbounded integers cannot reach a machine anyway, and PH3 already plans to replace them.
- **Lower `UCmd`** by bridging it to `W64`. It keeps F5's work, and has to settle what an unbounded integer means on a machine.

`L-UNIFY`, the directive design and `REL-01` wait on this choice, since each is about a language that may not be the one that compiles.

**What I would not claim from this.** Not that L is close. The plan's "45 to 65 sessions" was never measured, and one slice does not measure it: this one
avoided the expensive parts on purpose. The honest summary is that the method works end to end, on a program too small to be useful, and that the
next slice is what can show it will not scale.
