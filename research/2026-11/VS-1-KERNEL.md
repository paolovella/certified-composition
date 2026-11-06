# VS-1 step 2: what the slice needs from the kernel (2026-11-03)

**Result: on paper, the slice forces no kernel change.** Each of the three open questions has an answer on
today's `PassCert`, `Lang`, `Beh` and `Ev`. This is a design, tested only by one probe binary. Step 5's proof
is what judges F3's kill rule.

Probe: `selfStack` and `selfBranch` in `l-core/LCore/Slice/Skeleton.lean`, under QEMU 8.2.2 user mode.

## 1. What makes the stack pointer hard

Step 1 found that the loader's `sp` changes with the environment and `argv`. So a real run's initial state
includes values the source language knows nothing about, and the kernel asks two things of them:

- **`cover`:** every admissible target input must be `enc i` for some admissible source input.
- **`det`:** for **any** two source inputs, not only related ones, equal source views give equal target views.

The obvious fix fails. If the source input carries an unused `sp` and target addresses depend on it, two
inputs differing only in `sp` have equal source views and different target views, so `det` is false. Making
addresses relative to `sp` would hide it, but then the model no longer states what the attacker sees.

## 2. The design

**The program sets its own stack.** The entry stub loads `sp` with a fixed address in the image's own data
segment, as its first instruction. Nothing the compiled program does reads the loader's `sp`.

Probe: the first logged state shows three different loader values (`...a890`, `...be00`, `...a860`). From the
second instruction on, across a changed environment and changed `argv`, PC, `sp` and `a0` are identical at
every step, with `sp` at `0x21000`.

**A passive environment.** Each language in the pipeline has input `Inputs × E`, where `E` is what the machine
holds and the program must not depend on: the loader's `sp`, the other initial registers, and memory outside
the image's segments. The source's run ignores `E`. `lowIn` does not constrain it.
- `cover` holds, because the source carries `E` and `enc` passes it down.
- `det` becomes the real obligation: **the compiled program's view does not depend on `E`.** That is true only
  because of the stub, and it has to be proved from the machine's semantics.
- The target's `rel` then covers every environment, which is what an attacker controlling `argv` requires.

The source language is parameterised by `E`, so it does not name RISC-V registers. That is the cost: every
language in the pipeline has this parameter.

**Inputs by position, in a data segment.** A source program names its inputs in order, and input `k` is the word
at `base + 8k`. So `enc` does not depend on the program's variable table, and `enc`'s lack of a program argument
is not an obstacle for this slice. Unlike P1, nothing is hidden in the target program. The word width and a
fixed capacity make the map total.

Probe: inputs `(40, 2)` give `a0 = 42`. Inputs `(300, 0)` give `a0 = 0x12c`, with the same PCs and the same `sp`.

**`Adm` states the loader's contract:** the code is at its address, the data segment holds the inputs, and the
rest of that segment is zero. Probe: a load from the zeroed part reads 0. The contract is a trust-base entry,
checked only by running.

**The result is an event.** At the exit `ecall`, the machine emits `Ev.ext "ret" [a0]`, with outcome `done`. The
source emits the same event. `Beh` needs no `ret` field.
- `progress` and `reflect` already require finished runs to have equal events, so **result correctness follows
  from the existing obligations** and needs no new one.
- `rel` on the source already means a secret cannot reach the result.
- `ev_sim` needs the target's events to be a prefix of the source's, and they are: nothing is emitted before exit.
- This departs from PLAN-2026-10 §2, which gave `Beh` a `ret : List W64`. `Ev.ext` takes `Int`s, so the word is
  cast to a `Nat`-valued `Int`.

**`W64` lives in the slice, not in the kernel.** No kernel definition needs it once the result is an event. It
moves to Ring 0 with the RV `Lang`, if and when F6 locks them.

**Leakage.** The target's is `Lk.step [pc]` for each instruction and `Lk.addr` for each load and store. Slot and
input addresses are constants, and so `det` needs only that the PCs follow from the source's branch bits. Probe:
`selfBranch` on inputs 0 and 5 takes 7 and 8 instructions, and differs in one PC, as the source's branch bit would.
Faults: `Outcome.abort` suffices, and a compiled program in the slice cannot fault, since it touches only its
constant addresses.

## 3. Kernel changes

| Candidate | Forced by the slice? | Status |
|---|---|---|
| `ret` in `Beh` | No: an event does it | Not proposed |
| `enc : S.Prog → S.In → T.In` | No: positional inputs | Open for passes that change branches (`SPECULATION-PASSES.md`), and for a layout that really depends on the program |
| `cover` per compiled program, up to behaviour | No: the passive environment does it | Noted. It would remove `E` from every language, and it may be cleaner. Weigh it after step 5, with the cost of `E` known |
| `W64` in Ring 0 | No | Moves with the RV `Lang` at F6 |

## 4. What this does not show

- **Nothing is proved.** One probe binary is evidence about QEMU and Linux, not about the theorem. The kill rule
  stays unjudged until step 5.
- **"No kernel change" is an easy result to want.** The slice has no heap, calls or loops, and all its addresses
  are constants, so `det` is at its easiest. Secret-independent but input-dependent addresses, which real programs
  have, are not tested. A later slice has to.
- **Input through a data segment is not usable I/O.** Each input needs its own image, built from the same literal
  code. It keeps the OS out of the slice. Real input means a `read` shim and an OS contract.
- **Residue is out.** Registers and stack at exit still hold what they held, and the model does not observe them.
  PLAN-2026-10 §4 requires zeroisation before this is a claim about an attacker who reads memory.
- **The stack size is a fixed premise.** No recursion and no loops make it static here.

## 5. Next

Step 3: `Word`, the source `Lang` parameterised by `E`, the checker with accepted and refused witnesses, and `rel`
and `bound` on the source, in `l-core/LCore/Slice/`. No kernel branch is needed.
