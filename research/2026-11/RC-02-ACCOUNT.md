# RC-02: the account (2026-11-09)

The question came from RC-01's account: every function that returns data, not a flag, needs an output array. The first real one is
libsodium 1.0.20's `sodium_add`, at the 32-byte length of its call in `crypto_core_ed25519_scalar_add`. **It is certified constant-time with
its output, and with a constant budget, on its literal 204-byte RV64 image, by the kernel's transfers alone. The kernel did not change.**

**The claim, exactly.** This C function, read into L at length 32 and compiled by L's certified pipeline, is constant-time on the machine
model. On every two inputs, in every environment and at every fuel, its PCs, addresses, instruction count, outcome and every event but the
output and the result are equal. It runs at most 1825 instructions. It is **not** a claim that libsodium is constant-time, nor one about
cycles, caches or speculation.

## 1. What now exists

| Step | What | Where |
|---|---|---|
| 1 | The reading on paper, pinned: `utils.c`, `utils.h`, the call site and the define | `research/2026-11/RC-02-READING.md` |
| 2 | `sb` and `write(1, buf, len)` in `rvLang`; `write` as an event mid-run; QEMU compares stdout | `Slice/Rv.lean`, `test/rv_diff.py` |
| 3 | `storeB` and `emitB` through both passes; **the replay carries mid-run events** | `Slice2/{Source,Slots,Lower,Chunk,Pass,Out}.lean` |
| 4 | `ctOutCheck` and `relView noOut`, by RC-01's argument through an eraser | `Slice2/CTOut.lean` |
| 5 | The front end reads a direct `void` entry with written arrays; `read_add` by `decide` | `Slice2/{CFront,CSrc,Add}.lean` |
| 6 | The certificate and a constant budget on the image; QEMU, clang and arithmetic agree | `Slice2/AddBytes.lean`, `test/add_diff.py` |

**The headline theorem, `addC_ct_bytes`:** the program the front end reads from lines 313 to 318 and 355 to 360 of the pinned `utils.c`
compiles to exactly `addImage`, which has `Cert.relView (rvLang sec8) lowIn noOut`. `add_bound_bytes` adds 1825 instructions. Under QEMU, on
77 pairs, the image prints `(a + b) mod 2^256` in 1200 instructions on every pair. Clang's build of the same lines prints the same bytes at
`-O0` and `-O2`.

## 2. What the kernel needed

**Nothing, again.** `Lang`, `Beh`, `PassCert`, `relView_transfer` and `bound_transfer` are unchanged. `Ev.emit` already existed, so an
output needed no new observation.

**The pass framework did need a change, in Ring 1.** Its replay of the machine (`Exec`, `playApp`) carried leakage and no events, and every
pass proof assumed the only event was the result at exit. `ExecE` and `addEv` let a frame emit at its last micro-step. `behind`, `ahead`
and `det_run` carry the events, and `catch_run` replaces `fuel_ev`, which became false.
- All 61 earlier lowering mutants are still killed on the reworked replay, and so are 7 new ones.
- The choice was (a), events in the replay, over (b), outputs only at the end. The reason was PLAN-2026-10 §3's mid-run events. It is
  recorded for the user to revisit.

## 3. What went wrong, and what it teaches

Each item is in `backlog/RC-02.md`'s log, with its correction where one applies.

1. **The plan's design for outputs, `Prog.outs`, would have touched about 70 call sites.** A command, `emitB`, was additive. Before
   designing, I counted the call sites; that made the choice clear.
2. **The replay had no events.** This was found only when the lowering's proof was attempted. **Lesson: a framework's unstated assumption, here
   "events happen only at exit", shows up only when the first construct needs otherwise.**
3. **Harness gaps, three of them, each of the same kind: a check that passes for a reason other than the one it states.**
   - In `rv_diff.py`, inserting `sb` silently retargeted the anchor of "a faulting lbu leaks none". This is the second time; RC-01 step 3a had
     the first.
   - Expected deviations passed on any difference, so "write to any descriptor" survived.
   - `ctout_mut.py`'s first version had no baseline, and would have counted every mutant killed had the copy failed. `cfront_mut.py`
     compiled only `CFront.lean`, so mutants of rules witnessed in `Add.lean` would have survived unseen.
4. **Two corrections of record about the vendored source.**
   - The excerpt's lines were ~~354 to 360~~ 355 to 360.
   - `CSrc`'s pin check runs ~~at every build~~ only when `CSrc.lean` is compiled. Lake does not track the vendored files, and a cached build
     passed with `utils.c` changed. The fix is Ring 0, in `TP-01`.
5. **The plan said `noOut` sees that an output happened.** It does not: an observer chooses channels, so `noOut` drops the `"out"` events.
   What shows an output is the leakage. Corrected in the log.
6. **A CI flake, explained.** `conf-typing builds` failed its 15 s budget on the first run after most `l-core` commits: 77, 19, 15 and 19 s.
   The cause, reproduced on demand, is that `ConfTyping/LAdapter.lean` imports `LCore`. `CI-02` records it, with three fixes for the user's
   key.
7. **The budget rule was too strict for real code.** It refused any write to an input. It now refuses writes only to the inputs counters
   read, with a witness each way.

## 4. The trust base of `addC_ct_bytes`, for a real run

RC-01's, unchanged: the Lean kernels and the six that re-check them; `rvLang`, compared with QEMU and not linked to Sail; the ELF wrapper
and the loader; QEMU as the only machine; the kernel's definitions; the vendored text, pinned in an ordinary file until `TP-01`. **Added by
RC-02:**
- **The reading of `sodium_add`** (`RC-02-READING` §3): word casts as the identity, `(unsigned char)` as `& 255`, the stated length 32, and
  `a` and `b` not overlapping. It is believed by testing against clang on 77 pairs, and against arithmetic.
- **`write(1, …)` as the model states it**: compared with QEMU's stdout in `rv_diff.py` and `add_diff.py`, and known to differ from Linux on
  other descriptors and unreadable memory, where the model aborts.

## 5. What is next

S-USABLE's route continues:
- `CAP-01`, the caps;
- `W32-01`, left shifts and 32-bit words;
- `CPP-01`, macros and inline helpers;
- `RC-03`, the first milestone, `crypto_core_hchacha20`.

RC-02 removed none of these. It added the output arrays the milestone needs, and the mid-run events every later function with output
will use.

**Waiting for the user's key**, each in its item:
- the manifest line `fuel_ev` removed, at the merge;
- `CI-02`'s fix;
- `CI-03`, the `l-core` mutant scripts as CI steps;
- `TP-01`, the vendored files and their pins in Ring 0, with the check run on every build;
- `ROUTE2-01`, from S-USABLE. Route 2 rose to about 240 s over RC-02, against 319.
