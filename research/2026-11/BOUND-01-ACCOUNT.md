# BOUND-01: the account (2026-11-06)

The question came from VS-2's account: **over loops only `rel` reached the bytes, and `Cert.bound` cannot state a budget that depends on the
input.** Can a budget over loops reach literal machine code, by the kernel's transfers alone? For counted loops, yes. **The kernel needed one
change, a new shape, made before the lock and on the user's word.** Every pass proof is unchanged in kind: none is about a certificate.

## 1. What now exists

| Step | What | File |
|---|---|---|
| 1 | The seventh shape, `Cert.boundR`: each admissible input has a budget, chosen before the fuel, bounding its cost at every fuel. `PassCert.boundR_transfer`, `bound_iff_boundR`, `boundR_unbounded`, `Lang.Lawful.boundR_finishes`. Three frozen statements (42) | `l-core/LCore/Kernel/` |
| 2 | Counted loops `forN` and `forMax`, as sugar over VS-2's language | `Slice2/For.lean` |
| 3 | The checker's budget, by a potential over frames: `run_pot`, `slice_boundR` | `Slice2/Budget.lean` |
| 4 | The budget on literal RV64 bytes, by transfer: `countUp_bytes_budget`, `capped_bound_bytes` | `Slice2/BoundBytes.lean` |
| 5 | Under QEMU: 110 runs equal the model, all within budget, the check able to fail | `test/bound_diff.py` |
| 5a | A tighter `rvPass` cost transformer: each source step charged its own chunk | `Slice2/Pass.lean` |

**The headline theorem, `countUp_bytes_budget`:** on every admissible input and in every environment, at every fuel, the 104-byte image of a
loop counted by its public input runs at most `8 * (4n + 2) + 5` instructions, where `n` is the public word read back from the bytes. It comes
from the checker's certificate by `boundR_transfer` through VS-2's two passes. `capped`, the same loop with a cap of 4, has plain `bound` on its
bytes: 97 instructions, for every input up to `2^64 - 1`.

**How tight, measured:**

| Program | Source budget | Bytes budget, before 5a | Bytes budget, after | QEMU |
|---|---|---|---|---|
| `countUp` | `4n + 2`, exact | `104n + 78` | `32n + 21` | `19n + 9` |
| `capped` | 23, exact at the cap | 672 | 97 | at most 83 |

About 760 lines of Lean in the slice, and 108 in the kernel and its witnesses. One long session.

## 2. What the kernel needed

**One addition, and no change to anything that existed.** `ring0.lock` gained `Cert.boundR` and `PassCert.liftR`, and **no existing hash
moved**. `boundR_transfer` is three lines, from `cover` and `cost_sim`, like `bound_transfer`.

**Two design points the kernel now holds:**
- **The budget is chosen before the fuel.** The first sketch, in `VS-2-RESEARCH`, chose it after, and then every program has one: the budget
  can be the cost itself. `boundR_late_vacuous` records this, and `boundR_unbounded` refuses any run whose cost grows without limit.
- **The target's budget is a relation, `liftR`**, so no inverse of `enc` is needed. A target input that encodes several source inputs keeps each
  one's budget. One mutant showed a gap there: a lifting that forgot which input a budget came from passed every witness until
  `padPass_budget_exact` pinned it.

**Do not read this as "the kernel is complete".** It has still not met:
- **A budget that depends only on public input, as a general theorem.** It does not lift in general. For `countUp` it holds concretely,
  because the formula reads only the public word, through `wordAt_enc`. A general lift needs `enc` injective, and `LowR` preserved, per pass.
  Neither is proved as a lemma.
- **Nested or general loops.** The checker bounds only counted loops at the top of a body, not nested and not inside an `ite`. A `while` gets
  `rel` and no budget, as before.
- **Time.** The budget counts instructions in `rvLang`, not cycles, caches or speculation. QEMU is not hardware.

## 3. What went wrong, and what it teaches

Each item is in `backlog/BOUND-01.md`'s log, with its correction where one applies.

1. **The shape was wrong in the research note, and right in the kernel, because it was checked in Lean first.** The budget-after-fuel
   sketch is vacuous. `BoundRSketch.lean` found it before any plan was written. **Lesson: a definition the kernel will freeze is checked against
   a refused witness before it is planned around.**
2. **I miscounted the kernel's shapes.** I called `boundR` the sixth when it is the seventh. Corrected of record in two notes.
3. **A mutant survived** (step 1): no witness said that a target budget is that input's own. `padPass_budget_exact` now does.
4. **Two time budgets broke**, for different reasons, and the reasons mattered.
   - *guard-selftest* went over by 3 s on an unchanged script: this machine's process creation had slowed. `CC-01` cut `check-claims`'s
     processes with every verdict unchanged. Its first version was three times slower, from bash pattern matching on a large string.
   - *`lake check`* went over because the kernel-evaluated witnesses really are growing. Its budget was raised from 104 to 130 s, on the user's word.
5. **A placeholder `sorry`** went into `pot_mono` while proving. It was removed before the first check, and it marked a real missing lemma,
   `eval_upd_out`. **Guessed numbers** in the first budget witnesses were refused by `decide`.
6. **My estimate for option A was wrong.** Charging each step the largest frame's size gains almost nothing, since a loop's frame is the whole
   loop. Bounding a step by its own chunk is what tightened it.

## 4. The trust base of `countUp_bytes_budget`, for a real run

VS-2's, unchanged: the Lean kernels and the six that re-check them; `rvLang`, compared with QEMU and not linked to Sail; the ELF wrapper and the
loader; QEMU as the only machine; and the kernel's definitions, now including `Cert.boundR`, which F6 has not locked.

## 5. Recommendations

**On F6.** The lock was waiting for the L-BYTES route, and the user has chosen it: grow `sliceLang`. The kernel has now met loops,
input-dependent addresses, non-termination, and a budget that depends on the input. It needed one additive shape, made before the lock. **I would
lock the kernel's meaning now:** `Cert`, `PassCert`, `Lang`, `Beh` and the transfers. That means extending `ring0.lock`'s closure to the slices'
languages as each one becomes part of L, not before. REL-01 is still open in F6's log, and it is the user's to settle or to defer past the lock.

**On what comes next.** The first row of the vulnerability map on the grown language, through to the bytes, is the step that turns "certificates
reach machine code" into "a property the map names reaches machine code". The review of the repo named that, real code, as what validation most
lacks.

**Smaller, and optional:**
- A general lemma that a public-only budget lifts through passes whose `enc` is injective.
- Nested counted loops in the checker, on `EXPR-02`'s precedent.
- The QEMU tests in CI, VS-1's proposal 3, now five scripts.
