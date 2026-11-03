# Carrying speculation guarantees through a compiler: what the field does, 2026-11-03

Asked for by the user, to improve the window-aware pass relation in `backlog/L-UNIFY.md`.

**Finding.** The field's closest work has no window in the source semantics. The attacker picks each
branch. Adopting that removes the problem L-UNIFY's design was built around, and shows that the fix it
proposed weakens the attacker in the wrong place.

## How far this was read

| Source | Read |
|---|---|
| Arranz Olmos et al., POPL 2025 | **Not the paper**: ePrint, HAL and ACM refused the fetch. The authors' seminar slides and the abstract |
| Barthe et al., POPL 2020; Barthe et al., CCS 2021 | Abstracts, and the slides' summary of CT-simulations. Not the papers |
| Guarnieri et al., Spectector | Full text searched; §V.C and Theorem 1 read |
| Guarnieri et al., Hardware-Software Contracts | Full text searched; execution modes read |
| Fabian et al., "Do You Even Lift?", POPL 2025 | Technical report searched; the lifting theorem's statement read |
| 2026 follow-up, arXiv 2603.29800 | Searched; the always-mispredict template and its properties read |
| van der Wall and Meyer, SNIP, POPL 2025 | The conference abstract only |

Anything below about the POPL 2025 proof comes from the slides, and needs checking against the paper
before L-UNIFY relies on it.

## What the field does

**Directives, no window.** Arranz Olmos et al. let the attacker control speculation through a stream of
directives: `step`, `force b`, `mem a i`. States carry a mis-speculation bit. Their slides state a
"no-backtrack theorem": reasoning about Spectre needs no rollback. A program is secure when, for every
directive stream, related inputs give equal observations. The idea of attacker-chosen directives comes
from Cauligi et al.

**The preservation theorem.** From the slides: if there are `Td` and `To` such that every target run
under directives `D`, with observations `Ot`, has a source run under `Td(D)` with `Ot = To(Os)`, then for
any relation on inputs a secure `P` compiles to a secure `Q`. `To` is the leakage transformer of the
earlier CT-simulation work, and it is what L's `det` says in two-run form. `Td` is the new part. The
proof composes over passes. Passes proved: constant folding and propagation, loop peeling, register
allocation without spilling, with identity transformers; dead assignment and dead branch elimination,
which introduce directives and eliminate leakage; array reuse, array concatenation and linearization.

**Where windows live.** In Spectector and in hardware-software contracts, at the hardware boundary.
Spectector's Theorem 1: a program is secure for all prediction oracles with window at most `w` exactly
when it is secure under an always-mispredict semantics at `w`. Contracts pair an execution mode with an
observer. So the window is a parameter of what a processor promises, which is what PH5 needs.

**Nesting.** Spectector's Example 6: a correct prediction of a nested branch can leak more than a
misprediction, since a long nested arm can use up the window before the leak. Its always-mispredict
semantics gives a nested transaction its own budget so that the outer one continues afterwards. Hiding
what happens after a nested branch is therefore the wrong direction.

**Passes that break this.** Arranz Olmos et al. report failures in GCC and in Jasmin from spilling and
from stack array reuse. Their semantics lets a mis-speculated load read any location, so fresh arrays
count as transiently secret. SNIP reports a weakness in register allocation, confirmed in a mainstream
compiler on libsodium code. L's later passes (P1, P2-P7) are of these kinds.

**Adding more speculation later.** Fabian et al. lift a compiler's guarantee from a base semantics to one
with more mechanisms, given three properties: security in the base, independence in the extension, and
safe nesting. That is the route for v2 and v4, without new compilation proofs.

## What this means for L

**1. The root cause of the `det` failure is that the machine hides transient branches.** `transRun` runs
a nested `ite` as one silent command, so the source's view does not show which arm ran. A real attacker
measures it. L-UNIFY's probe failed because the source's views agreed only for that reason.

**2. L-UNIFY's proposed fix is the wrong direction.** Ending the window at a nested branch would lose the
leak in Example 6's shape. The probe `ex6` shows today's `ucmdLangW` finds it at window 2, with the secret
as the address.

**3. Replace the window with directives.** A prototype, `DirProbe.lean` beside this note, adds a stream
to `urunS`: at each `ite` and `loop` the attacker forces the arm or lets it run correctly. An empty
stream is the architectural run. Results on the prototype, which is an evaluation and proves nothing:

| Probe | Result |
|---|---|
| The fuel-cap program, `n` = 29, 30, 40, inner branch forced either way | source and target views are equal, and agree across secrets |
| The same, inner branch correct | source's views differ across secrets, so `det` asks nothing, and each target view equals its source view |
| `ex6`, outer forced, inner correct | the secret appears as the address |
| `brWitness`, which `bcheck` accepts, and its `split`, on 7 directive streams | agree on all 7 |
| `transientUse` and `gadget`, which `bcheck` refuses | differ on the 3 streams that force the outer branch true |

**4. What it costs.**
- **`bound` no longer holds on every input**, because the attacker can force a loop forever. It holds on
  the architectural streams, which are `ucmdLangS`.
- **Trace certificates need a rule:** events only count while not mis-speculating, so a forced `access`
  is not a read. That needs the mis-speculation bit, and is a design decision of its own.
- **`Split.lean`'s proofs are over `urunS`,** so its 985 lines need the stream threaded through. It looks
  mechanical, and this is not measured.
- **Its strength against `ucmdLangW` is unproved here.** The slides' no-backtrack theorem is about their
  language. `ucmdLangW` and `bcheck_relW` should stay until L has its own proof.
- **Memory directives are not modelled.** UCmd has no arrays, so the `mem` directive has nothing to act
  on. PH5 must add it, and with it fresh memory as transiently secret.

**5. A kernel question this raises, for later passes.** `PassCert.enc : S.In → T.In` does not take the
program. `split` keeps every branch, so its transformer is the identity. A pass that removes or adds
branches has a directive transformer that depends on the program, and the slides' `Td` goes from target
to source. So `enc` may be too weak for such passes, once directives are in `In`. Not a problem for
`splitPass`. It is a Ring 0 question to answer before F6 locks `PassCert`, and it is not settled here.

`P1` shows why it has not come up. `slotLang`'s input is still a named `Store`, and its `Prog` carries the
table (`p1Pass`), so a program-dependent encoding hides inside the target program. That works for a
table, as a loader's layout would. It does not work for directives: the target's input would stay in the
source's format, so a certificate on it would not range over the choices a target attacker has. That is
the failure F3 fixed for inputs outside `enc`'s image. The candidate fix is `enc : S.Prog → S.In → T.In`.

## Recommendation

Change L-UNIFY from a window-indexed family to one language whose input includes a directive stream, and
keep the window for PH5's hardware contract. The first steps, each able to stop the item:
1. Read the POPL 2025 paper itself. The user can supply it, or a browser session can fetch it.
2. Prove `bcheck`'s `rel` on the directive machine: a lockstep proof like `runS_same`, where a forced
   branch needs no guard agreement. Riskiest for the design.
3. Settle the `enc` question against one pass that changes branches, on paper.

## Sources

- [Preservation of Speculative Constant-Time by Compilation, POPL 2025, abstract](https://eprint.iacr.org/2024/1203), and [the authors' slides](https://members.loria.fr/VLaporte/files/Prosecco2024_SCTP.pdf)
- [Formal Verification of a Constant-Time Preserving C Compiler, POPL 2020](https://eprint.iacr.org/2019/926)
- [Structured Leakage and Applications to Cryptographic Constant-Time and Cost, CCS 2021](https://eprint.iacr.org/2021/650)
- [Constant-Time Foundations for the New Spectre Era, Cauligi et al.](https://arxiv.org/pdf/1910.01755), seen through search results only
- [Spectector: Principled Detection of Speculative Information Flows](https://arxiv.org/pdf/1812.08639)
- [Hardware-Software Contracts for Secure Speculation](https://arxiv.org/abs/2006.03841)
- [Do You Even Lift? Strengthening Compiler Security Guarantees Against Spectre Attacks, POPL 2025](https://arxiv.org/pdf/2405.10089)
- [Always-mispredict template for composed speculation, 2026](https://arxiv.org/abs/2603.29800)
- [SNIP: Speculative Execution and Non-Interference Preservation for Compiler Transformations, POPL 2025](https://popl25.sigplan.org/details/POPL-2025-popl-research-papers/51/SNIP-Speculative-Execution-and-Non-Interference-Preservation-for-Compiler-Transforma)
- [Exorcising Spectres with Secure Compilers, CCS 2021](https://arxiv.org/abs/1910.08607v3), seen through search results only
