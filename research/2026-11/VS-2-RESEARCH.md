# After VS-2: what others did about the two open decisions (2026-11-06)

VS-2's account left the user two decisions: whether L's certificates should bound running time over loops, and which L-BYTES route to take. This
note reports what published work says about each. **Sources were read at the level of abstracts, project pages and search summaries, not full papers.**
Where a claim below rests on more than that, it says so, and where it rests on less, it is marked *unverified*.

## 1. A correction this research forces

Both accounts say `UCmd`'s unbounded integers ~~cannot reach a machine~~ (VS-1 §6, VS-2 §6, and `backlog/L-BYTES.md`'s entry of 2026-11-06). **That is
false as stated.** CakeML's generated machine code includes "a verified arbitrary precision arithmetic (bignum) library" in its verified runtime, and
targets RISC-V among five architectures (Tan, Myreen, Kumar, Fox, Owens, Norrish, *The verified CakeML compiler backend*, JFP 2019).

What is true is narrower, and it is the real argument. A bignum's running time and the addresses it touches depend on how large it is. For a secret
value, those are exactly what `rel` observes: PCs, addresses and cost. A bignum runtime that hid them would need a fixed number of limbs, and that is a
bounded integer again. So **for secret data, lowering `UCmd` means a constant-time bignum runtime, or bounding the integers.** Bounding them is what
`sliceLang` already does. The preference for growing `sliceLang` stands, for this stated reason.

## 2. Budgets over loops

**What VS-2 has already, and what the literature calls it.** `rel` compares the cost at every fuel, so on two inputs with the same public part the
machine takes the same number of instructions. The running time is a function of the public input, at instruction granularity. That is the "cost"
half of constant-time. What is missing is a **number**: an upper bound that a reader can check.

| Work | How the bound survives compilation | What it suggests for L |
|---|---|---|
| CerCo, *Certified Complexity* (FP7, 2010 to 2014) | Cost labels are inserted at C program points, and the proof shows the compiled code's cost is exactly what the labels say, concretely, on an 8051 | The bound lives in the source, as annotations. The compiler's proof makes the annotations exact |
| Carbonneaux, Hoffmann, Ramananandro, Shao, *End-to-end verification of stack-space bounds for C programs* (PLDI 2014) | Weighted event traces of calls and returns, which a CompCert-based compiler preserves. Bounds are proved at the C level in a quantitative Hoare logic. The automatic analyser handles non-recursive code only | Cost as a property of traces, carried by the same proof as correctness. Close to `Xform.cost` |
| Carbonneaux, Hoffmann, Shao, *Compositional certified resource bounds* (PLDI 2015, tool C4B) | Bounds inferred by amortised analysis and abstract interpretation, reduced to linear programming, and connected to that quantitative logic | Bounds for loops can be inferred, linear in the inputs, without a person writing them |
| Hoffmann and others, RAML (AARA) | Multivariate polynomial bounds in the *sizes* of inputs, by LP. The user gives the maximal degree | The budget is a function of the input, by design. Whether RAML emits machine-checked certificates was not confirmed |
| Barthe, Grégoire, Laporte, Priya, *Structured leakage and applications to cryptographic constant-time and cost* (CCS 2021) | Leakage transformers map source leakage to target leakage, shown on Jasmin, with preservation proved for constant-time **and cost** | The nearest to L's design: `Xform.lk` is a leakage transformer, and cost rides on the same object. *How their cost relates to leakage was not read: the PDF was refused, and the abstract does not say* |

**What this suggests, as a design to decide, not to build yet.**
- **A sixth shape whose budget may depend on the input, stated as a relation so that no inverse of `enc` is needed:**
  `boundR L R p := ∀ n i, L.Adm i → ∃ k, R i k ∧ (L.run n p i).cost ≤ k`. Its transfer would take `R` to
  `R' u k := ∃ i k', enc i = u ∧ R i k' ∧ k = t.cost k'`, from `cover` and `cost_sim`, as `bound_transfer` does now. A budget that may depend only on the public
  part is `R` respecting `lowIn`. That costs one more condition and no new idea. *This is a sketch: it has not been checked in Lean.*
- **Who supplies `R`.** CerCo and the PLDI 2014 work put bounds in the source and let the compiler carry them. C4B and RAML infer them. For L, the
  checker would infer them, as `costOf` does now. That needs loops it can bound. **`EXPR-02` already did this in `conf-typing`:** nested counted loops,
  checked by `bcheck`, fuel-indexed so that `decide` still reduces. The cheapest route is a counted loop, `for e body`, with `e` evaluated once and public,
  and budget `e * costOf body` plus a constant, beside `while`, which keeps `rel` and no budget.
- **Granularity.** Every work above counts something like instructions or stack words, as `rvLang` does. None reaches cycles, caches or speculation.
  Nor would L's, which is the limit VS-1 already states.

## 3. Termination, which `spin` and `secretLoop` touched

Kashyap, Wiedermann and Hardekopf (IEEE S&P 2011) compare definitions of timing- and termination-sensitive noninterference, and find that many proofs
use weaker ones than the attacks require. VS-2's `rel` compares outcome and cost at every fuel, which is the strong, termination- and time-sensitive form at
instruction granularity. That is why `secretLoop`'s binary is refuted through **whether** it finishes as well as when. The search found no compiler
proof that preserves all three of time, termination and noninterference together. Sison and Murray (JFP 2021) carry noninterference to assembly for
concurrent programs. Whether they treat termination was not confirmed.

## 4. What this changes

1. **A correction of record** in VS-1's and VS-2's accounts and in `L-BYTES`, as §1 states.
2. **The budget decision gets a concrete option:** the `boundR` shape, with a counted loop on the `EXPR-02` precedent. It is still the user's decision,
   and still a G-0 change if taken.
3. **No change to the F6 recommendation.** The `boundR` shape would be additive. Under a lock it needs the user's key, as every kernel change does, so it
   is not a reason to lock sooner or later.

## Sources

- CerCo: [arXiv 1010.1697](https://arxiv.org/pdf/1010.1697), [CORDIS D5.1](https://cordis.europa.eu/docs/projects/cnect/1/243881/080/deliverables/002-D51.pdf), [Edinburgh project page](https://publish.lfcs.inf.ed.ac.uk/research/mobility+security/), [FOPARA 2013](https://rd.springer.com/content/pdf/10.1007%2F978-3-319-12466-7_1.pdf)
- Stack bounds, PLDI 2014: [FLINT page](https://flint.cs.yale.edu/publications/veristack.html), [paper](https://www.cs.yale.edu/homes/hoffmann/papers/veristack2014.pdf)
- C4B, PLDI 2015: [FLINT page](https://flint.cs.yale.edu/publications/ccrb.html), [paper](https://cs.yale.edu/flint/certikos/publications/ccrb.pdf)
- RAML: [Hoffmann, Wang 2015](https://www.cs.yale.edu/homes/hoffmann/papers/HoffmannW15.pdf), [towards OCaml](https://arxiv.org/pdf/1611.00692)
- CakeML backend, JFP 2019: [Chalmers record](https://research.chalmers.se/en/publication/?id=508594), [Kent repository](https://kar.kent.ac.uk/71304/)
- Constant-time preservation: [Barthe, Grégoire, Laporte, CSF 2018](https://members.loria.fr/VLaporte/files/CSF2018_ConstantTimePreservation.pdf), [ePrint 2019/926](https://eprint.iacr.org/2019/926.pdf), [structured leakage, ePrint 2021/650](https://eprint.iacr.org/2021/650)
- Termination: [Kashyap, Wiedermann, Hardekopf, S&P 2011](https://www.ieee-security.org/TC/SP2011/PAPERS/2011/paper026.pdf), [Sison, Murray, JFP 2021](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/A46AD098BDBBE50665D4094BE8F6D8DD/S0956796821000162a.pdf/verified-secure-compilation-for-mixed-sensitivity-concurrent-programs.pdf)
