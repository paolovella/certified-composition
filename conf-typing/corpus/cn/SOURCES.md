# CN — the foreign certificate stage B receives

Not written by me, and not written for this repo. The C below is transcribed verbatim from
the CN tutorial's own exercise files. `ConfTyping/CNReceive.lean` models *what CN's
ownership clause asserts* about these functions; it does not re-verify any C, and it does
not parse CN's output.

## The tool

**CN** — a separation-logic refinement-type verifier for real C, built on the **Cerberus**
C semantics.

> Christopher Pulte, Dhruv C. Makwana, Thomas Sewell, Kayvan Memarian, Peter Sewell, Neel
> Krishnaswami. *CN: Verifying Systems C Code with Separation-Logic Refinement Types.*
> POPL 2023 / PACMPL 7(POPL). <https://dl.acm.org/doi/abs/10.1145/3571194>

Two facts about CN are load-bearing for the ledger in `CNReceive.lean`, and both come from
the paper as summarised on its own pages:

1. It **builds on the Cerberus semantics for C**, rather than on an ad-hoc model.
2. Its type system is engineered so obligations land in a **decidable SMT fragment**
   (quantifier-free, with uninterpreted functions, linear integer arithmetic, records and
   extensional arrays), discharged by an **SMT backend**.

Those are the three entries of `CNTrust.fixedBase`: Cerberus's C semantics, CN's own
refinement type system, and the solver. The point of `CNTrust.needs` is that a given
result need not rest on all three — a purely structural ownership obligation never reaches
the solver.

Tutorial: <https://rems-project.github.io/cn-tutorial/>

## The syntax, as it actually is

CN's ownership resource is written `take <name> = RW<T>(p)`. Note **`RW`**, not the
`Owned<T>` of older write-ups — checked against the current tutorial rather than recalled.

## `bcp_framerule.c` — the frame rule, verbatim

Source: `src/exercises/bcp_framerule.c`, rems-project/cn-tutorial.

```c
void incr_first (unsigned int *p, unsigned int *q)
/*@ requires take pv = RW<unsigned int>(p);
    ensures take pv_ = RW<unsigned int>(p);
            pv_ == pv + 1u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}

void incr_first_frame (unsigned int *p, unsigned int *q)
/*@ requires take pv = RW<unsigned int>(p);
             take qv = RW<unsigned int>(q);
    ensures take pv_ = RW<unsigned int>(p);
            take qv_ = RW<unsigned int>(q);
            pv_ == pv + 1u32;
            qv_ == qv;
@*/
{
  incr_first(p, q);
}
```

**This file is why stage B is anchored here.** `incr_first` owns `p` and *not* `q` — `q` is
an argument it never takes ownership of. `incr_first_frame` owns both, calls `incr_first`,
and its postcondition `qv_ == qv` is not proved by its body: the body is one call. It is
**derived by the frame rule** from the callee's footprint. That derivation is what
`cn_frame_rule` and `cn_untouched_outside` model, and it is the reason a footprint is the
right thing to make into a grade.

## `pointers` tutorial — the ownership clause in isolation

Source: <https://rems-project.github.io/cn-tutorial/getting-started/tutorials/pointers/>

```c
unsigned int read (unsigned int *p)
/*@ requires take P = RW<unsigned int>(p);
    ensures take P_post = RW<unsigned int>(p);
            return == P;
            P_post == P;
@*/
{
  return *p;
}

void incr (unsigned int *p)
/*@ requires take P = RW<unsigned int>(p);
    ensures take P_post = RW<unsigned int>(p);
            P_post == P + 1u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n+1;
  *p = m;
}
```

`incrAt` in `CNReceive.lean` is `incr` at an abstract location.

## What was modelled, and what was dropped

| CN asserts | stage B | why |
|---|---|---|
| `take pv = RW<unsigned int>(p)` — the footprint | **received**, as `ModifiesOnly` | it is the part that composes; union is the composition |
| `pv_ == pv + 1u32` — the functional post | **not modelled** | it does not accumulate under composition the way a footprint does; it is per-function, and stage B is about the composition law |
| `qv_ == qv` — the framed-off part | **derived**, `cn_untouched_outside` | the whole point: it should fall out of the algebra, not be assumed |

## The reception gap, stated plainly

Nothing here proves that CN's `take pv = RW<unsigned int>(p)` *implies*
`ModifiesOnly f (fun l => l = p)`. That implication is CN's soundness theorem over
Cerberus's memory object model, and restating it is not this repo's business. The
encoding is done **by hand**, and it is an assumption of the same kind as
`Bridge.ofKernel` taking a Dobrushin coefficient as a hypothesis rather than computing it.

Two further gaps worth naming rather than burying:

- `CStore = CLoc → Nat` is a **total map**, not Cerberus's memory object model. Provenance,
  alignment, object lifetime and `uchar` representation all disappear. The modelled claim
  is only as good as that abstraction.
- The footprint is a location set, so **CN's `each(...)` array resources** (see
  `src/exercises/array_swap.c`) are expressible only as the set of locations they range
  over. Nothing here handles the quantified resource itself.
