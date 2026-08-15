// Stage K — a `lcheck` whose agreement with its specification is itself verified,
// rather than trusted extraction.
//
// The kill criterion for this stage is: *if the Verus spec is a transliteration of
// the Rust rather than of the Lean, it proves the code equals itself.* So the two
// sides are deliberately built on different objects:
//
//   * the SPECIFICATION tracks outstanding allocations as a mathematical
//     `Set<nat>`, and its rules are `ConfTyping.lcheck`'s, clause for clause —
//     `alloc` refuses a variable already tracked and otherwise inserts, `free`
//     demands the variable be tracked and removes it, `assign`/`load` refuse to
//     write over a tracked variable;
//   * the IMPLEMENTATION carries a `u8` machine word.
//
// The theorem is that the word always DENOTES the set. That is a refinement, not
// an identity, and it is what `certcheck`-as-trusted-extraction does not have.

use vstd::prelude::*;

verus! {

pub const NV: u8 = 2;

pub const T_SKIP: u8 = 0;
pub const T_ALLOC: u8 = 1;
pub const T_FREE: u8 = 2;
pub const T_ASSIGN: u8 = 3;
pub const T_LOAD: u8 = 4;
pub const T_CHECK: u8 = 5;

// ---------------------------------------------------------------- the two sides

/// Bit `i` of the machine word, in arithmetic rather than bit-twiddling so the
/// solver can see through it.
pub open spec fn bit_of(m: u8, i: nat) -> bool {
    if i == 0 { m % 2 == 1 } else { (m / 2) % 2 == 1 }
}

/// What a machine word DENOTES. The whole stage rests on this function existing:
/// the implementation manipulates `m`, the specification talks about
/// `word_set(m)`, and they are different objects.
pub open spec fn word_set(m: u8) -> Set<nat> {
    Set::new(|i: nat| i < NV as nat && bit_of(m, i))
}

/// A word is well formed when it uses no bits outside the variable range.
pub open spec fn wf_word(m: u8) -> bool { m < 4 }

// --------------------------------------------------------- the rules, as a spec

/// `ConfTyping.lcheck`'s rules for the non-recursive commands, over sets.
pub open spec fn spec_step(tag: u8, x: nat, o: Set<nat>) -> Option<Set<nat>> {
    if tag == T_SKIP || tag == T_CHECK {
        Some(o)
    } else if tag == T_ASSIGN || tag == T_LOAD {
        if o.contains(x) { None } else { Some(o) }
    } else if tag == T_ALLOC {
        if o.contains(x) { None } else { Some(o.insert(x)) }
    } else if tag == T_FREE {
        if o.contains(x) { Some(o.remove(x)) } else { None }
    } else {
        None
    }
}

// --------------------------------------------------------- the rules, as code

pub fn step_impl(tag: u8, x: u8, m: u8) -> (r: Option<u8>)
    requires wf_word(m), x < NV,
    ensures
        match r {
            Some(m2) => wf_word(m2)
                && spec_step(tag, x as nat, word_set(m)) == Some(word_set(m2)),
            None => spec_step(tag, x as nat, word_set(m)) is None,
        },
{
    let bit: u8 = if x == 0 { 1 } else { 2 };
    let present: bool = if x == 0 { m % 2 == 1 } else { (m / 2) % 2 == 1 };

    assert(present == word_set(m).contains(x as nat));

    if tag == T_SKIP || tag == T_CHECK {
        Some(m)
    } else if tag == T_ASSIGN || tag == T_LOAD {
        if present { None } else { Some(m) }
    } else if tag == T_ALLOC {
        if present {
            None
        } else {
            let m2 = m + bit;
            assert(word_set(m2) =~= word_set(m).insert(x as nat)) by {
                assert forall |i: nat| i < NV as nat implies
                    (bit_of(m2, i) == (bit_of(m, i) || i == x as nat)) by {
                    assert(i == 0 || i == 1);
                }
            }
            Some(m2)
        }
    } else if tag == T_FREE {
        if present {
            let m2 = m - bit;
            assert(word_set(m2) =~= word_set(m).remove(x as nat)) by {
                assert forall |i: nat| i < NV as nat implies
                    (bit_of(m2, i) == (bit_of(m, i) && i != x as nat)) by {
                    assert(i == 0 || i == 1);
                }
            }
            Some(m2)
        } else {
            None
        }
    } else {
        None
    }
}

// ------------------------------------------------- a whole program, straight-line

/// `ConfTyping.lcheck` over a sequence of atomic commands: `seq` is a fold, and a
/// refusal anywhere is a refusal overall.
pub open spec fn spec_lcheck(ops: Seq<(u8, nat)>, o: Set<nat>) -> Option<Set<nat>>
    decreases ops.len(),
{
    if ops.len() == 0 {
        Some(o)
    } else {
        match spec_step(ops[0].0, ops[0].1, o) {
            None => None,
            Some(o1) => spec_lcheck(ops.skip(1), o1),
        }
    }
}

pub open spec fn as_spec_ops(v: Seq<(u8, u8)>) -> Seq<(u8, nat)> {
    v.map(|i: int, p: (u8, u8)| (p.0, p.1 as nat))
}

pub open spec fn ops_wf(v: Seq<(u8, u8)>) -> bool {
    forall |i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).1 < NV
}

/// The verified checker. The loop carries the specification forward as its
/// invariant, so the returned word denotes exactly the set the rules compute.
pub fn lcheck_impl(ops: &Vec<(u8, u8)>, m0: u8) -> (r: Option<u8>)
    requires wf_word(m0), ops_wf(ops@),
    ensures
        match r {
            Some(m) => wf_word(m)
                && spec_lcheck(as_spec_ops(ops@), word_set(m0)) == Some(word_set(m)),
            None => spec_lcheck(as_spec_ops(ops@), word_set(m0)) is None,
        },
{
    let mut m: u8 = m0;
    let mut k: usize = 0;
    proof { assert(as_spec_ops(ops@).skip(0) =~= as_spec_ops(ops@)); }
    while k < ops.len()
        invariant
            0 <= k <= ops.len(),
            wf_word(m),
            ops_wf(ops@),
            spec_lcheck(as_spec_ops(ops@), word_set(m0))
                == spec_lcheck(as_spec_ops(ops@).skip(k as int), word_set(m)),
        decreases ops.len() - k,
    {
        let op = ops[k];
        proof {
            assert(as_spec_ops(ops@).skip(k as int).len() == ops@.len() - k);
            assert(as_spec_ops(ops@).skip(k as int)[0] == (op.0, op.1 as nat));
            assert(as_spec_ops(ops@).skip(k as int).skip(1)
                =~= as_spec_ops(ops@).skip(k as int + 1));
        }
        match step_impl(op.0, op.1, m) {
            None => {
                return None;
            }
            Some(m2) => {
                m = m2;
                k = k + 1;
            }
        }
    }
    proof {
        assert(as_spec_ops(ops@).skip(k as int) =~= Seq::<(u8, nat)>::empty());
    }
    Some(m)
}

/// `ConfTyping.leakSafe`: nothing tracked at the start, nothing tracked at the end.
pub fn leak_safe(ops: &Vec<(u8, u8)>) -> (r: bool)
    requires ops_wf(ops@),
    ensures r == (spec_lcheck(as_spec_ops(ops@), Set::empty()) == Some(Set::<nat>::empty())),
{
    proof { assert(word_set(0u8) =~= Set::<nat>::empty()); }
    match lcheck_impl(ops, 0u8) {
        None => false,
        Some(m) => {
            let e = m == 0;
            proof {
                if m == 0 { assert(word_set(m) =~= Set::<nat>::empty()); }
                else { assert(word_set(m).contains(if m % 2 == 1 { 0nat } else { 1nat })); }
            }
            e
        }
    }
}

/// Runtime validation, so the binary has a total entry point: the verified
/// `leak_safe` has a precondition, and something has to discharge it for real input.
pub fn ops_valid(ops: &Vec<(u8, u8)>) -> (r: bool)
    ensures r == ops_wf(ops@),
{
    let mut k: usize = 0;
    while k < ops.len()
        invariant
            0 <= k <= ops.len(),
            forall |i: int| 0 <= i < k ==> (#[trigger] ops@[i]).1 < NV,
        decreases ops.len() - k,
    {
        if ops[k].1 >= NV {
            assert(!ops_wf(ops@)) by { assert(ops@[k as int].1 >= NV); }
            return false;
        }
        k = k + 1;
    }
    true
}

/// Total: no precondition, so plain Rust can call it.
pub fn leak_safe_total(ops: &Vec<(u8, u8)>) -> (r: bool)
    ensures r ==> spec_lcheck(as_spec_ops(ops@), Set::empty()) == Some(Set::<nat>::empty()),
{
    if ops_valid(ops) { leak_safe(ops) } else { false }
}

}

/// A binary that runs. `(tag, var)` pairs; the verified `leak_safe_total` decides.
fn main() {
    let cases: [(&str, &[(u8, u8)]); 4] = [
        ("alloc p ; free p",                   &[(1, 0), (2, 0)]),
        ("alloc p",                            &[(1, 0)]),
        ("alloc p ; assign p",                 &[(1, 0), (3, 0)]),
        ("alloc p ; alloc q ; free p ; free q", &[(1, 0), (1, 1), (2, 0), (2, 1)]),
    ];
    for (name, ops) in cases.iter() {
        let v: Vec<(u8, u8)> = ops.to_vec();
        let verdict = if leak_safe_total(&v) { "ACCEPT" } else { "REFUSE" };
        println!("{:<38} {}", name, verdict);
    }
}
