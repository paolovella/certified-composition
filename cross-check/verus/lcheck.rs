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
pub const T_SEQ: u8 = 6;
pub const T_ITE: u8 = 7;

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

// ------------------------------------------------------ programs with branches
//
// The straight-line fragment above is a fold. Branches are where `lcheck` earns
// its keep — the rule that catches `b06` is that BOTH ARMS must end with the same
// outstanding set — and lifting that to the implementation needs one new fact:
// `word_set` is injective on well-formed words. The specification compares SETS;
// the code compares MACHINE WORDS; those are only the same test because no two
// distinct words denote the same set.

pub struct Node { pub tag: u8, pub x: u8, pub l: usize, pub r: usize }

pub open spec fn tree_wf(p: Seq<Node>) -> bool {
    forall |i: int| 0 <= i < p.len() ==> {
        &&& (#[trigger] p[i]).x < NV
        &&& (p[i].tag == T_SEQ || p[i].tag == T_ITE ==>
                p[i].l < p.len() && p[i].r < p.len())
    }
}

/// `ConfTyping.lcheck`, tree form, over sets.
pub open spec fn spec_tree(p: Seq<Node>, i: int, o: Set<nat>, fuel: nat) -> Option<Set<nat>>
    decreases fuel,
{
    if fuel == 0 || i < 0 || i >= p.len() {
        None
    } else if p[i].tag == T_SEQ {
        match spec_tree(p, p[i].l as int, o, (fuel - 1) as nat) {
            None => None,
            Some(o1) => spec_tree(p, p[i].r as int, o1, (fuel - 1) as nat),
        }
    } else if p[i].tag == T_ITE {
        match spec_tree(p, p[i].l as int, o, (fuel - 1) as nat) {
            None => None,
            Some(a) => match spec_tree(p, p[i].r as int, o, (fuel - 1) as nat) {
                None => None,
                Some(b) => if a =~= b { Some(a) } else { None },
            },
        }
    } else {
        spec_step(p[i].tag, p[i].x as nat, o)
    }
}

/// **The fact the branch rule rests on.** Distinct well-formed words denote
/// distinct sets, so comparing words is comparing sets.
pub proof fn word_set_inj(a: u8, b: u8)
    requires wf_word(a), wf_word(b), word_set(a) =~= word_set(b),
    ensures a == b,
{
    assert(word_set(a).contains(0nat) == word_set(b).contains(0nat));
    assert(word_set(a).contains(1nat) == word_set(b).contains(1nat));
    assert(a % 2 == b % 2);
    assert((a / 2) % 2 == (b / 2) % 2);
}

/// The verified checker, branches included.
pub fn tree_impl(p: &Vec<Node>, i: usize, m: u8, fuel: usize) -> (r: Option<u8>)
    requires wf_word(m), tree_wf(p@),
    ensures
        match r {
            Some(m2) => wf_word(m2)
                && spec_tree(p@, i as int, word_set(m), fuel as nat) == Some(word_set(m2)),
            None => spec_tree(p@, i as int, word_set(m), fuel as nat) is None,
        },
    decreases fuel,
{
    if fuel == 0 || i >= p.len() {
        return None;
    }
    let n = &p[i];
    if n.tag == T_SEQ {
        match tree_impl(p, n.l, m, fuel - 1) {
            None => None,
            Some(m1) => tree_impl(p, n.r, m1, fuel - 1),
        }
    } else if n.tag == T_ITE {
        match tree_impl(p, n.l, m, fuel - 1) {
            None => None,
            Some(a) => match tree_impl(p, n.r, m, fuel - 1) {
                None => None,
                Some(b) => {
                    if a == b {
                        proof { assert(word_set(a) =~= word_set(b)); }
                        Some(a)
                    } else {
                        proof {
                            if word_set(a) =~= word_set(b) { word_set_inj(a, b); }
                        }
                        None
                    }
                }
            },
        }
    } else {
        step_impl(n.tag, n.x, m)
    }
}

/// `leakSafe` for programs with branches.
pub fn tree_leak_safe(p: &Vec<Node>, fuel: usize) -> (r: bool)
    requires tree_wf(p@),
    ensures r == (spec_tree(p@, 0, Set::empty(), fuel as nat) == Some(Set::<nat>::empty())),
{
    proof { assert(word_set(0u8) =~= Set::<nat>::empty()); }
    match tree_impl(p, 0, 0u8, fuel) {
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

/// Runtime tree well-formedness, so the tree entry point is total too.
pub fn tree_wf_check(p: &Vec<Node>) -> (r: bool)
    ensures r == tree_wf(p@),
{
    let mut k: usize = 0;
    while k < p.len()
        invariant
            0 <= k <= p.len(),
            forall |i: int| 0 <= i < k ==> {
                &&& (#[trigger] p@[i]).x < NV
                &&& (p@[i].tag == T_SEQ || p@[i].tag == T_ITE ==>
                        p@[i].l < p@.len() && p@[i].r < p@.len())
            },
        decreases p.len() - k,
    {
        let n = &p[k];
        if n.x >= NV {
            assert(!tree_wf(p@)) by { assert(p@[k as int].x >= NV); }
            return false;
        }
        if (n.tag == T_SEQ || n.tag == T_ITE) && (n.l >= p.len() || n.r >= p.len()) {
            assert(!tree_wf(p@)) by { assert(p@[k as int].tag == T_SEQ || p@[k as int].tag == T_ITE); }
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

/// A binary that runs. The straight-line cases go through the fold; `b06` and its
/// repair go through the branch rule.
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

    // corpus/ext/b06 — CWE-401: alloc, then one arm frees and the other does not.
    let b06: Vec<Node> = vec![
        Node { tag: 6, x: 0, l: 1, r: 2 },
        Node { tag: 1, x: 0, l: 0, r: 0 },
        Node { tag: 7, x: 0, l: 3, r: 4 },
        Node { tag: 0, x: 0, l: 0, r: 0 },
        Node { tag: 2, x: 0, l: 0, r: 0 },
    ];
    // the repair: both arms free.
    let b06_fixed: Vec<Node> = vec![
        Node { tag: 6, x: 0, l: 1, r: 2 },
        Node { tag: 1, x: 0, l: 0, r: 0 },
        Node { tag: 7, x: 0, l: 3, r: 4 },
        Node { tag: 2, x: 0, l: 0, r: 0 },
        Node { tag: 2, x: 0, l: 0, r: 0 },
    ];
    println!("{:<38} {}", "b06 (CWE-401)", verdict_tree(&b06));
    println!("{:<38} {}", "b06, repaired", verdict_tree(&b06_fixed));
}

fn verdict_tree(p: &Vec<Node>) -> &'static str {
    if tree_wf_check(p) {
        if tree_leak_safe(p, 16) { "ACCEPT" } else { "REFUSE" }
    } else {
        "MALFORMED"
    }
}
