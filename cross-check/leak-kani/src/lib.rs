//! An independent adversary against `ConfTyping.leakSafe_sound`.
//!
//! This is NOT a re-proof. It is an attack on the gap between the Lean theorem and
//! the intent — a modelling error, which is the class of error Lean cannot see.
//! `uexec`'s memory fragment and `lcheck` are re-implemented here from the Lean,
//! by hand, and Kani searches exhaustively over symbolic programs for one that
//! `leakSafe` ACCEPTS and that LEAKS.
//!
//! Faithfulness, stated so the kill criterion can be applied:
//!   * modelled: store (var -> address), `live`, `freed`, `fresh`, `dead`, and
//!     `pickAddr` reusing a freed address before taking a fresh one;
//!   * omitted: `heap`, `sstore`, `sink`, `auth`, `reads`, `hlab`. None of these is
//!     read or written by the `live` transitions, so none can change whether an
//!     address is allocated. `hop .store` and `memop .deref` are omitted for the
//!     same reason — they touch `heap` and `dead`, never `live` or the pointer store.
//!   * `loop` IS modelled, bounded: the body runs 0..MAXITER times, chosen
//!     symbolically. `uexec` recurses on fuel and terminates when the guard is
//!     false; here the number of iterations is a symbolic value the adversary
//!     picks, which covers every run `uexec` could take up to that bound.

pub const NN: usize = 5; // program nodes
pub const NV: usize = 2; // variables
pub const NA: u8 = 3;    // distinct addresses

pub const T_SKIP: u8 = 0;
pub const T_ALLOC: u8 = 1;
pub const T_FREE: u8 = 2;
pub const T_ASSIGN: u8 = 3;
pub const T_LOAD: u8 = 4;
pub const T_CHECK: u8 = 5;
pub const T_SEQ: u8 = 6;
pub const T_ITE: u8 = 7;
pub const T_LOOP: u8 = 8;

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Node {
    pub tag: u8,
    pub x: u8, // variable written / freed
    pub l: u8,
    pub r: u8,
}

/// Children strictly increase, so the tree is finite and acyclic.
pub fn well_formed(p: &[Node; NN]) -> bool {
    let mut i = 0;
    while i < NN {
        let n = p[i];
        if n.tag > T_LOOP {
            return false;
        }
        if (n.x as usize) >= NV {
            return false;
        }
        if n.tag == T_SEQ || n.tag == T_ITE {
            let l = n.l as usize;
            let r = n.r as usize;
            if l <= i || l >= NN || r <= i || r >= NN {
                return false;
            }
        }
        if n.tag == T_LOOP {
            let l = n.l as usize;
            if l <= i || l >= NN {
                return false;
            }
        }
        i += 1;
    }
    true
}

// ---------------------------------------------------------------- the checker

/// `lcheck`, over a bitmask of tracked variables. `None` is a refusal.
pub fn lcheck(p: &[Node; NN], i: usize, o: u8, fuel: usize) -> Option<u8> {
    if fuel == 0 || i >= NN {
        return None;
    }
    let n = p[i];
    let bit = 1u8 << n.x;
    match n.tag {
        T_SKIP | T_CHECK => Some(o),
        T_ASSIGN | T_LOAD => {
            if o & bit != 0 {
                None
            } else {
                Some(o)
            }
        }
        T_ALLOC => {
            if o & bit != 0 {
                None
            } else {
                Some(o | bit)
            }
        }
        T_FREE => {
            if o & bit != 0 {
                Some(o & !bit)
            } else {
                None
            }
        }
        T_SEQ => match lcheck(p, n.l as usize, o, fuel - 1) {
            Some(o1) => lcheck(p, n.r as usize, o1, fuel - 1),
            None => None,
        },
        T_ITE => {
            // both arms must end with the same tracked set
            match (
                lcheck(p, n.l as usize, o, fuel - 1),
                lcheck(p, n.r as usize, o, fuel - 1),
            ) {
                (Some(a), Some(b)) if a == b => Some(a),
                _ => None,
            }
        }
        _ => {
            // LOOP: the body must be a fixpoint of the tracked set
            match lcheck(p, n.l as usize, o, fuel - 1) {
                Some(o1) if o1 == o => Some(o),
                _ => None,
            }
        }
    }
}

/// `leakSafe`: nothing tracked at the start, nothing tracked at the end.
pub fn leak_safe(p: &[Node; NN]) -> bool {
    matches!(lcheck(p, 0, 0, NN), Some(0))
}

// ------------------------------------------------------------- the semantics

#[derive(Clone, Copy)]
pub struct St {
    pub store: [i8; NV], // -1 = no address
    pub live: u8,        // bitmask over addresses
    pub freed: u8,       // bitmask: retired, reusable
    pub fresh: u8,       // next never-used address
    pub dead: bool,
}

impl St {
    pub fn new() -> St {
        St { store: [-1; NV], live: 0, freed: 0, fresh: 0, dead: false }
    }
}

/// `pickAddr`: reuse a freed address before taking a fresh one.
fn pick_addr(st: &St) -> Option<u8> {
    let mut a = 0u8;
    while a < NA {
        if st.freed & (1 << a) != 0 {
            return Some(a);
        }
        a += 1;
    }
    if st.fresh < NA {
        Some(st.fresh)
    } else {
        None
    }
}

pub const MAXITER: u8 = 2;

/// `uexec`'s memory fragment. `br` supplies branch decisions, `iters` loop counts.
pub fn exec(p: &[Node; NN], i: usize, st: &mut St, br: &[bool; NN], iters: &[u8; NN], fuel: usize) {
    if fuel == 0 || i >= NN {
        return;
    }
    let n = p[i];
    let v = n.x as usize;
    match n.tag {
        T_SKIP => {}
        T_CHECK => {
            // a refused check aborts; after that every command is a no-op
            if !st.dead && br[i] {
                st.dead = true;
            }
        }
        T_ALLOC => {
            if !st.dead {
                if let Some(a) = pick_addr(st) {
                    if st.freed & (1 << a) != 0 {
                        st.freed &= !(1 << a);
                    } else {
                        st.fresh += 1;
                    }
                    st.live |= 1 << a;
                    st.store[v] = a as i8;
                }
            }
        }
        T_FREE => {
            if !st.dead {
                let a = st.store[v];
                if a >= 0 && st.live & (1 << a) != 0 {
                    st.live &= !(1 << a);
                    st.freed |= 1 << a;
                } else {
                    st.dead = true;
                }
            }
        }
        T_ASSIGN => {
            if !st.dead {
                st.store[v] = -1;
            }
        }
        T_LOAD => {
            if !st.dead {
                st.store[v] = -1;
            }
        }
        T_SEQ => {
            exec(p, n.l as usize, st, br, iters, fuel - 1);
            exec(p, n.r as usize, st, br, iters, fuel - 1);
        }
        T_ITE => {
            if br[i] {
                exec(p, n.l as usize, st, br, iters, fuel - 1);
            } else {
                exec(p, n.r as usize, st, br, iters, fuel - 1);
            }
        }
        _ => {
            // LOOP: run the body `iters[i]` times, a symbolic count.
            let mut t = 0u8;
            while t < iters[i] && t < MAXITER {
                exec(p, n.l as usize, st, br, iters, fuel - 1);
                t += 1;
            }
        }
    }
}

// ------------------------------------------------------------------ the attack

#[cfg(kani)]
mod attack {
    use super::*;

    /// **The adversary.** If `leakSafe` accepts a program, then every completing run
    /// of it must end with nothing allocated. A counterexample is a defect in
    /// `LeakCert.lean`.
    #[kani::proof]
    #[kani::unwind(8)]
    fn accepted_programs_do_not_leak() {
        let p: [Node; NN] = kani::any();
        kani::assume(well_formed(&p));
        kani::assume(leak_safe(&p));

        let br: [bool; NN] = kani::any();
        let mut st = St::new();
        let iters: [u8; NN] = kani::any();
        exec(&p, 0, &mut st, &br, &iters, NN);

        if !st.dead {
            assert!(st.live == 0, "leakSafe accepted a program that leaks");
        }
    }

    /// **Teeth, part two — the one that matters.** `accepted_programs_do_not_leak`
    /// would pass vacuously if `leakSafe` only ever accepted programs that never
    /// allocate. Refuting this shows the accepted set contains programs that really
    /// do allocate and complete: a witness is expected, so FAILURE here is success.
    #[kani::proof]
    #[kani::unwind(8)]
    fn accepted_programs_can_allocate() {
        let p: [Node; NN] = kani::any();
        kani::assume(well_formed(&p));
        kani::assume(leak_safe(&p));
        let br: [bool; NN] = kani::any();
        let mut st = St::new();
        let iters: [u8; NN] = kani::any();
        exec(&p, 0, &mut st, &br, &iters, NN);
        assert!(st.dead || st.fresh == 0, "witness: an accepted program that allocates");
    }

    /// Teeth: the search space really does contain leaking programs, so a passing
    /// run above is not vacuous.
    #[kani::proof]
    #[kani::unwind(8)]
    fn some_program_leaks() {
        let p: [Node; NN] = kani::any();
        kani::assume(well_formed(&p));
        let br: [bool; NN] = kani::any();
        let mut st = St::new();
        let iters: [u8; NN] = kani::any();
        exec(&p, 0, &mut st, &br, &iters, NN);
        // refuted by a leaking witness, which is what we want to see
        assert!(st.dead || st.live == 0, "witness: a program that leaks");
    }
}

#[cfg(test)]
mod concrete {
    use super::*;

    fn skip() -> Node { Node { tag: T_SKIP, x: 0, l: 0, r: 0 } }

    /// `alloc p ; free p` — the simplest program that allocates and is accepted.
    #[test]
    fn accepted_and_allocates() {
        let p: [Node; NN] = [
            Node { tag: T_SEQ, x: 0, l: 1, r: 2 },
            Node { tag: T_ALLOC, x: 0, l: 0, r: 0 },
            Node { tag: T_FREE, x: 0, l: 0, r: 0 },
            skip(),
            skip(),
        ];
        assert!(well_formed(&p));
        assert!(leak_safe(&p), "alloc;free must be accepted");
        let mut st = St::new();
        exec(&p, 0, &mut st, &[false; NN], &[0u8; NN], NN);
        assert!(!st.dead, "must complete");
        assert_eq!(st.fresh, 1, "must actually allocate");
        assert_eq!(st.live, 0, "must not leak");
    }

    /// `while c { alloc x }` — the unbounded leak. Must be REFUSED, and it really
    /// does leak when the body runs at least once.
    #[test]
    fn loop_alloc_is_refused() {
        let mut p: [Node; NN] = [skip(); NN];
        p[0] = Node { tag: T_LOOP, x: 0, l: 1, r: 0 };
        p[1] = Node { tag: T_ALLOC, x: 0, l: 0, r: 0 };
        assert!(well_formed(&p));
        assert!(!leak_safe(&p), "while-loop that only allocates must be refused");
        let mut st = St::new();
        let mut iters = [0u8; NN];
        iters[0] = 1;
        exec(&p, 0, &mut st, &[false; NN], &iters, NN);
        assert!(!st.dead && st.live != 0, "and it really leaks");
    }

    /// `while c { alloc x ; free x }` — balanced, so the body is a fixpoint.
    #[test]
    fn loop_balanced_is_accepted() {
        let mut p: [Node; NN] = [skip(); NN];
        p[0] = Node { tag: T_LOOP, x: 0, l: 1, r: 0 };
        p[1] = Node { tag: T_SEQ, x: 0, l: 2, r: 3 };
        p[2] = Node { tag: T_ALLOC, x: 0, l: 0, r: 0 };
        p[3] = Node { tag: T_FREE, x: 0, l: 0, r: 0 };
        assert!(well_formed(&p));
        assert!(leak_safe(&p), "balanced loop must be accepted");
        let mut st = St::new();
        let mut iters = [0u8; NN];
        iters[0] = 2;
        exec(&p, 0, &mut st, &[false; NN], &iters, NN);
        assert!(!st.dead && st.live == 0, "and it does not leak");
    }

    /// `b06`: alloc, then one arm frees and the other does not. Must be REFUSED.
    #[test]
    fn b06_is_refused() {
        let p: [Node; NN] = [
            Node { tag: T_SEQ, x: 0, l: 1, r: 2 },
            Node { tag: T_ALLOC, x: 0, l: 0, r: 0 },
            Node { tag: T_ITE, x: 0, l: 3, r: 4 },
            skip(),
            Node { tag: T_FREE, x: 0, l: 0, r: 0 },
        ];
        assert!(well_formed(&p));
        assert!(!leak_safe(&p), "b06 must be refused");
        // and it really does leak on the skip arm
        let mut st = St::new();
        exec(&p, 0, &mut st, &[true; NN], &[0u8; NN], NN);
        assert!(!st.dead && st.live != 0, "b06 leaks on the skip arm");
    }
}
