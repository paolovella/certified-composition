use vstd::prelude::*;

verus! {

spec fn double(n: nat) -> nat { 2 * n }

fn double_impl(n: u32) -> (r: u32)
    requires n < 1000,
    ensures r as nat == double(n as nat),
{
    n + n
}

fn main() {}

}
