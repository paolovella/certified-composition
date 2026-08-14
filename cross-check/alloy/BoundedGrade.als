/*
 * Stage H — Alloy as an independent adversary against `BoundedCert.lean`.
 *
 * Stage F proved, in Lean, that a bounded certificate's grade is the PAIR
 * (bound, growth), composing as
 *
 *     bmul <b2,g2> <b1,g1> = < min b1 (b2 - g1), g1 + g2 >
 *
 * with truncated subtraction. Two claims rest on that: the composition is
 * associative, and the composite bound is NOT a function of the two bounds
 * (`bounded_grade_does_not_factor`).
 *
 * This model restates both over Alloy's own integers and lets a SAT solver look
 * for counterexamples. It is not a re-proof: it is a second opinion from a tool
 * with a different arithmetic, at a stated scope.
 *
 * The second assertion is EXPECTED TO FAIL. That is the point — it is the teeth.
 * An Alloy model in which every check passes has not been shown to be able to
 * refute anything.
 */
module BoundedGrade

open util/integer

/* Truncated subtraction: Nat's `-`, which is where the vacuous grade comes from. */
fun tsub[x, y: Int]: Int { x >= y implies minus[x, y] else 0 }

fun tmin[x, y: Int]: Int { x < y implies x else y }

/* The bound component of `bmul <b2,g2> <b1,g1>`. */
fun cbound[b1, b2, g1: Int]: Int { tmin[b1, tsub[b2, g1]] }

pred nonneg[a, b, c, d, e, f: Int] {
  a >= 0 and b >= 0 and c >= 0 and d >= 0 and e >= 0 and f >= 0
}

/* Alloy's Int is a wrapping bitvector, so `plus` and `minus` can silently
   overflow and produce a counterexample that is an artifact of the MODEL's own
   arithmetic rather than of the law. Keeping every value and every intermediate
   sum well inside bitwidth 6 (-32..31) is what makes the check mean anything. */
pred small[a, b, c, d, e, f: Int] {
  nonneg[a, b, c, d, e, f]
  a <= 7 and b <= 7 and c <= 7 and d <= 7 and e <= 7 and f <= 7
}

/*
 * S1 — associativity of the bound component.
 * Lean: `bmul_assoc`. Expected: no counterexample.
 */
assert S1_BoundAssociative {
  all b1, g1, b2, g2, b3, g3: Int |
    small[b1, g1, b2, g2, b3, g3] implies
      cbound[cbound[b1, b2, g1], b3, plus[g1, g2]]
        = cbound[b1, cbound[b2, b3, g2], g1]
}

/*
 * S2 — `min` alone is not the composite bound.
 * Lean: `min_unsound`, and the witness in `bounded_coupling_witness`.
 * EXPECTED TO FAIL: growth changes the answer.
 */
assert S2_BoundIsMinOfBounds {
  all b1, b2, g1: Int |
    (b1 >= 0 and b2 >= 0 and g1 >= 0) implies cbound[b1, b2, g1] = tmin[b1, b2]
}

/*
 * S3 — the composite bound is a function of the two bounds alone.
 * Lean: `bounded_grade_does_not_factor`.
 * EXPECTED TO FAIL: same bounds, different growth, different answer.
 */
assert S3_BoundFactors {
  all b1, b2, g, g2: Int |
    (b1 >= 0 and b2 >= 0 and g >= 0 and g2 >= 0) implies
      cbound[b1, b2, g] = cbound[b1, b2, g2]
}

/*
 * S4 — with no growth, `min` IS right.
 * Lean: `min_sound_when_nongrowing`. Expected: no counterexample.
 */
assert S4_MinSoundWhenNonGrowing {
  all b1, b2: Int |
    (b1 >= 0 and b2 >= 0) implies cbound[b1, b2, 0] = tmin[b1, b2]
}

check S1_BoundAssociative for 6 Int
check S2_BoundIsMinOfBounds for 6 Int
check S3_BoundFactors for 6 Int
check S4_MinSoundWhenNonGrowing for 6 Int
