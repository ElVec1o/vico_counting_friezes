/-
  VicoEnum/DivisorSum.lean

  The cubic as a sum of divisor counts in arithmetic progressions.

  The equation `auv = n + u + v` factors on each `a`-slice. Multiplying by `a`,

      (au - 1)(av - 1) = a(auv - u - v) + 1 = an + 1,

  so the solutions with a given `a` are the factorisations of `an + 1` into two factors
  congruent to `-1` modulo `a`, and the second congruence is automatic once the first
  holds. Hence

      C(n) = sum over a of #{ d dividing an+1 : d = -1 mod a }.

  This locates the analytic difficulty exactly. Counting `C(n)` is counting divisors of
  `an+1` in a fixed residue class modulo `a`, summed over `a`, and the modulus `a` grows
  with the quantity `an+1` whose divisors are being counted. When `a` is of size `n^{1/2}`
  the modulus is comparable to the square root of `an+1`, which is precisely the range in
  which the standard equidistribution results for divisors in progressions give nothing:
  the Weil bound on the associated modular hyperbola has error of size `n^{1/2}` against a
  main term of size `n^{1/3}`, as recorded in the paper.

  So the analytic half is not a missing trick. It is the divisor-in-progressions problem at
  the modulus where the known technology stops.
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace VicoEnum

/-- **The slice factorisation.** For `a ≠ 0`, the solutions of `auv = n + u + v` with a
given `a` are exactly the factorisations `(au-1)(av-1) = an+1`. -/
theorem cubic_slice_factor {a : ℤ} (ha : a ≠ 0) (u v n : ℤ) :
    a * u * v = n + u + v ↔ (a * u - 1) * (a * v - 1) = a * n + 1 := by
  constructor
  · intro h; linear_combination a * h
  · intro h
    have : a * (a * u * v) = a * (n + u + v) := by linear_combination h
    exact mul_left_cancel₀ ha this

/-- **The second congruence is automatic.** If `d` divides `an+1` and `d ≡ -1 mod a`, then
the complementary divisor is also `≡ -1 mod a`. So the count on each slice is a count of
divisors in a single residue class, not a pair of conditions. -/
theorem complement_congr {a d e n : ℤ} (hde : d * e = a * n + 1)
    (hd : a ∣ d + 1) : a ∣ e + 1 := by
  obtain ⟨k, hk⟩ := hd
  exact ⟨k * e - n, by linear_combination e * hk - hde⟩

/-- The divisor produced by a solution is congruent to `-1`. -/
theorem slice_divisor_congr (a u : ℤ) : a ∣ (a * u - 1) + 1 := ⟨u, by ring⟩

/-- The divisor produced by a solution divides `an+1`. -/
theorem slice_divisor_dvd {a u v n : ℤ} (ha : a ≠ 0) (h : a * u * v = n + u + v) :
    (a * u - 1) ∣ a * n + 1 :=
  ⟨a * v - 1, ((cubic_slice_factor ha u v n).mp h).symm⟩

/-- **Recovering the solution from the divisor.** If `d ∣ an+1` and `a ∣ d+1`, the pair
`(u,v)` with `au = d+1` and `av = (an+1)/d + 1` solves the cubic. -/
theorem solution_of_divisor {a d e n u v : ℤ} (ha : a ≠ 0)
    (hde : d * e = a * n + 1) (hu : a * u = d + 1) (hv : a * v = e + 1) :
    a * u * v = n + u + v := by
  refine (cubic_slice_factor ha u v n).mpr ?_
  rw [show a * u - 1 = d by linarith, show a * v - 1 = e by linarith]
  exact hde

/-! ### Reducing the conjectured order to equidistribution

`C(n)` is the sum over `a` of the divisors of `an+1` in one residue class mod `a`. If those
divisors equidistribute, each slice contributes about `d(an+1)/a`, and the whole sum is at
most `(max divisor count) * (harmonic sum)`. Since the divisor function is `m^{o(1)}` and
the harmonic sum is `O(log n)`, that bound is `n^{o(1)}`.

So the conjecture `C(p) = p^{o(1)}` follows from the equidistribution statement
`C(p) = O(∑_a d(ap+1)/a)`. `weighted_sum_le` is the finite core of the elementary step.

The remaining input, `d(m) = m^{o(1)}`, is not in Mathlib at the version used here; that gap
is recorded in the paper. -/

/-- **The elementary half of the reduction.** If every term of a weighted sum is bounded by
`D`, the weighted sum is at most `D` times the sum of the weights. Applied with
`f a = d(a n + 1)` and weights `1/(a+1)`, this bounds `∑ d(an+1)/a` by the largest divisor
count times the harmonic sum. -/
theorem weighted_sum_le {A : ℕ} {D : ℚ} (f w : ℕ → ℚ)
    (hD : ∀ a ∈ Finset.range A, f a ≤ D) (hw : ∀ a ∈ Finset.range A, 0 ≤ w a) :
    ∑ a ∈ Finset.range A, f a * w a ≤ ∑ a ∈ Finset.range A, D * w a :=
  Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_right (hD a ha) (hw a ha)

end VicoEnum
