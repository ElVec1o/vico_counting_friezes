/-
  VicoEnum/FordCongruence.lean

  A congruence for sums of Ford counts.

  The rotation action of `Z/5` on width-5 quiddity cycles is free (`thm:free`), so
  `5 | T(N,5)` (`five_dvd_T5`). Read through `T5_sum_ford`, that is a statement about
  counts of solutions of `xyz = A(x+y) + B`, with no reference to friezes:

      5 divides the sum, over the divisors M of N^2 in the support, of
      F(gcd(N,M), M gcd(N,M)/N).

  The individual terms are generally not divisible by five. At `N = 8` the five terms are
  17, 27, 31, 31, 39, none of them divisible by five, and the sum is 145. Over `N <= 25`
  only 23 of the 101 terms are divisible by five, and every one of the 25 sums is.

  Nothing in the equation `xyz = A(x+y) + B` suggests this. It is what the frieze side
  contributes to the Diophantine side, rather than the other way round.
-/
import VicoEnum.FordSquarefree

namespace VicoEnum

/-- **A congruence for sums of Ford counts.** For every `N`, the sum of the Ford counts
appearing in `T5_sum_ford` is divisible by five. The individual terms are not: at `N = 8`
they are `17, 27, 31, 31, 39`. The divisibility comes from the free rotation action on
friezes and has no evident explanation on the Diophantine side. -/
theorem ford_sum_five_dvd {N : ℕ} (hN : 0 < N) :
    5 ∣ ∑ M ∈ (N ^ 2).divisors.filter (fun M => (N / Nat.gcd N M) ∣ M),
      (FordSet (Nat.gcd N M) (M / (N / Nat.gcd N M))).ncard := by
  rw [← T5_sum_ford hN]; exact five_dvd_T5 hN

/-- The same congruence at a squarefree `N`, where the sum has one term per divisor:
`5 ∣ Σ_{m ∣ N} F(N, N m)`. -/
theorem ford_sum_five_dvd_squarefree {N : ℕ} (hN : 0 < N) (hsq : Squarefree N) :
    5 ∣ ∑ m ∈ N.divisors, (FordSet N (N * m)).ncard := by
  rw [← T5_squarefree hN hsq]; exact five_dvd_T5 hN

end VicoEnum
