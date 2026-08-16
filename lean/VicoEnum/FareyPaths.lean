/-
  VicoEnum/FareyPaths.lean

  Counting the objects of Theorem B of Karpenkov, Short, van Son and Zabolotskii.

  Their Theorem B: for positive integers N, K, R with N = K R, the minimal clockwise paths
  of length n in the Farey graph F_R, modulo SL(2,Z), correspond one to one with the
  positive friezes over (1/N)Z of width n and greatest common divisor K.

  Every frieze over (1/N)Z has a greatest common divisor K dividing N, so at width five,
  writing P R for the number of those path classes in F_R,

      T5 N = sum over R | N of P R.

  `path_count_of_T5` inverts this: P R = sum over d | R of mu(R/d) T5 d. Combined with
  `T5_sum_ford`, which evaluates T5 N as a sum of Ford counts, this counts the path classes
  of F_R for every R.

  At a prime p >= 5 the sum has two terms and P p = 5 C(p), where C(p) counts the solutions
  of a u v = p + u + v. So the number of minimal closed clockwise 5-paths in F_p, modulo
  SL(2,Z), is exactly five times the Ford count at p.
-/
import VicoEnum.FordDiagonal

namespace VicoEnum
open ArithmeticFunction

/-- **The count by exact greatest common divisor.** Theorem B of Karpenkov, Short, van Son
and Zabolotskii puts the positive friezes over `(1/N)ℤ` of width `n` and greatest common
divisor `K` in bijection with the minimal closed clockwise paths of length `n` in the Farey
graph `F_R`, `R = N/K`, modulo `SL(2,ℤ)`. Writing `P R` for the number of those paths at
width five, every frieze over `(1/N)ℤ` has some `K ∣ N`, so `T5 N = ∑_{R ∣ N} P R`. Möbius
inversion then evaluates `P` from `T5`. -/
theorem path_count_of_T5 {P : ℕ → ℤ}
    (hsum : ∀ N > 0, ∑ R ∈ N.divisors, P R = (T5 N : ℤ)) :
    ∀ R > 0, P R = ∑ x ∈ R.divisorsAntidiagonal, (μ x.1 : ℤ) * (T5 x.2 : ℤ) := by
  intro R hR
  have h := (sum_eq_iff_sum_smul_moebius_eq (f := P) (g := fun N => (T5 N : ℤ))).mp hsum R hR
  simpa using h.symm

end VicoEnum
