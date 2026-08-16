/-
  VicoEnum/WidthSixNoGo.lean

  The width-5 decomposition does not extend to width 6.

  At width five, `thm:t5red` confines the reduction parameter by `M | N^2`, so the index set
  of `T5_sum_ford` is a set of divisors of `N^2` and is determined by `N` alone. That is what
  makes the decomposition into Ford counts finite and explicit.

  At width six the parameter is not so confined. The quiddity cycle

      (1/2, 6, 1, 2, 3/2, 4)

  is a positive frieze of width six over (1/2)Z; in numerators `(p,q,r,e) = (1,12,2,3)`,
  which is `width6_witness`. Its reduction data is

      A = pq - N^2 = 8,   B = qr - N^2 = 20,   g = gcd(A,B) = 4,   U = 2,   V = 5,
      M = gUV - N^2(U+V) = 12,

  and `12` divides no power of `2` (`twelve_not_dvd_two_pow`). So at `N = 2` the width-6
  parameter already leaves the divisors of every power of `N`, and no decomposition indexed
  by such divisors can exist.

  The mechanism is the continuant window `R` of `general_reduction`: at width five `R = 1`
  and the divisibility `N^{n-4} R | g M` reduces to one on `N` alone; from width six on,
  `R` is a quiddity numerator and carries primes coprime to `N`. Here `R = q = 12`.
-/
import VicoEnum.DiscreteRings
namespace VicoEnum

/-- `12` divides no power of `2`. -/
theorem twelve_not_dvd_two_pow (k : ℕ) : ¬ ((12 : ℕ) ∣ 2 ^ k) := by
  intro h
  have h3 : (3 : ℕ) ∣ 2 ^ k := dvd_trans ⟨4, by norm_num⟩ h
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3)
  omega

/-- **The witness.** `(p,q,r,e) = (1,12,2,3)` satisfies the width-6 conditions at `N = 2`. -/
theorem width6_witness : W6 2 1 12 2 3 := by decide

/-- **No-go at width six.** At width five the reduction parameter `M` divides `N^2`
(`thm:t5red`), so the index set of the decomposition is determined by `N`. At width six it
is not: the frieze `width6_witness` over `(1/2)ℤ` has

    A = pq - N^2 = 8,  B = qr - N^2 = 20,  g = gcd(A,B) = 4,  U = 2,  V = 5,
    M = gUV - N^2(U+V) = 12,

and `12` divides no power of `2`. So no decomposition of `T(N,6)` indexed by the divisors
of a power of `N` exists, and the width-5 argument does not extend. -/
theorem width6_param_not_dvd_pow :
    (Nat.gcd (1 * 12 - 2 ^ 2) (12 * 2 - 2 ^ 2) = 4) ∧
    ((1 * 12 - 2 ^ 2) / 4 = 2) ∧ ((12 * 2 - 2 ^ 2) / 4 = 5) ∧
    (4 * 2 * 5 - 2 ^ 2 * (2 + 5) = 12) ∧
    (∀ k : ℕ, ¬ ((12 : ℕ) ∣ 2 ^ k)) :=
  ⟨by decide, by decide, by decide, by decide, twelve_not_dvd_two_pow⟩

end VicoEnum
