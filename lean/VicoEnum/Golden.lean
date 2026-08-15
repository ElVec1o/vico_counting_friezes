/-
  VicoEnum/Golden.lean

  Why the rotation has no fixed point on numerator pairs.

  Transporting Theorem `thm:free` from friezes to the index set of `T5` needs the rotation
  written as a map on numerator pairs. A fixed point of that map is a pair with `p = q` and
  `a₂ = a₀`, which by the width-5 parameterisation forces

      p² = pN + N²,

  the golden-ratio relation. Completing the square gives `(2p - N)² = 5N²`, so it has no
  solution with `N > 0`: that would make `5` a square. The argument is recorded here
  separately from the transport, which needs the arithmetic of the parameterisation as well.

  Over the friezes themselves the corresponding statement is `no_constant_quiddity`, which
  goes through the cubic `a³ - 2a - 1 = 0` instead. The two are consistent: `p² = pN + N²`
  implies `p³ = 2pN² + N³`, which is that cubic cleared of denominators.
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace VicoEnum

/-- **Five is not a square, in the form needed.** `k² = 5N²` forces `N = 0`, because the
exponent of `5` is even on the left and odd on the right. -/
theorem not_five_mul_sq {k N : ℕ} (hN : 0 < N) : k ^ 2 ≠ 5 * N ^ 2 := by
  intro h
  have h5 : Nat.Prime 5 := by norm_num
  have hk : k ≠ 0 := by
    rintro rfl
    simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true] at h
    have : 0 < N ^ 2 := by positivity
    omega
  have hN2 : N ^ 2 ≠ 0 := by positivity
  have e1 : (k ^ 2).factorization 5 = 2 * k.factorization 5 := by
    rw [Nat.factorization_pow]; simp [mul_comm]
  have e2 : (5 * N ^ 2).factorization 5 = 1 + 2 * N.factorization 5 := by
    rw [Nat.factorization_mul (by norm_num) hN2, Nat.factorization_pow]
    simp [h5.factorization_self, mul_comm]
  rw [h, e2] at e1
  omega

/-- **The golden relation has no solution over `ℕ`.** A fixed point of the rotation on
numerator pairs would satisfy `p² = pN + N²`; completing the square turns that into
`(2p - N)² = 5N²`. -/
theorem no_golden_pair {N p : ℕ} (hN : 0 < N) : p * p ≠ p * N + N * N := by
  intro h
  have hz : ((2 * (p : ℤ) - N)) ^ 2 = 5 * (N : ℤ) ^ 2 := by
    have hc : (p : ℤ) * p = (p : ℤ) * N + (N : ℤ) * N := by exact_mod_cast h
    linear_combination 4 * hc
  have habs : ((2 * (p : ℤ) - N).natAbs) ^ 2 = 5 * N ^ 2 := by
    have hns : (((2 * (p : ℤ) - N).natAbs : ℤ)) ^ 2 = (2 * (p : ℤ) - N) ^ 2 := by
      rw [← Int.abs_eq_natAbs, sq_abs]
    have : (((2 * (p : ℤ) - N).natAbs : ℤ)) ^ 2 = 5 * (N : ℤ) ^ 2 := by rw [hns, hz]
    exact_mod_cast this
  exact not_five_mul_sq hN habs

/-- The same relation in the shape the parameterisation produces: with `p = q` the
condition `a₂ = a₀` reads `N²(p+N) = p(p² - N²)`, which reduces to `p² = pN + N²` once the
common factor `p + N` is removed. -/
theorem golden_of_fixed {N p : ℕ} (hN : 0 < N) (hp : 0 < p)
    (h : N ^ 2 * (p + N) = p * (p * p - N ^ 2)) (hlt : N ^ 2 < p * p) : False := by
  have hz : (N : ℤ) ^ 2 * ((p : ℤ) + N) = (p : ℤ) * ((p : ℤ) * p - (N : ℤ) ^ 2) := by
    have hsub : ((p * p - N ^ 2 : ℕ) : ℤ) = (p : ℤ) * p - (N : ℤ) ^ 2 := by
      push_cast [Nat.cast_sub hlt.le]; ring
    have := h
    zify [hlt.le] at this
    linarith [this]
  -- factor out (p + N), which is positive
  have hfac : ((p : ℤ) + N) * ((N : ℤ) ^ 2 - (p * p - p * N)) = 0 := by linear_combination hz
  have hpos : ((p : ℤ) + N) ≠ 0 := by positivity
  have : (N : ℤ) ^ 2 = (p : ℤ) * p - (p : ℤ) * N := by
    rcases mul_eq_zero.mp hfac with hc | hc
    · exact absurd hc hpos
    · linarith
  have hnat : p * p = p * N + N * N := by
    have : (p : ℤ) * p = (p : ℤ) * N + (N : ℤ) * N := by linarith [this]
    exact_mod_cast this
  exact no_golden_pair hN hnat

end VicoEnum
