/-
  VicoEnum/FordMin.lean

  The smallest variable in Ford's equation, and what it gives for `T(N,5)`.

  `ford_min_bound`: if `h u v = A(u+v) + B` in positive integers then
  `T = min(h,u,v)` satisfies `T^3 <= 2AT + B`. The proof uses only the symmetry in
  `u` and `v`: with `u <= v`, dividing `huv <= 2Av + B` by `v` and using `T <= v`
  gives `v(T^2 - 2A) <= B`, and `T <= v` finishes.

  `ford_min_bound_N`: every term of `T5_sum_ford` has `A <= N` and `B <= N^2`
  (`ford_params_le`), and then `T^3 <= 8N^2`, that is `T <= 2 N^(2/3)`.

  Consequence, written out in the paper. Fix a term `F(A,B)`. Sorting by which of
  `h, u, v` is least, each choice of the least variable `t <= 2N^(2/3)` determines the
  other two up to a divisor count: if `u` is least then `v` divides `Au+B`; if `h` is
  least then `hu - A` divides `A^2 + Bh`, by `(hu-A)(hv-A) = A^2 + Bh`. Every number
  whose divisors are being counted is at most a fixed power of `N`, so the elementary
  bound `d(n) = O_eps(n^eps)` (`card_divisors_pow_le`) gives
  `F(A,B) = O_eps(N^(2/3+eps))`. The number of terms is `N^(o(1))` by `cor:terms`, so

      T(N,5) = O_eps(N^(2/3+eps)),

  for every `N`. This improves `cor:t5upper`, which gives `O_eps(N^(1+eps))`. No
  Shiu-type input is needed, only the divisor bound already in the library.
-/
import VicoEnum.FordSum

namespace VicoEnum

/-- **The smallest variable in Ford's equation.** If `huv = A(u+v)+B` in positive
integers then `T = min(h,u,v)` satisfies `T^3 ≤ 2AT + B`. Only the symmetry in `u` and
`v` is used. -/
theorem ford_min_bound {A B h u v : ℕ}
    (heq : h * u * v = A * (u + v) + B) :
    (min h (min u v)) ^ 3 ≤ 2 * A * (min h (min u v)) + B := by
  set T := min h (min u v) with hT
  have hTh : T ≤ h := min_le_left _ _
  have hTu : T ≤ u := le_trans (min_le_right _ _) (min_le_left _ _)
  have hTv : T ≤ v := le_trans (min_le_right _ _) (min_le_right _ _)
  -- some `w` among `u, v` is the larger, and carries the inequality
  have key : ∃ w : ℕ, T ≤ w ∧ T * T * w ≤ 2 * A * w + B := by
    rcases le_total u v with huv | hvu
    · refine ⟨v, hTv, ?_⟩
      calc T * T * v ≤ (h * u) * v := Nat.mul_le_mul_right _ (Nat.mul_le_mul hTh hTu)
        _ = A * (u + v) + B := by rw [← heq]
        _ ≤ 2 * A * v + B := by
            have : A * (u + v) ≤ 2 * A * v := by
              rw [show 2 * A * v = A * (v + v) from by ring]
              exact Nat.mul_le_mul_left _ (by omega)
            omega
    · refine ⟨u, hTu, ?_⟩
      calc T * T * u ≤ (h * v) * u := Nat.mul_le_mul_right _ (Nat.mul_le_mul hTh hTv)
        _ = A * (u + v) + B := by rw [← heq]; ring
        _ ≤ 2 * A * u + B := by
            have : A * (u + v) ≤ 2 * A * u := by
              rw [show 2 * A * u = A * (u + u) from by ring]
              exact Nat.mul_le_mul_left _ (by omega)
            omega
  obtain ⟨w, hTw, hle⟩ := key
  have hZ : (T : ℤ) * T * w ≤ 2 * A * w + B := by exact_mod_cast hle
  have hTwZ : (T : ℤ) ≤ (w : ℤ) := by exact_mod_cast hTw
  have hT0 : (0 : ℤ) ≤ (T : ℤ) := Int.natCast_nonneg _
  have hB0 : (0 : ℤ) ≤ (B : ℤ) := Int.natCast_nonneg _
  have hfin : (T : ℤ) ^ 3 ≤ 2 * A * T + B := by
    rcases le_or_lt ((T : ℤ) * T) (2 * A) with hc | hc
    · nlinarith [hT0, hB0, hc]
    · have h1 : (0 : ℤ) ≤ (T : ℤ) * T - 2 * A := by linarith
      have h2 : (T : ℤ) * ((T : ℤ) * T - 2 * A) ≤ (w : ℤ) * ((T : ℤ) * T - 2 * A) :=
        mul_le_mul_of_nonneg_right hTwZ h1
      nlinarith [h2, hZ]
  exact_mod_cast hfin

/-- **The cube-root shape at the parameters of the decomposition.** Every term of
`T5_sum_ford` has `A ≤ N` and `B ≤ N^2`, and then the smallest variable satisfies
`T^3 ≤ 8N^2`, that is `T ≤ 2N^(2/3)`. -/
theorem ford_min_bound_N {N T : ℕ} (hN : 0 < N) (h : T ^ 3 ≤ 2 * N * T + N ^ 2) :
    T ^ 3 ≤ 8 * N ^ 2 := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  rcases le_or_lt (2 * T) N with hc | hc
  · have hle : 2 * N * T ≤ N ^ 2 := by nlinarith [hc, hN]
    omega
  · have hN2 : N ^ 2 < 2 * N * T := by nlinarith [hc, hN]
    have h4 : T ^ 2 * T < 4 * N * T := by nlinarith [h, hN2]
    have hT2 : T ^ 2 < 4 * N := Nat.lt_of_mul_lt_mul_right h4
    have e2 : (T ^ 2) ^ 3 ≤ (4 * N) ^ 3 := Nat.pow_le_pow_left (le_of_lt hT2) 3
    have hsq : (T ^ 3) ^ 2 ≤ (8 * N ^ 2) ^ 2 := by
      calc (T ^ 3) ^ 2 = (T ^ 2) ^ 3 := by ring
        _ ≤ (4 * N) ^ 3 := e2
        _ = 64 * N ^ 3 := by ring
        _ ≤ 64 * N ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by norm_num))
        _ = (8 * N ^ 2) ^ 2 := by ring
    exact Nat.pow_le_pow_iff_left two_ne_zero |>.mp hsq

/-- The two parameter bounds satisfied by every term of `T5_sum_ford`. -/
theorem ford_params_le {N M : ℕ} (hN : 0 < N) (hM : M ∣ N ^ 2) :
    Nat.gcd N M ≤ N ∧ M / (N / Nat.gcd N M) ≤ N ^ 2 := by
  refine ⟨Nat.le_of_dvd hN (Nat.gcd_dvd_left _ _), ?_⟩
  exact le_trans (Nat.div_le_self _ _) (Nat.le_of_dvd (by positivity) hM)

end VicoEnum
