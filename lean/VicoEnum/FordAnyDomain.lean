/-
  VicoEnum/FordAnyDomain.lean

  Ford's equation over an arbitrary domain, and finiteness over the Gaussian integers.

  Width five over `(1/N)O` asks for `p, q` in `O` with

      D = pq - N²  ≠ 0,    N²(p+N) = Dk,    N²(q+N) = Dl.

  Eliminating `p` and `q` from those three relations gives, in any commutative domain,

      D k l = N⁴ + N³(k+l),

  which is Ford's equation. Over `ℤ` with positivity this is the equation counted by
  `C(p)`; the derivation below uses no order, so it holds over `ℤ[i]`, over any ring of
  integers, and over any commutative domain at all.

  Finiteness over `ℤ[i]` then follows from the norm. `ford_min_norm_bound` shows one of
  `k`, `l` has bounded norm, and `ford_determines_l` shows the third variable is then
  pinned by the other two, so the solution set is finite. This is what replaces the
  order-theoretic search bounds of the real theory.
-/
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.LinearCombination

namespace VicoEnum

/-- **Ford's equation, over any commutative domain.** From `D = pq - N²` together with
`N²(p+N) = Dk` and `N²(q+N) = Dl` one gets `Dkl = N⁴ + N³(k+l)`, with no use of order,
positivity, or the arithmetic of `ℤ`. -/
theorem ford_general {O : Type*} [CommRing O] [IsDomain O] {N p q D k l : O}
    (hD : D = p * q - N ^ 2) (hD0 : D ≠ 0)
    (hk : N ^ 2 * (p + N) = D * k) (hl : N ^ 2 * (q + N) = D * l) :
    D * k * l = N ^ 4 + N ^ 3 * (k + l) := by
  refine mul_left_cancel₀ hD0 ?_
  calc D * (D * k * l) = (N ^ 2 * (p + N)) * (N ^ 2 * (q + N)) := by
        rw [hk, hl]; ring
    _ = D * (N ^ 4 + N ^ 3 * (k + l)) := by
        linear_combination N ^ 3 * hk + N ^ 3 * hl - N ^ 4 * hD

/-- `k` vanishes exactly when `p = -N`, the degeneracy that positivity hides over `ℝ`.
So on genuine friezes `k ≠ 0`, and likewise `l ≠ 0`. -/
theorem ford_k_ne_zero {O : Type*} [CommRing O] [IsDomain O] {N p D k : O}
    (hN : (N : O) ≠ 0) (hp : p + N ≠ 0) (hk : N ^ 2 * (p + N) = D * k) : k ≠ 0 := by
  intro h
  rw [h, mul_zero] at hk
  rcases mul_eq_zero.mp hk with h1 | h2
  · exact hN (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1)
  · exact hp h2

/-- **The third variable is pinned by the other two.** Ford's equation rearranges to
`l(Dk - N³) = N⁴ + N³k`, so once `D` and `k` are known and `Dk ≠ N³`, the value of `l` is
determined. With `ford_min_norm_bound` this is what makes the solution set finite. -/
theorem ford_determines_l {O : Type*} [CommRing O] [IsDomain O] {N D k l : O}
    (h : D * k * l = N ^ 4 + N ^ 3 * (k + l)) :
    l * (D * k - N ^ 3) = N ^ 4 + N ^ 3 * k := by
  linear_combination h

/-- The degenerate branch `Dk = N³` forces `k = -N`. Combined with `N²(p+N) = Dk` this
gives `p = 0`, which is not a quiddity numerator, so the branch is empty on friezes. -/
theorem ford_degenerate_branch {O : Type*} [CommRing O] [IsDomain O] {N D k l : O}
    (hN : (N : O) ≠ 0) (h : D * k * l = N ^ 4 + N ^ 3 * (k + l))
    (hdeg : D * k = N ^ 3) : k = -N := by
  have h1 : N ^ 4 + N ^ 3 * k = 0 := by linear_combination -ford_determines_l h + l * hdeg
  have h2 : N ^ 3 * (N + k) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h4
  · exact absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h3) hN
  · linear_combination h4

/-! ## Finiteness over the Gaussian integers

Over `ℝ` the solution set is cut down by positivity. Over `ℤ[i]` there is no order, and
finiteness instead comes from the norm: Ford's equation forces one of `k`, `l` to have
bounded norm, and `ford_determines_l` then pins the remaining variable. -/

open Zsqrtd in
/-- A quadratic triangle inequality for the norm on `ℤ[i]`. -/
theorem gaussian_norm_add_le (x y : GaussianInt) :
    (x + y).norm ≤ 2 * x.norm + 2 * y.norm := by
  simp only [Zsqrtd.norm_def, Zsqrtd.add_re, Zsqrtd.add_im]
  nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.im - y.im)]

open Zsqrtd in
/-- **The Gaussian finiteness bound.** A solution of Ford's equation over `ℤ[i]` with
`D ≠ 0` has `min(‖k‖, ‖l‖) ≤ 8N⁶ + 2N⁸`. So one of the two variables ranges over a finite
set, and `ford_determines_l` fixes the third from the other two. This is what replaces the
order-theoretic search bound of the real theory, and it is the reason the count over
`(1/N)ℤ[i]` is finite even though `ℤ[i]` carries no order. -/
theorem ford_min_norm_bound {N : ℕ} {D k l : GaussianInt} (hD : D ≠ 0)
    (h : D * k * l = (N : GaussianInt) ^ 4 + (N : GaussianInt) ^ 3 * (k + l)) :
    min k.norm l.norm ≤ 8 * (N : ℤ) ^ 6 + 2 * (N : ℤ) ^ 8 := by
  have hnk : 0 ≤ k.norm := GaussianInt.norm_nonneg k
  have hnl : 0 ≤ l.norm := GaussianInt.norm_nonneg l
  have hnD : 0 ≤ D.norm := GaussianInt.norm_nonneg D
  have hD1 : 1 ≤ D.norm := by
    rcases hnD.lt_or_eq with h1 | h1
    · omega
    · exact absurd (GaussianInt.norm_eq_zero.mp h1.symm) hD
  have e4 : ((N : GaussianInt) ^ 4).norm = (N : ℤ) ^ 8 := by
    rw [show ((N : GaussianInt) ^ 4) = ((N ^ 4 : ℕ) : GaussianInt) by push_cast; ring,
      Zsqrtd.norm_natCast]; push_cast; ring
  have e3 : ((N : GaussianInt) ^ 3).norm = (N : ℤ) ^ 6 := by
    rw [show ((N : GaussianInt) ^ 3) = ((N ^ 3 : ℕ) : GaussianInt) by push_cast; ring,
      Zsqrtd.norm_natCast]; push_cast; ring
  have hprod : D.norm * k.norm * l.norm
      = ((N : GaussianInt) ^ 4 + (N : GaussianInt) ^ 3 * (k + l)).norm := by
    rw [← h, Zsqrtd.norm_mul, Zsqrtd.norm_mul]
  have hstep : ((N : GaussianInt) ^ 4 + (N : GaussianInt) ^ 3 * (k + l)).norm
      ≤ 2 * (N : ℤ) ^ 8 + 2 * ((N : ℤ) ^ 6 * (k + l).norm) := by
    have := gaussian_norm_add_le ((N : GaussianInt) ^ 4) ((N : GaussianInt) ^ 3 * (k + l))
    rwa [e4, Zsqrtd.norm_mul, e3] at this
  have hkl : (k + l).norm ≤ 2 * k.norm + 2 * l.norm := gaussian_norm_add_le k l
  have hN6 : (0 : ℤ) ≤ (N : ℤ) ^ 6 := by positivity
  have key : k.norm * l.norm ≤ 2 * (N : ℤ) ^ 8 + 4 * (N : ℤ) ^ 6 * (k.norm + l.norm) := by
    nlinarith [hprod, hstep, hkl, hnk, hnl, hD1, hN6,
      mul_nonneg hnk hnl, mul_le_mul_of_nonneg_left hkl hN6]
  by_contra hcon
  push_neg at hcon
  have ha : 8 * (N : ℤ) ^ 6 + 2 * (N : ℤ) ^ 8 < k.norm := lt_of_lt_of_le hcon (min_le_left _ _)
  have hb : 8 * (N : ℤ) ^ 6 + 2 * (N : ℤ) ^ 8 < l.norm := lt_of_lt_of_le hcon (min_le_right _ _)
  have hN8 : (0 : ℤ) ≤ (N : ℤ) ^ 8 := by positivity
  nlinarith [key, ha, hb, hN6, hN8,
    mul_pos (by linarith : (0:ℤ) < k.norm - 4 * (N : ℤ) ^ 6)
            (by linarith : (0:ℤ) < l.norm - 4 * (N : ℤ) ^ 6)]

end VicoEnum
