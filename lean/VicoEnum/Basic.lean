/-
  VicoEnum/Basic.lean

  Definitions for positive rational friezes over `(1/N)ℤ`, and the two results
  that need no frieze machinery:

    D4  the rotation action of `ℤ/5` on width-5 quiddity cycles is free
    D2  the width-5 search bound `p ≤ N³ + 2N²`

  Conventions follow Karpenkov, Short, van Son and Zabolotskii, arXiv:2601.21445, §6.
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors

namespace VicoEnum

/-! ## The lattice `(1/N)ℤ` -/

/-- `x` lies in `(1/N)ℤ`. -/
def InLattice (N : ℕ) (x : ℚ) : Prop := ∃ k : ℤ, x = (k : ℚ) / (N : ℚ)

lemma inLattice_iff {N : ℕ} (hN : 0 < N) (x : ℚ) :
    InLattice N x ↔ ∃ k : ℤ, (N : ℚ) * x = (k : ℚ) := by
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k, by field_simp⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by field_simp at hk ⊢; linarith [hk]⟩

/-! ## D4: the rotation action of `ℤ/5` is free

A width-5 quiddity cycle fixed by a nontrivial rotation is constant, and the
closing condition then forces `a³ - 2a - 1 = 0`. Since
`a³ - 2a - 1 = (a+1)(a² - a - 1)`, the only positive root is the golden ratio.
The proof is elementary: clearing denominators shows any rational root is an
integer, and no positive integer is a root.
-/

/-- For any rational `a`, `a.num = a * a.den`. -/
lemma num_eq_mul_den (a : ℚ) : (a.num : ℚ) = a * (a.den : ℚ) := by
  have hd : ((a.den : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := ℚ)).mpr a.den_nz
  exact (div_eq_iff hd).mp (Rat.num_div_den a)

/-- A rational root of `X³ - 2X - 1` has denominator one. -/
lemma den_eq_one_of_root {a : ℚ} (h : a ^ 3 - 2 * a - 1 = 0) : a.den = 1 := by
  have hnum := num_eq_mul_den a
  -- clear denominators: n³ = 2·n·d² + d³ over ℚ, then over ℤ
  have keyQ : (a.num : ℚ) ^ 3
      = 2 * (a.num : ℚ) * (a.den : ℚ) ^ 2 + (a.den : ℚ) ^ 3 := by
    rw [hnum]; linear_combination ((a.den : ℚ) ^ 3) * h
  have key : a.num ^ 3 = 2 * a.num * (a.den : ℤ) ^ 2 + (a.den : ℤ) ^ 3 := by
    exact_mod_cast keyQ
  have hdvd : (a.den : ℤ) ∣ a.num ^ 3 :=
    ⟨2 * a.num * (a.den : ℤ) + (a.den : ℤ) ^ 2, by rw [key]; ring⟩
  have hcop : IsCoprime (a.num) ((a.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using a.reduced
  have hcop3 : IsCoprime (a.num ^ 3) ((a.den : ℤ)) := hcop.pow_left
  have hunit : IsUnit ((a.den : ℤ)) := hcop3.isUnit_of_dvd' hdvd dvd_rfl
  have hd1 : (a.den : ℤ) = 1 ∨ (a.den : ℤ) = -1 := Int.isUnit_iff.mp hunit
  have hpos : 0 < (a.den : ℤ) := Int.natCast_pos.mpr a.pos
  omega

/-- **D4.** No positive rational number satisfies `a³ = 2a + 1`. Hence a positive
rational width-5 quiddity cycle has no nontrivial rotational symmetry, and the
`ℤ/5` action on such cycles is free. -/
theorem no_pos_rat_root (a : ℚ) (ha : 0 < a) : a ^ 3 - 2 * a - 1 ≠ 0 := by
  intro h
  have hden := den_eq_one_of_root h
  have hane : a = (a.num : ℚ) := by
    have := num_eq_mul_den a
    rw [hden] at this; simpa using this.symm
  have hnpos : 0 < a.num := by
    have : (0 : ℚ) < (a.num : ℚ) := by rw [← hane]; exact ha
    exact_mod_cast this
  have hz : a.num ^ 3 - 2 * a.num - 1 = 0 := by
    have : ((a.num : ℚ)) ^ 3 - 2 * (a.num : ℚ) - 1 = 0 := by rw [← hane]; exact h
    exact_mod_cast this
  -- n(n² - 2) = 1 forces n ∣ 1, and n = 1 is not a root
  have hfac : a.num * (a.num ^ 2 - 2) = 1 := by linarith [hz, sq_nonneg a.num]
  have hdvd : a.num ∣ 1 := ⟨a.num ^ 2 - 2, hfac.symm⟩
  have hn1 : a.num = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h1 | h1 <;> omega
  rw [hn1] at hfac
  norm_num at hfac

/-! ## D2: the width-5 search bound

With `a₀ = p/N`, `a₁ = q/N` and `e = pq - N²`, membership of `a₄ = N(q+N)/e` in
`(1/N)ℤ` is `e ∣ N²(q+N)`. Positivity of `e` then bounds `p`, and symmetrically `q`.
-/

/-- **D2.** Any width-5 solution satisfies `p ≤ N³ + 2N²`. -/
theorem width5_bound {N p q : ℤ} (hN : 0 < N) (hq : 0 < q)
    (hepos : 0 < p * q - N ^ 2) (hdvd : (p * q - N ^ 2) ∣ N ^ 2 * (q + N)) :
    p ≤ N ^ 3 + 2 * N ^ 2 := by
  have hpos : 0 < N ^ 2 * (q + N) := by positivity
  have h1 : p * q - N ^ 2 ≤ N ^ 2 * (q + N) := Int.le_of_dvd hpos hdvd
  have h2 : q * (p - N ^ 2) ≤ N ^ 3 + N ^ 2 := by nlinarith [h1]
  rcases le_or_lt p (N ^ 2) with hle | hgt
  · nlinarith [sq_nonneg N, hN]
  · have h3 : 0 < p - N ^ 2 := by omega
    have h4 : p - N ^ 2 ≤ q * (p - N ^ 2) := le_mul_of_one_le_left h3.le hq
    linarith

/-- The same bound for `q`, by the symmetry of the defining conditions. -/
theorem width5_bound' {N p q : ℤ} (hN : 0 < N) (hp : 0 < p)
    (hepos : 0 < p * q - N ^ 2) (hdvd : (p * q - N ^ 2) ∣ N ^ 2 * (p + N)) :
    q ≤ N ^ 3 + 2 * N ^ 2 := by
  have h1 : 0 < q * p - N ^ 2 := by rwa [mul_comm]
  have h2 : (q * p - N ^ 2) ∣ N ^ 2 * (p + N) := by rwa [mul_comm q p]
  exact width5_bound hN hp h1 h2

end VicoEnum
