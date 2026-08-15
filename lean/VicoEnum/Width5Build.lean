/-
  VicoEnum/Width5Build.lean

  The ten closing identities at width five.

  `friezeOf_isFrieze` reduces building a frieze of width `n` to the two closing conditions
  `K_{n-2} = 1` and `K_{n-1} = 0`. At `n = 5` those are `K_3 = 1` and `K_4 = 0` at each of
  the five columns, ten identities in all, and they are checked here for the quiddity that a
  `W5` pair determines:

      a₀,  a₁,  (a₀+1)/D,  D,  (a₁+1)/D,        D = a₀a₁ - 1.

  Every one reduces to `a₀a₁ - D = 1`, which is the definition of `D`. With the `hD : D ≠ 0`
  that `W5` supplies through `N² < pq`, `field_simp` and `ring` close each case.

  This is the analytic half of the converse of Proposition `prop:w5cond`. The remaining half
  is the lattice condition, that the entries lie in `(1/N)ℤ`, which is not proved here.
-/
import VicoEnum.Build

namespace VicoEnum

/-! ## Closed forms for the short continuants -/

theorem Kc_two (a : ℤ → ℚ) (j : ℤ) : Kc a j 2 = a (j + 1) * a j - 1 := by
  rw [Kc_succ_succ a j 0]; simp

theorem Kc_three (a : ℤ → ℚ) (j : ℤ) :
    Kc a j 3 = a (j + 2) * (a (j + 1) * a j - 1) - a j := by
  have hi : j + ((1 : ℕ) : ℤ) + 1 = j + 2 := by push_cast; ring
  rw [Kc_succ_succ a j 1, Kc_two, Kc_one, hi]

theorem Kc_four (a : ℤ → ℚ) (j : ℤ) :
    Kc a j 4 = a (j + 3) * (a (j + 2) * (a (j + 1) * a j - 1) - a j)
      - (a (j + 1) * a j - 1) := by
  have hi : j + ((2 : ℕ) : ℤ) + 1 = j + 3 := by push_cast; ring
  rw [Kc_succ_succ a j 2, Kc_three, Kc_two, hi]

/-! ## The width-5 quiddity of a pair -/

/-- The five quiddity entries determined by `a₀` and `a₁`, extended `5`-periodically. -/
noncomputable def quid5fn (a0 a1 : ℚ) : ℤ → ℚ := fun j =>
  if j % 5 = 0 then a0
  else if j % 5 = 1 then a1
  else if j % 5 = 2 then (a0 + 1) / (a0 * a1 - 1)
  else if j % 5 = 3 then a0 * a1 - 1
  else (a1 + 1) / (a0 * a1 - 1)

theorem quid5fn_periodic (a0 a1 : ℚ) (j : ℤ) :
    quid5fn a0 a1 (j + 5) = quid5fn a0 a1 j := by
  simp only [quid5fn, show (j + 5) % 5 = j % 5 from by omega]

theorem q0 (a0 a1 : ℚ) (j : ℤ) (h : j % 5 = 0) : quid5fn a0 a1 j = a0 := by
  simp [quid5fn, h]
theorem q1 (a0 a1 : ℚ) (j : ℤ) (h : j % 5 = 1) : quid5fn a0 a1 j = a1 := by
  simp [quid5fn, h]
theorem q2 (a0 a1 : ℚ) (j : ℤ) (h : j % 5 = 2) :
    quid5fn a0 a1 j = (a0 + 1) / (a0 * a1 - 1) := by simp [quid5fn, h]
theorem q3 (a0 a1 : ℚ) (j : ℤ) (h : j % 5 = 3) :
    quid5fn a0 a1 j = a0 * a1 - 1 := by simp [quid5fn, h]
theorem q4 (a0 a1 : ℚ) (j : ℤ) (h : j % 5 = 4) :
    quid5fn a0 a1 j = (a1 + 1) / (a0 * a1 - 1) := by simp [quid5fn, h]

/-! ## The ten identities

Each reduces to `a₀a₁ - D = 1`, the definition of `D`. -/

/-- **`K_3 = 1` at every column.** -/
theorem quid5fn_three {a0 a1 : ℚ} (hD : a0 * a1 - 1 ≠ 0) (j : ℤ) :
    Kc (quid5fn a0 a1) j 3 = 1 := by
  rw [Kc_three]
  rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4)
    with h | h | h | h | h
  · rw [q0 a0 a1 j h, q1 a0 a1 (j+1) (by omega), q2 a0 a1 (j+2) (by omega)]; field_simp; all_goals ring
  · rw [q1 a0 a1 j h, q2 a0 a1 (j+1) (by omega), q3 a0 a1 (j+2) (by omega)]; field_simp; all_goals ring
  · rw [q2 a0 a1 j h, q3 a0 a1 (j+1) (by omega), q4 a0 a1 (j+2) (by omega)]; field_simp; all_goals ring
  · rw [q3 a0 a1 j h, q4 a0 a1 (j+1) (by omega), q0 a0 a1 (j+2) (by omega)]; field_simp; all_goals ring
  · rw [q4 a0 a1 j h, q0 a0 a1 (j+1) (by omega), q1 a0 a1 (j+2) (by omega)]; field_simp; all_goals ring

/-- **`K_4 = 0` at every column.** -/
theorem quid5fn_four {a0 a1 : ℚ} (hD : a0 * a1 - 1 ≠ 0) (j : ℤ) :
    Kc (quid5fn a0 a1) j 4 = 0 := by
  have h3 := quid5fn_three hD j
  rw [Kc_three] at h3
  rw [Kc_four, h3]
  rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4)
    with h | h | h | h | h
  · rw [q0 a0 a1 j h, q1 a0 a1 (j+1) (by omega), q3 a0 a1 (j+3) (by omega)]; all_goals ring
  · rw [q1 a0 a1 j h, q2 a0 a1 (j+1) (by omega), q4 a0 a1 (j+3) (by omega)]; field_simp; all_goals ring
  · rw [q2 a0 a1 j h, q3 a0 a1 (j+1) (by omega), q0 a0 a1 (j+3) (by omega)]; field_simp; all_goals ring
  · rw [q3 a0 a1 j h, q4 a0 a1 (j+1) (by omega), q1 a0 a1 (j+3) (by omega)]; field_simp; all_goals ring
  · rw [q4 a0 a1 j h, q0 a0 a1 (j+1) (by omega), q2 a0 a1 (j+3) (by omega)]; field_simp; all_goals ring

/-- **The construction.** A pair `(a₀,a₁)` with `a₀a₁ ≠ 1` generates a frieze of width `5`.
This is the analytic half of the converse of Proposition `prop:w5cond`; the lattice
condition, that the entries lie in `(1/N)ℤ`, is not proved here. -/
theorem width5_build {a0 a1 : ℚ} (hD : a0 * a1 - 1 ≠ 0) :
    IsFrieze 5 (friezeOf (quid5fn a0 a1)) := by
  refine friezeOf_isFrieze (by omega) ?_ (fun j => quid5fn_three hD j)
    (fun j => quid5fn_four hD j)
  intro j
  have h5 : ((5 : ℕ) : ℤ) = 5 := by norm_num
  rw [h5]
  exact quid5fn_periodic a0 a1 j

end VicoEnum
