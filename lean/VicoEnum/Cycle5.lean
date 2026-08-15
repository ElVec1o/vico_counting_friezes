/-
  VicoEnum/Cycle5.lean

  The rotation on numerator pairs closes after five steps.

  `W5_rot` shows the step preserves `W5`. What is needed to feed
  `five_dvd_card_of_free` is that iterating it five times is the identity. Division in `ℕ`
  makes the iterates awkward, so the five numerators of a width-5 quiddity are characterised
  by three division-free relations:

      p₀p₁ = N² + N p₃,     p₂p₃ = N(p₀+N),     p₄p₃ = N(p₁+N),

  which are the parameterisation `a₃ = a₀a₁-1`, `a₂a₃ = a₀+1`, `a₄a₃ = a₁+1` cleared of
  denominators. From them the two remaining steps are forced: the step out of `(p₃,p₄)`
  returns `p₀`, and the step out of `(p₄,p₀)` returns `p₁`, both by cancelling `p₁` and `p₂`.

  Checked against the parameterisation for the 724 pairs satisfying `W5` with `N < 11` and
  `p₀,p₁ < 160`, with no discrepancy.
-/
import VicoEnum.RotPair

namespace VicoEnum

/-- The five numerators of a width-5 quiddity cycle, characterised without division. -/
structure Quid5 (N p0 p1 p2 p3 p4 : ℕ) : Prop where
  pos1 : 0 < p1
  pos2 : 0 < p2
  pos3 : 0 < p3
  /-- `a₃ = a₀a₁ - 1`, cleared. -/
  mid : p0 * p1 = N ^ 2 + N * p3
  /-- `a₂a₃ = a₀ + 1`, cleared. -/
  left : p2 * p3 = N * (p0 + N)
  /-- `a₄a₃ = a₁ + 1`, cleared. -/
  right : p4 * p3 = N * (p1 + N)

/-- The step out of `(p₃,p₄)` returns `p₀`. Its denominator is `p₃p₄ - N² = Np₁`, and the
numerator `N²(p₃+N)` is `N·p₀p₁`. -/
theorem rot_step_five {N p0 p1 p2 p3 p4 p5 : ℕ} (hN : 0 < N)
    (h : Quid5 N p0 p1 p2 p3 p4) (h5 : RotStep N p3 p4 p5) : p5 = p0 := by
  simp only [RotStep] at h5
  have hden : p3 * p4 - N ^ 2 = N * p1 := by
    have : p3 * p4 = N * p1 + N ^ 2 := by
      have := h.right; nlinarith [this]
    omega
  rw [hden] at h5
  have hnum : N ^ 2 * (p3 + N) = N * (p0 * p1) := by rw [h.mid]; ring
  rw [hnum] at h5
  -- p5 * (N * p1) = N * (p0 * p1)
  have hcan : p5 * p1 = p0 * p1 := by
    have hNpos : 0 < N := hN
    have h1 : N * (p5 * p1) = N * (p0 * p1) := by rw [← h5]; ring
    exact Nat.eq_of_mul_eq_mul_left hNpos h1
  exact Nat.eq_of_mul_eq_mul_right h.pos1 hcan

/-- The step out of `(p₄,p₀)` returns `p₁`. Its denominator is `p₄p₀ - N² = Np₂`, obtained
by cancelling `p₃`, and the numerator matches `N·p₁p₂` the same way. -/
theorem rot_step_six {N p0 p1 p2 p3 p4 p6 : ℕ} (hN : 0 < N)
    (h : Quid5 N p0 p1 p2 p3 p4) (h6 : RotStep N p4 p0 p6) : p6 = p1 := by
  simp only [RotStep] at h6
  -- (p4 p0 - N²) p3 = N p2 p3, so p4 p0 - N² = N p2
  have hd : p4 * p0 * p3 = N ^ 2 * (N + p3 + p0) := by
    calc p4 * p0 * p3 = p0 * (p4 * p3) := by ring
      _ = p0 * (N * (p1 + N)) := by rw [h.right]
      _ = N * (p0 * p1) + N ^ 2 * p0 := by ring
      _ = N * (N ^ 2 + N * p3) + N ^ 2 * p0 := by rw [h.mid]
      _ = N ^ 2 * (N + p3 + p0) := by ring
  have hden : p4 * p0 - N ^ 2 = N * p2 := by
    have h1 : (p4 * p0) * p3 = (N ^ 2 + N * p2) * p3 := by
      rw [hd]
      calc N ^ 2 * (N + p3 + p0) = N ^ 2 * p3 + N * (N * (p0 + N)) := by ring
        _ = N ^ 2 * p3 + N * (p2 * p3) := by rw [h.left]
        _ = (N ^ 2 + N * p2) * p3 := by ring
    have h2 : p4 * p0 = N ^ 2 + N * p2 := Nat.eq_of_mul_eq_mul_right h.pos3 h1
    omega
  rw [hden] at h6
  -- p6 * (N p2) = N²(p4+N), and N²(p4+N) = N (p1 p2) by cancelling p3
  have hnum : N ^ 2 * (p4 + N) = N * (p1 * p2) := by
    have h1 : (N ^ 2 * (p4 + N)) * p3 = (N * (p1 * p2)) * p3 := by
      calc (N ^ 2 * (p4 + N)) * p3 = N ^ 2 * (p4 * p3) + N ^ 3 * p3 := by ring
        _ = N ^ 2 * (N * (p1 + N)) + N ^ 3 * p3 := by rw [h.right]
        _ = N ^ 2 * (N * p1 + (N ^ 2 + N * p3)) := by ring
        _ = N ^ 2 * (N * p1 + p0 * p1) := by rw [← h.mid]
        _ = N * (p1 * (N * (p0 + N))) := by ring
        _ = N * (p1 * (p2 * p3)) := by rw [h.left]
        _ = (N * (p1 * p2)) * p3 := by ring
    exact Nat.eq_of_mul_eq_mul_right h.pos3 h1
  rw [hnum] at h6
  have hcan : p6 * p2 = p1 * p2 := by
    have h1 : N * (p6 * p2) = N * (p1 * p2) := by rw [← h6]; ring
    exact Nat.eq_of_mul_eq_mul_left hN h1
  exact Nat.eq_of_mul_eq_mul_right h.pos2 hcan

/-- **The rotation closes after five steps.** Starting from `(p₀,p₁)` and applying the step
five times returns `(p₀,p₁)`. The first three steps are recorded in `Quid5`, which says that
`p₂`, `p₃`, `p₄` are the third, fourth and fifth numerators; the last two steps are then
forced, and that is what is proved. -/
theorem rot_five_closes {N p0 p1 p2 p3 p4 p5 p6 : ℕ} (hN : 0 < N)
    (h : Quid5 N p0 p1 p2 p3 p4)
    (h5 : RotStep N p3 p4 p5) (h6 : RotStep N p4 p5 p6) : p5 = p0 ∧ p6 = p1 := by
  have e5 : p5 = p0 := rot_step_five hN h h5
  subst e5
  exact ⟨rfl, rot_step_six hN h h6⟩

end VicoEnum
