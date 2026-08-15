/-
  VicoEnum/Width6Model.lean

  A model of `IsFrieze 6`, so the width-6 results are not vacuously true.

  At width 5 this role is played by `cc5_positive`. Width 6 had no witness at all, so
  `width6_from_frieze` and `width6_fourth` both quantified over a class not known to be
  inhabited. The Conway--Coxeter frieze with quiddity `(1,4,1,2,2,2)` supplies one. It is
  taken in preference to `(1,3,1,3,1,3)`, which is also valid but has period `2`, so it would
  test the six closing identities on only three distinct columns.

  In the labels of `W6` its numerators at `N = 1` are `p,q,r,c₃,e,c₅ = 1,4,1,2,2,2`, giving
  `pqr = 4 = N²(e+p+r)`, `e ∣ pq`, `e ∣ qr` and `e ∣ N(p+r)` with `e = 2`, so the fourth
  divisibility is tested with a nontrivial `e` rather than `e = 1`.
-/
import VicoEnum.Width6Fourth
import VicoEnum.Width5Build

namespace VicoEnum

/-- The quiddity `(1,4,1,2,2,2)`, extended `6`-periodically. -/
noncomputable def quid6 : ℤ → ℚ := fun j =>
  if j % 6 = 0 then 1 else if j % 6 = 1 then 4 else if j % 6 = 2 then 1
  else if j % 6 = 3 then 2 else if j % 6 = 4 then 2 else 2

theorem quid6_periodic (j : ℤ) : quid6 (j + 6) = quid6 j := by
  simp only [quid6, show (j + 6) % 6 = j % 6 from by omega]

theorem s0 (j : ℤ) (h : j % 6 = 0) : quid6 j = 1 := by simp [quid6, h]
theorem s1 (j : ℤ) (h : j % 6 = 1) : quid6 j = 4 := by simp [quid6, h]
theorem s2 (j : ℤ) (h : j % 6 = 2) : quid6 j = 1 := by simp [quid6, h]
theorem s3 (j : ℤ) (h : j % 6 = 3) : quid6 j = 2 := by simp [quid6, h]
theorem s4 (j : ℤ) (h : j % 6 = 4) : quid6 j = 2 := by simp [quid6, h]
theorem s5 (j : ℤ) (h : j % 6 = 5) : quid6 j = 2 := by simp [quid6, h]

/-- The length-five continuant. -/
theorem Kc_five (a : ℤ → ℚ) (j : ℤ) :
    Kc a j 5 = a (j + 4) * (a (j + 3) * (a (j + 2) * (a (j + 1) * a j - 1) - a j)
        - (a (j + 1) * a j - 1))
      - (a (j + 2) * (a (j + 1) * a j - 1) - a j) := by
  have hi : j + ((3 : ℕ) : ℤ) + 1 = j + 4 := by push_cast; ring
  rw [Kc_succ_succ a j 3, Kc_four, Kc_three, hi]

/-- **`K₄ = 1` at every column.** -/
theorem quid6_four (j : ℤ) : Kc quid6 j 4 = 1 := by
  rw [Kc_four]
  rcases (by omega : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5)
    with h | h | h | h | h | h
  · rw [s0 j h, s1 (j+1) (by omega), s2 (j+2) (by omega), s3 (j+3) (by omega)]; norm_num
  · rw [s1 j h, s2 (j+1) (by omega), s3 (j+2) (by omega), s4 (j+3) (by omega)]; norm_num
  · rw [s2 j h, s3 (j+1) (by omega), s4 (j+2) (by omega), s5 (j+3) (by omega)]; norm_num
  · rw [s3 j h, s4 (j+1) (by omega), s5 (j+2) (by omega), s0 (j+3) (by omega)]; norm_num
  · rw [s4 j h, s5 (j+1) (by omega), s0 (j+2) (by omega), s1 (j+3) (by omega)]; norm_num
  · rw [s5 j h, s0 (j+1) (by omega), s1 (j+2) (by omega), s2 (j+3) (by omega)]; norm_num

/-- **`K₅ = 0` at every column.** -/
theorem quid6_five (j : ℤ) : Kc quid6 j 5 = 0 := by
  rw [Kc_five]
  rcases (by omega : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5)
    with h | h | h | h | h | h
  · rw [s0 j h, s1 (j+1) (by omega), s2 (j+2) (by omega), s3 (j+3) (by omega),
      s4 (j+4) (by omega)]; norm_num
  · rw [s1 j h, s2 (j+1) (by omega), s3 (j+2) (by omega), s4 (j+3) (by omega),
      s5 (j+4) (by omega)]; norm_num
  · rw [s2 j h, s3 (j+1) (by omega), s4 (j+2) (by omega), s5 (j+3) (by omega),
      s0 (j+4) (by omega)]; norm_num
  · rw [s3 j h, s4 (j+1) (by omega), s5 (j+2) (by omega), s0 (j+3) (by omega),
      s1 (j+4) (by omega)]; norm_num
  · rw [s4 j h, s5 (j+1) (by omega), s0 (j+2) (by omega), s1 (j+3) (by omega),
      s2 (j+4) (by omega)]; norm_num
  · rw [s5 j h, s0 (j+1) (by omega), s1 (j+2) (by omega), s2 (j+3) (by omega),
      s3 (j+4) (by omega)]; norm_num

/-- **The model.** -/
noncomputable def cc6 : ℕ → ℤ → ℚ := friezeOf quid6

theorem cc6_isFrieze : IsFrieze 6 cc6 := by
  refine friezeOf_isFrieze (by omega) ?_ (fun j => quid6_four j) (fun j => quid6_five j)
  intro j
  have h6 : ((6 : ℕ) : ℤ) = 6 := by norm_num
  rw [h6]
  exact quid6_periodic j

/-- **The interior is positive**, so `IsFrieze 6` and the positivity hypothesis of
`width6_from_frieze` and `width6_fourth` are jointly satisfiable. -/
theorem cc6_positive : ∀ r j, 0 < r → r < 6 → 0 < cc6 r j := by
  intro r j h0 h6
  rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) with rfl | rfl | rfl | rfl | rfl
  · exact one_pos
  · show 0 < quid6 j
    rcases (by omega : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5)
      with h | h | h | h | h | h
    · rw [s0 j h]; norm_num
    · rw [s1 j h]; norm_num
    · rw [s2 j h]; norm_num
    · rw [s3 j h]; norm_num
    · rw [s4 j h]; norm_num
    · rw [s5 j h]; norm_num
  · show 0 < Kc quid6 j 2
    rw [Kc_two]
    rcases (by omega : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5)
      with h | h | h | h | h | h
    · rw [s0 j h, s1 (j+1) (by omega)]; norm_num
    · rw [s1 j h, s2 (j+1) (by omega)]; norm_num
    · rw [s2 j h, s3 (j+1) (by omega)]; norm_num
    · rw [s3 j h, s4 (j+1) (by omega)]; norm_num
    · rw [s4 j h, s5 (j+1) (by omega)]; norm_num
    · rw [s5 j h, s0 (j+1) (by omega)]; norm_num
  · show 0 < Kc quid6 j 3
    rw [Kc_three]
    rcases (by omega : j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 2 ∨ j % 6 = 3 ∨ j % 6 = 4 ∨ j % 6 = 5)
      with h | h | h | h | h | h
    · rw [s0 j h, s1 (j+1) (by omega), s2 (j+2) (by omega)]; norm_num
    · rw [s1 j h, s2 (j+1) (by omega), s3 (j+2) (by omega)]; norm_num
    · rw [s2 j h, s3 (j+1) (by omega), s4 (j+2) (by omega)]; norm_num
    · rw [s3 j h, s4 (j+1) (by omega), s5 (j+2) (by omega)]; norm_num
    · rw [s4 j h, s5 (j+1) (by omega), s0 (j+2) (by omega)]; norm_num
    · rw [s5 j h, s0 (j+1) (by omega), s1 (j+2) (by omega)]; norm_num
  · show 0 < Kc quid6 j 4
    rw [quid6_four j]; norm_num

/-! ## Non-vacuity of the width-6 results

`width6_fourth` instantiated at `cc6`. The point is that `e = 2` here, so the divisibility
`e ∣ N(p+r)` is tested with a nontrivial modulus rather than holding for free. -/

theorem cc6_quid : ((1:ℕ) : ℚ) * quiddity cc6 0 = (1 : ℕ) ∧
    ((1:ℕ) : ℚ) * quiddity cc6 1 = (4 : ℕ) ∧ ((1:ℕ) : ℚ) * quiddity cc6 2 = (1 : ℕ) ∧
    ((1:ℕ) : ℚ) * quiddity cc6 3 = (2 : ℕ) ∧ ((1:ℕ) : ℚ) * quiddity cc6 4 = (2 : ℕ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (1:ℚ) * quid6 0 = 1; rw [s0 0 (by norm_num)]; norm_num
  · show (1:ℚ) * quid6 1 = 4; rw [s1 1 (by norm_num)]; norm_num
  · show (1:ℚ) * quid6 2 = 1; rw [s2 2 (by norm_num)]; norm_num
  · show (1:ℚ) * quid6 3 = 2; rw [s3 3 (by norm_num)]; norm_num
  · show (1:ℚ) * quid6 4 = 2; rw [s4 4 (by norm_num)]; norm_num

theorem cc6_row3 : InLattice 1 (cc6 3 2) := by
  refine ⟨1, ?_⟩
  show Kc quid6 2 2 = _
  rw [Kc_two, s3 (2+1) (by norm_num), s2 2 (by norm_num)]; norm_num

/-- **`width6_fourth` is not vacuous.** -/
theorem width6_fourth_nonvacuous : (2:ℕ) ∣ 1 * (1 + 1) :=
  width6_fourth (N := 1) (by norm_num) cc6_isFrieze cc6_positive
    (p := 1) (q := 4) (r := 1) (c₃ := 2) (e := 2)
    cc6_quid.1 cc6_quid.2.1 cc6_quid.2.2.1 cc6_quid.2.2.2.1 cc6_quid.2.2.2.2 cc6_row3

end VicoEnum
