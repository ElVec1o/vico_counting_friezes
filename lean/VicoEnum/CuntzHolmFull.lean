/-
  VicoEnum/CuntzHolmFull.lean

  The Cuntz--Holm bound, proved by a telescoping sum.

  Cuntz and Holm (J. Comb. Algebra 3 (2019), Theorem 3.6) argue by contradiction,
  running a descent that carries a lower bound along one row and an upper bound along
  the other. The two are mutually recursive, which makes the induction awkward.

  Setting `s i = |x (i+1)| / |y i|` removes the coupling. Dividing the diamond
  relation by `|y i| * |y (i+1)|` gives

      s i  ≤  1 / (|y i| * |y (i+1)|)  +  s (i+1),

  a one-sided recurrence. Telescoping it from `s 0 = |x 1|`, which holds because
  `y 0 = 1`, down to `s n = 1 / |y n| ≤ 1/M`, and bounding the first gap by `1/M` and
  the remaining `n-1` gaps by `1/M²`, yields

      |x 1|  ≤  2/M + (n-1)/M²  =  ((n-1) + 2M)/M²,

  which is the bound. The proof is direct rather than by contradiction.
-/
import VicoEnum.CuntzHolm

namespace VicoEnum

/-- The ratio `s i = |x (i+1)| / |y i|`. -/
noncomputable def chS (x y : ℕ → ℚ) (i : ℕ) : ℚ := |x (i + 1)| / |y i|

/-- **The one-sided recurrence.** The diamond relation, divided by the two second-row
absolute values, bounds `s i` by `s (i+1)` plus one gap term. -/
theorem chS_step {x y : ℕ → ℚ} {i : ℕ}
    (hyi : 0 < |y i|) (hyi1 : 0 < |y (i + 1)|)
    (h : x (i + 1) * y (i + 1) = 1 + x (i + 2) * y i) :
    chS x y i ≤ 1 / (|y i| * |y (i + 1)|) + chS x y (i + 1) := by
  have key : |x (i + 1)| * |y (i + 1)| ≤ 1 + |x (i + 2)| * |y i| := by
    calc |x (i + 1)| * |y (i + 1)| = |x (i + 1) * y (i + 1)| := (abs_mul _ _).symm
      _ = |1 + x (i + 2) * y i| := by rw [h]
      _ ≤ |(1 : ℚ)| + |x (i + 2) * y i| := abs_add _ _
      _ = 1 + |x (i + 2)| * |y i| := by rw [abs_mul]; norm_num
  have hd : (0 : ℚ) < |y i| * |y (i + 1)| := mul_pos hyi hyi1
  have ha : |y i| ≠ 0 := ne_of_gt hyi
  have hb : |y (i + 1)| ≠ 0 := ne_of_gt hyi1
  have h1 : chS x y i = (|x (i + 1)| * |y (i + 1)|) / (|y i| * |y (i + 1)|) := by
    unfold chS; field_simp; ring
  have h2 : 1 / (|y i| * |y (i + 1)|) + chS x y (i + 1)
      = (1 + |x (i + 2)| * |y i|) / (|y i| * |y (i + 1)|) := by
    unfold chS; field_simp; ring
  rw [h1, h2]
  gcongr

/-- Telescoped form: after `k` steps, `s 0` is bounded by `s k` plus the accumulated
gaps, each of which is at most `1/M²` after the first, which is at most `1/M`. -/
theorem chS_telescope {M : ℚ} (hM : 0 < M) {x y : ℕ → ℚ} {n : ℕ}
    (hy0 : y 0 = 1)
    (hyM : ∀ i, 1 ≤ i → i ≤ n → M ≤ |y i|)
    (hrel : ∀ i, i + 1 ≤ n → x (i + 1) * y (i + 1) = 1 + x (i + 2) * y i) :
    ∀ k, 1 ≤ k → k ≤ n →
      chS x y 0 ≤ chS x y k + 1 / M + ((k : ℚ) - 1) / M ^ 2 := by
  have hy0abs : |y 0| = 1 := by rw [hy0]; norm_num
  have hpos : ∀ i, i ≤ n → 0 < |y i| := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · rw [hy0abs]; norm_num
    · exact lt_of_lt_of_le hM (hyM i hi1 hi)
  intro k
  induction k with
  | zero => intro h; omega
  | succ j ih =>
    intro _ hjn
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · -- first step: the gap is 1/(|y 0| |y 1|) = 1/|y 1| ≤ 1/M
      have h1 := chS_step (hpos 0 (by omega)) (hpos 1 hjn) (hrel 0 hjn)
      have hy1 : M ≤ |y 1| := hyM 1 (by omega) hjn
      have hgap : 1 / (|y 0| * |y 1|) ≤ 1 / M := by
        rw [hy0abs, one_mul]
        exact one_div_le_one_div_of_le hM hy1
      have hzero : ((0 : ℕ) + 1 : ℕ) = 1 := rfl
      simp only [hzero, Nat.cast_one, sub_self, zero_div, add_zero]
      linarith [h1, hgap]
    · -- later steps: the gap is at most 1/M²
      have hjn' : j ≤ n := by omega
      have hprev := ih (by omega) hjn'
      have h1 := chS_step (hpos j hjn') (hpos (j + 1) hjn) (hrel j hjn)
      have hyj : M ≤ |y j| := hyM j hj1 hjn'
      have hyj1 : M ≤ |y (j + 1)| := hyM (j + 1) (by omega) hjn
      have hgap : 1 / (|y j| * |y (j + 1)|) ≤ 1 / M ^ 2 := by
        have : M ^ 2 ≤ |y j| * |y (j + 1)| := by nlinarith [hM]
        exact one_div_le_one_div_of_le (by positivity) this
      push_cast
      have hsplit : ((j : ℚ) + 1 - 1) / M ^ 2 = ((j : ℚ) - 1) / M ^ 2 + 1 / M ^ 2 := by
        field_simp
      rw [hsplit]
      linarith [hprev, h1, hgap]

/-- **Theorem 3.6 of Cuntz--Holm**, in the two-row form, proved directly.

Given two consecutive rows of a frieze of height `n`, with `y 0 = 1`, every entry of
the second row of absolute value at least `M`, and the terminal condition
`x (n+1) = 1`, the leading entry satisfies `|x 1| ≤ ((n-1) + 2M)/M²`. -/
theorem cuntz_holm_bound {M : ℚ} (hM : 0 < M) {x y : ℕ → ℚ} {n : ℕ} (hn : 1 ≤ n)
    (hy0 : y 0 = 1)
    (hyM : ∀ i, 1 ≤ i → i ≤ n → M ≤ |y i|)
    (hrel : ∀ i, i + 1 ≤ n → x (i + 1) * y (i + 1) = 1 + x (i + 2) * y i)
    (hxn : x (n + 1) = 1) :
    |x 1| ≤ ((n : ℚ) - 1 + 2 * M) / M ^ 2 := by
  have hy0abs : |y 0| = 1 := by rw [hy0]; norm_num
  have hs0 : chS x y 0 = |x 1| := by unfold chS; rw [hy0abs]; norm_num
  have hyn : M ≤ |y n| := hyM n hn le_rfl
  have hynpos : 0 < |y n| := lt_of_lt_of_le hM hyn
  have hsn : chS x y n ≤ 1 / M := by
    have : chS x y n = 1 / |y n| := by unfold chS; rw [hxn]; norm_num
    rw [this]
    exact one_div_le_one_div_of_le hM hyn
  have := chS_telescope hM hy0 hyM hrel n hn le_rfl
  rw [hs0] at this
  have hMne : M ≠ 0 := hM.ne'
  have hfin : |x 1| ≤ 1 / M + 1 / M + ((n : ℚ) - 1) / M ^ 2 := by linarith [this, hsn]
  have heq : 1 / M + 1 / M + ((n : ℚ) - 1) / M ^ 2 = ((n : ℚ) - 1 + 2 * M) / M ^ 2 := by
    field_simp; ring
  linarith [hfin, heq.le, heq.ge]

end VicoEnum
