/-
  VicoEnum/Width6.lean

  Sufficiency at width 6: what the glide-fixed row costs.

  A width-6 frieze has interior rows 2, 3 and 4. The glide symmetry exchanges rows 2 and
  4 and fixes row 3, so beyond the quiddity cycle there is exactly one further row to
  control. This module makes both halves of that statement precise.

  Row 4 costs nothing: `w6_row4` shows that the width-6 continuant of three consecutive
  quiddity entries is again a quiddity entry, at each of the six positions. So row 4 is
  row 2 permuted, and imposes no condition that row 2 does not already impose.

  Row 3 costs three conditions, not six. Its entries are `a_j a_{j+1} - 1`, and
  `w6_glide` shows `a_j a_{j+1} = a_{j+3} a_{j+4}`, so the six products collapse to three.
  Writing `a_j = p_j / N`, `row3_lattice_iff` says the entry lies in `(1/N)ℤ` exactly when
  `N ∣ p_j p_{j+1}`, and `row3_pos_iff` says it is positive exactly when `N² < p_j p_{j+1}`.

  Together with `general_reduction` at `n = 6`, which handles the quiddity, this is a
  complete criterion: `(p₀,p₁,p₂)` comes from a positive width-6 frieze over `(1/N)ℤ` if
  and only if, with `e := (p₀p₁p₂ - N²(p₀+p₂))/N²` and `p₃ := p₀p₁/e`,

    (a)  N² ∣ p₀p₁p₂ - N²(p₀+p₂)  and  e > 0,
    (b)  e ∣ p₀p₁  and  e ∣ p₁p₂,
    (c)  N ∣ p₀p₁,  N ∣ p₁p₂,  N ∣ p₂p₃,
    (d)  N² < p₀p₁,  N² < p₁p₂,  N² < p₂p₃.

  Both directions are proved in the paper (Theorem `thm:w6count`): necessity from
  Proposition `prop:param` with the two `row3` lemmas, and sufficiency because rows 2 and 3
  determine the array, row 4 is row 2 shifted by the glide, and rows 1 and 5 are constant.
  Neither direction is formalised here; what this file carries is the row-3 criterion that
  both use. As a consistency check the criterion was enumerated over the Cuntz--Holm box
  `p_j ≤ 2N³+2N²` for `N ≤ 6`, reproducing `T(N,6) = 14, 102, 259, 487, 504, 1197` with no
  candidate escaping the box (`code/w6_sufficiency.py`).
-/
import VicoEnum.GeneralWidth

namespace VicoEnum

/-! ## The two rows below the quiddity -/

/-- The width-6 frieze continuant `K₃(x,y,z) = z(xy-1) - x`. Row 4 of a width-6 frieze is
`K3` applied to three consecutive quiddity entries. -/
def K3 (x y z : ℚ) : ℚ := z * (x * y - 1) - x

/-- **Row 4 imposes nothing.** At each of the six positions the width-6 continuant of
three consecutive quiddity entries is again a quiddity entry, four steps along. So row 4
is a cyclic shift of row 2, and a quiddity cycle in `(1/N)ℤ` puts row 4 in `(1/N)ℤ` for
free. The first identity is the parameterisation `a₄ = K₃(a₀,a₁,a₂)` itself; the other
five are its cyclic conjugates. -/
theorem w6_row4 {a₀ a₁ a₂ a₃ a₄ a₅ : ℚ} (hD : a₄ ≠ 0)
    (h4 : a₄ = a₂ * (a₀ * a₁ - 1) - a₀) (h3 : a₃ = a₀ * a₁ / a₄)
    (h5 : a₅ = a₁ * a₂ / a₄) :
    K3 a₀ a₁ a₂ = a₄ ∧ K3 a₁ a₂ a₃ = a₅ ∧ K3 a₂ a₃ a₄ = a₀ ∧
      K3 a₃ a₄ a₅ = a₁ ∧ K3 a₄ a₅ a₀ = a₂ ∧ K3 a₅ a₀ a₁ = a₃ := by
  subst h3; subst h5; subst h4
  refine ⟨by simp only [K3], ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [K3]
      field_simp
      ring

/-- **Row 3 has period 3, not 6.** The glide symmetry fixes row 3, so its entries repeat
after three steps: `a_j a_{j+1} = a_{j+3} a_{j+4}`. The six conditions carried by row 3
therefore collapse to three. This needs only the shape of `a₃` and `a₅`, not the closing
condition. -/
theorem w6_glide {a₀ a₁ a₂ a₃ a₄ a₅ : ℚ} (hD : a₄ ≠ 0)
    (h3 : a₃ = a₀ * a₁ / a₄) (h5 : a₅ = a₁ * a₂ / a₄) :
    a₀ * a₁ = a₃ * a₄ ∧ a₁ * a₂ = a₄ * a₅ ∧ a₂ * a₃ = a₅ * a₀ := by
  subst h3; subst h5
  refine ⟨by field_simp, by field_simp, by field_simp; ring⟩

/-! ## What row 3 costs, arithmetically -/

/-- **The row-3 lattice condition.** With `a_j = p/N` and `a_{j+1} = q/N`, the row-3 entry
`a_j a_{j+1} - 1` lies in `(1/N)ℤ` if and only if `N ∣ pq`. This is the extra divisibility
that width 5 does not have, and Remark 2.3 locates it: at width 5 the glide exchanges the
two interior rows, at width 6 it fixes one. -/
theorem row3_lattice_iff {N : ℕ} (hN : 0 < N) (p q : ℤ) :
    InLattice N (((p : ℚ) / N) * ((q : ℚ) / N) - 1) ↔ (N : ℤ) ∣ p * q := by
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have key : ∀ m : ℤ, ((N : ℚ) * (((p : ℚ) / N) * ((q : ℚ) / N) - 1) = (m : ℚ))
      ↔ p * q = (N : ℤ) * (m + N) := by
    intro m
    rw [show ((N : ℚ) * (((p : ℚ) / N) * ((q : ℚ) / N) - 1))
        = ((p : ℚ) * (q : ℚ) - (N : ℚ) ^ 2) / (N : ℚ) by field_simp; ring,
      div_eq_iff hN']
    constructor
    · intro h
      have hc : ((p * q : ℤ) : ℚ) = (((N : ℤ) * (m + N) : ℤ) : ℚ) := by
        push_cast; linear_combination h
      exact_mod_cast hc
    · intro h
      have hc : ((p * q : ℤ) : ℚ) = (((N : ℤ) * (m + N) : ℤ) : ℚ) := by exact_mod_cast h
      push_cast at hc
      linear_combination hc
  rw [inLattice_iff hN]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m + N, (key m).mp hm⟩
  · rintro ⟨t, ht⟩
    exact ⟨t - N, (key (t - N)).mpr (by rw [ht]; ring)⟩

/-- **The row-3 positivity condition.** The same entry is positive if and only if
`N² < pq`. -/
theorem row3_pos_iff {N : ℕ} (hN : 0 < N) (p q : ℤ) :
    0 < ((p : ℚ) / N) * ((q : ℚ) / N) - 1 ↔ (N : ℤ) * (N : ℤ) < p * q := by
  have hN' : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hpos : (0 : ℚ) < (N : ℚ) * (N : ℚ) := by positivity
  rw [sub_pos, div_mul_div_comm, one_lt_div hpos]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- **The six row-3 products are three.** In integer terms: with `e p₃ = p₀p₁`, `p₄ = e`
and `e p₅ = p₁p₂`, the products `p_j p_{j+1}` around the cycle take only the three values
`p₀p₁`, `p₁p₂`, `p₂p₃`. This is `w6_glide` after clearing denominators. -/
theorem w6_row3_reduce {e p₀ p₁ p₂ p₃ p₄ p₅ : ℤ} (he : e ≠ 0)
    (h3 : e * p₃ = p₀ * p₁) (h4 : p₄ = e) (h5 : e * p₅ = p₁ * p₂) :
    p₃ * p₄ = p₀ * p₁ ∧ p₄ * p₅ = p₁ * p₂ ∧ p₂ * p₃ = p₅ * p₀ := by
  refine ⟨by rw [h4]; linarith [h3], by rw [h4]; linarith [h5], ?_⟩
  have h : e * (p₂ * p₃ - p₅ * p₀) = 0 := by linear_combination p₂ * h3 - p₀ * h5
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 he
  · linarith [h1]

/-- **The width-6 criterion for row 3.** The six lattice conditions carried by row 3 are
equivalent to the three on `p₀p₁`, `p₁p₂`, `p₂p₃`. Combined with `general_reduction` at
`n = 6`, which handles the quiddity, and with `w6_row4`, which disposes of row 4, this is
the whole of the width-6 condition. -/
theorem w6_row3_criterion {N : ℤ} {e p₀ p₁ p₂ p₃ p₄ p₅ : ℤ} (he : e ≠ 0)
    (h3 : e * p₃ = p₀ * p₁) (h4 : p₄ = e) (h5 : e * p₅ = p₁ * p₂) :
    (N ∣ p₀ * p₁ ∧ N ∣ p₁ * p₂ ∧ N ∣ p₂ * p₃) ↔
      (N ∣ p₀ * p₁ ∧ N ∣ p₁ * p₂ ∧ N ∣ p₂ * p₃ ∧
        N ∣ p₃ * p₄ ∧ N ∣ p₄ * p₅ ∧ N ∣ p₅ * p₀) := by
  obtain ⟨e34, e45, e50⟩ := w6_row3_reduce he h3 h4 h5
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, c, by rw [e34]; exact a, by rw [e45]; exact b, by rw [← e50]; exact c⟩
  · rintro ⟨a, b, c, -, -, -⟩
    exact ⟨a, b, c⟩

end VicoEnum
