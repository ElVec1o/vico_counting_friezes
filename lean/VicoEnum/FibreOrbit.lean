/-
  VicoEnum/FibreOrbit.lean

  The fibres of the map from paths to friezes are the `SL₂(ℤ)` orbits, as one statement.

  `Transfer` shows the map relating two paths with the same frieze is additive and
  homogeneous. That makes it a matrix, but leaves the matrix implicit. This file extracts its
  four entries, proves the determinant is one, and states the fibre description as a single
  biconditional:

      (the two paths have the same frieze)  ↔  (they differ by an integer matrix of
                                                determinant one)

  with no quotient types and no prose assembly. The forward direction needs minimality, in
  the form of a B\'ezout witness, and one nonzero determinant; the backward direction is
  `fdet_sl2_invariant` and needs nothing.
-/
import VicoEnum.Transfer

namespace VicoEnum

/-- The determinant of a plane matrix acts on `fdet` by multiplication. A ring identity. -/
theorem fdet_linear_map (m₁₁ m₁₂ m₂₁ m₂₂ : ℤ) (x y : ℤ × ℤ) :
    fdet (m₁₁ * x.1 + m₁₂ * x.2, m₂₁ * x.1 + m₂₂ * x.2)
         (m₁₁ * y.1 + m₁₂ * y.2, m₂₁ * y.1 + m₂₂ * y.2)
      = (m₁₁ * m₂₂ - m₁₂ * m₂₁) * fdet x y := by
  simp only [fdet]; ring

/-- The four entries of the transfer matrix, read off `transferMap` by linearity. -/
def tm₁₁ (a b : ℤ) (p q r s P Q Rt S : ℤ × ℤ) : ℤ :=
  a * (-p.2) * Q.1 - a * (-q.2) * P.1 + b * (-r.2) * S.1 - b * (-s.2) * Rt.1
def tm₁₂ (a b : ℤ) (p q r s P Q Rt S : ℤ × ℤ) : ℤ :=
  a * p.1 * Q.1 - a * q.1 * P.1 + b * r.1 * S.1 - b * s.1 * Rt.1
def tm₂₁ (a b : ℤ) (p q r s P Q Rt S : ℤ × ℤ) : ℤ :=
  a * (-p.2) * Q.2 - a * (-q.2) * P.2 + b * (-r.2) * S.2 - b * (-s.2) * Rt.2
def tm₂₂ (a b : ℤ) (p q r s P Q Rt S : ℤ × ℤ) : ℤ :=
  a * p.1 * Q.2 - a * q.1 * P.2 + b * r.1 * S.2 - b * s.1 * Rt.2

/-- **The transfer is that matrix.** -/
theorem transferMap_matrix (a b : ℤ) (p q r s P Q Rt S x : ℤ × ℤ) :
    transferMap a b p q r s P Q Rt S x
      = (tm₁₁ a b p q r s P Q Rt S * x.1 + tm₁₂ a b p q r s P Q Rt S * x.2,
         tm₂₁ a b p q r s P Q Rt S * x.1 + tm₂₂ a b p q r s P Q Rt S * x.2) := by
  simp only [transferMap, fdet, tm₁₁, tm₁₂, tm₂₁, tm₂₂]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- **The fibres are the `SL₂(ℤ)` orbits.** Two paths have the same frieze exactly when they
differ by an integer matrix of determinant one.

The forward direction uses minimality, as a B\'ezout witness `a·[v i₀, v j₀] + b·[v i₁, v j₁] = 1`,
and one nonzero determinant, which a clockwise path supplies. The backward direction holds
for any paths. This is the quotient statement of the classification, as a single Lean
theorem. -/
theorem fibre_eq_orbit {v v' : ℕ → ℤ × ℤ} {a b : ℤ} {i₀ j₀ i₁ j₁ k₀ l₀ : ℕ}
    (hmin : a * fdet (v i₀) (v j₀) + b * fdet (v i₁) (v j₁) = 1)
    (hne : fdet (v k₀) (v l₀) ≠ 0) :
    (∀ i j, fdet (v i) (v j) = fdet (v' i) (v' j))
      ↔ ∃ m₁₁ m₁₂ m₂₁ m₂₂ : ℤ, m₁₁ * m₂₂ - m₁₂ * m₂₁ = 1 ∧
          ∀ k, v' k = (m₁₁ * (v k).1 + m₁₂ * (v k).2, m₂₁ * (v k).1 + m₂₂ * (v k).2) := by
  constructor
  · intro hsame
    set M₁₁ := tm₁₁ a b (v i₀) (v j₀) (v i₁) (v j₁) (v' i₀) (v' j₀) (v' i₁) (v' j₁) with hM₁₁
    set M₁₂ := tm₁₂ a b (v i₀) (v j₀) (v i₁) (v j₁) (v' i₀) (v' j₀) (v' i₁) (v' j₁) with hM₁₂
    set M₂₁ := tm₂₁ a b (v i₀) (v j₀) (v i₁) (v j₁) (v' i₀) (v' j₀) (v' i₁) (v' j₁) with hM₂₁
    set M₂₂ := tm₂₂ a b (v i₀) (v j₀) (v i₁) (v j₁) (v' i₀) (v' j₀) (v' i₁) (v' j₁) with hM₂₂
    have key : ∀ k, v' k
        = (M₁₁ * (v k).1 + M₁₂ * (v k).2, M₂₁ * (v k).1 + M₂₂ * (v k).2) := by
      intro k
      rw [← transferMap_apply hsame hmin k, transferMap_matrix]
    refine ⟨M₁₁, M₁₂, M₂₁, M₂₂, ?_, key⟩
    have hpres : fdet (v' k₀) (v' l₀) = fdet (v k₀) (v l₀) := (hsame k₀ l₀).symm
    rw [key k₀, key l₀, fdet_linear_map] at hpres
    have h0 : ((M₁₁ * M₂₂ - M₁₂ * M₂₁) - 1) * fdet (v k₀) (v l₀) = 0 := by
      linear_combination hpres
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exact absurd h hne
  · rintro ⟨m₁₁, m₁₂, m₂₁, m₂₂, hdet, hk⟩ i j
    rw [hk i, hk j, fdet_linear_map, hdet, one_mul]

end VicoEnum
