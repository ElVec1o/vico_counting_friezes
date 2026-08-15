/-
  VicoEnum/Param.lean

  The continuant parameterisation at the widths used in the paper.

  Proposition 2.1 states that a positive rational frieze of width `n` is determined
  by `a_0, …, a_{n-4}` through the frieze continuants. At `n = 5` and `n = 6` that
  reads

    n = 5:  a_2 = (a_0+1)/D,      a_3 = D,  a_4 = (a_1+1)/D,   D = a_0a_1 - 1,
    n = 6:  a_3 = a_0a_1/D,       a_4 = D,  a_5 = a_1a_2/D,    D = a_2(a_0a_1-1) - a_0.

  The closing condition is that the monodromy is `-I`. Both cases are verified here
  as matrix identities, which is Proposition 2.1 at the two widths the paper uses.
-/
import VicoEnum.Width4

namespace VicoEnum

open Matrix

/-- **Proposition 2.1 at width 5.** The parameterisation closes. -/
theorem frieze5_monodromy (a₀ a₁ : ℚ) (hD : a₀ * a₁ - 1 ≠ 0) :
    M a₀ * M a₁ * M ((a₀ + 1) / (a₀ * a₁ - 1)) * M (a₀ * a₁ - 1)
      * M ((a₁ + 1) / (a₀ * a₁ - 1)) = -1 := by
  have hneg : (-1 : Matrix (Fin 2) (Fin 2) ℚ) = !![-1, 0; 0, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hneg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.mul_fin_two] <;> field_simp <;> ring

/-- **Proposition 2.1 at width 6.** The parameterisation closes. -/
theorem frieze6_monodromy (a₀ a₁ a₂ : ℚ) (hD : a₂ * (a₀ * a₁ - 1) - a₀ ≠ 0) :
    M a₀ * M a₁ * M a₂ * M (a₀ * a₁ / (a₂ * (a₀ * a₁ - 1) - a₀))
      * M (a₂ * (a₀ * a₁ - 1) - a₀)
      * M (a₁ * a₂ / (a₂ * (a₀ * a₁ - 1) - a₀)) = -1 := by
  have hneg : (-1 : Matrix (Fin 2) (Fin 2) ℚ) = !![-1, 0; 0, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hneg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.mul_fin_two] <;> field_simp <;> ring

/-- **Proposition 3.1 (width-5 conditions), lattice half.** With `a₀ = p/N` and
`a₁ = q/N` the middle entry is `a₃ = D = e/N²` for `e = pq - N²`, and the two outer
entries are `N(p+N)/e` and `N(q+N)/e`. -/
theorem width5_entries (N p q : ℚ) (hN : N ≠ 0) (he : p * q - N ^ 2 ≠ 0) :
    (p / N) * (q / N) - 1 = (p * q - N ^ 2) / N ^ 2 ∧
    ((p / N) + 1) / ((p / N) * (q / N) - 1) = N * (p + N) / (p * q - N ^ 2) ∧
    ((q / N) + 1) / ((p / N) * (q / N) - 1) = N * (q + N) / (p * q - N ^ 2) := by
  refine ⟨by field_simp; ring, ?_, ?_⟩ <;>
    · rw [show (p / N) * (q / N) - 1 = (p * q - N ^ 2) / N ^ 2 by field_simp; ring]
      field_simp
      ring

end VicoEnum
