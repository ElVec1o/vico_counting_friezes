/-
  VicoEnum/Monodromy.lean

  The frieze condition as an integral matrix factorisation, at every width.

  A positive rational frieze of width n over (1/N)Z has quiddity a_i = p_i/N with p_i a
  positive integer, and the defining condition is the monodromy identity
  M(a_0) ... M(a_{n-1}) = -1, where M(a) = !![a, -1; 1, 0]. Clearing denominators with

      W(N, p) = !![p, -N; N, 0] = N * M(p/N)

  turns this into an identity between integral matrices,

      W(p_0) ... W(p_{n-1}) = -N^n I,

  with no denominators anywhere. `M_eq_smul_W` is the scaling and `monodromy5_scaled` is
  the width-5 product. So T(N,n) counts the factorisations of -N^n I into n matrices of the
  form W(N, p) with p a positive integer.

  This is width-uniform, unlike the Ford decomposition, which needs the continuant window
  R = 1 and therefore holds only at width five. Counting the factorisations at width n >= 6
  is open; the reformulation is recorded because it is the only width-uniform handle the
  project has, not because it counts anything.

  Checked against the tabulated counts for (N,n) = (1,4), (1,5), (1,6), (2,4), (2,5),
  (3,4), (3,5), (4,4), by code/monodromy_count.py.
-/
import VicoEnum.FordToFrieze
namespace VicoEnum

/-- The integral matrix of a quiddity numerator. -/
def W (N p : ℕ) : Matrix (Fin 2) (Fin 2) ℚ := !![(p : ℚ), -(N : ℚ); (N : ℚ), 0]

/-- **The monodromy matrix, cleared of denominators.** For `a = p/N` the frieze matrix
`M a` is `W N p` scaled by `1/N`. -/
theorem M_eq_smul_W {N p : ℕ} (hN : 0 < N) :
    M ((p : ℚ) / (N : ℚ)) = ((N : ℚ)⁻¹) • W N p := by
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, W, Matrix.smul_apply, div_eq_inv_mul] <;> field_simp

/-- **The width-5 monodromy, cleared of denominators.** Writing `a_i = p_i/N`, the product
of the five frieze matrices scales to an integral matrix product:
`W(p_0)...W(p_4) = N^5 * (M(a_0)...M(a_4))`. In particular the frieze condition
`M(a_0)...M(a_4) = -1` is the integral identity `W(p_0)...W(p_4) = -N^5 I`. -/
theorem monodromy5_scaled {N : ℕ} (hN : 0 < N) (p₀ p₁ p₂ p₃ p₄ : ℕ) :
    W N p₀ * W N p₁ * W N p₂ * W N p₃ * W N p₄
      = ((N : ℚ) ^ 5) • (M ((p₀ : ℚ) / N) * M ((p₁ : ℚ) / N) * M ((p₂ : ℚ) / N)
          * M ((p₃ : ℚ) / N) * M ((p₄ : ℚ) / N)) := by
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [M_eq_smul_W hN, M_eq_smul_W hN, M_eq_smul_W hN, M_eq_smul_W hN, M_eq_smul_W hN]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show ((N : ℚ) ^ 5) * ((N : ℚ)⁻¹ * ((N : ℚ)⁻¹ * ((N : ℚ)⁻¹ *
    ((N : ℚ)⁻¹ * (N : ℚ)⁻¹)))) = 1 from by field_simp; ring, one_smul]

end VicoEnum
