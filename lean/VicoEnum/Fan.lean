/-
  VicoEnum/Fan.lean

  U3: the rational fan closes.

  The rational fan of width `n = m + 5` over `(1/N)ℤ` is the quiddity cycle

      ( (m+1)N² + 2N,  1/N,  N+1,  2,…,2 (m times),  N+1,  1/N ).

  At `N = 1` it is `(n-2, 1, 2,…,2, 1)`, the fan triangulation of the `n`-gon.
  The theorem below is that its monodromy is `-I`, which is the closing condition
  for a frieze of width `n`. The proof is a telescoping product: the middle block
  of `2`s has the closed form `M(2)^m = !![m+1, -m; m, 1-m]`, and multiplying the
  six factors right to left produces `-a` in the `(0,1)` slot after five of them,
  which is exactly what the leading entry `a` cancels.
-/
import VicoEnum.Width4

namespace VicoEnum

open Matrix

/-- The leading entry of the rational fan of width `m + 5`. -/
def fanLead (m : ℕ) (N : ℚ) : ℚ := ((m : ℚ) + 1) * N ^ 2 + 2 * N

/-- The middle block of `2`s has a closed form. -/
theorem M_two_pow (m : ℕ) :
    (M 2) ^ m = !![(m : ℚ) + 1, -(m : ℚ); (m : ℚ), 1 - (m : ℚ)] := by
  induction m with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [M]
  | succ k ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [M, Matrix.mul_fin_two] <;> push_cast <;> ring

/-- **U3.** The rational fan closes: its monodromy is `-I`. This holds for every
`m ≥ 0` and every nonzero `N`, so the fan is a frieze of every width `n = m+5`. -/
theorem fan_monodromy (m : ℕ) (N : ℚ) (hN : N ≠ 0) :
    M (fanLead m N) * M (1 / N) * M (N + 1) * (M 2) ^ m * M (N + 1) * M (1 / N)
      = -1 := by
  rw [M_two_pow]
  have hneg : (-1 : Matrix (Fin 2) (Fin 2) ℚ) = !![-1, 0; 0, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hneg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, fanLead, Matrix.mul_fin_two] <;> field_simp <;> ring

/-! ## U3': the columns of the fan

Frieze entries are continuants, and the continuant `K_k(x_1,…,x_k)` is the `(0,0)`
entry of `M(x_1)⋯M(x_k)`. So the two columns that carry the whole positivity and
lattice argument are read off from the same products as the monodromy.
-/

/-- **Column 1 of the fan is constantly `1/N`.** This is the only column where a
denominator appears, and it never propagates. -/
theorem fan_col_one (k : ℕ) (N : ℚ) (hN : N ≠ 0) :
    (M (1 / N) * M (N + 1) * (M 2) ^ k) 0 0 = 1 / N := by
  rw [M_two_pow]
  simp [M, Matrix.mul_fin_two]
  field_simp

/-- **Column 0 of the fan descends arithmetically**, by `N` per row, from the
leading entry down to `1`. With `n = m+5` and `k = r-4` this is
`F(r,0) = 1 + (n-1-r)N`. -/
theorem fan_col_zero (m k : ℕ) (N : ℚ) (hN : N ≠ 0) :
    (M (fanLead m N) * M (1 / N) * M (N + 1) * (M 2) ^ k) 0 0
      = ((m : ℚ) - (k : ℚ)) * N + 1 := by
  rw [M_two_pow]
  simp [M, fanLead, Matrix.mul_fin_two]
  field_simp
  ring

/-- Every column-0 entry with `k ≤ m` is at least `1`, hence positive. -/
theorem fan_col_zero_pos {m k : ℕ} (hkm : k ≤ m) {N : ℚ} (hN : 0 < N) :
    1 ≤ (M (fanLead m N) * M (1 / N) * M (N + 1) * (M 2) ^ k) 0 0 := by
  rw [fan_col_zero m k N hN.ne']
  have : (0 : ℚ) ≤ (m : ℚ) - (k : ℚ) := by
    have : (k : ℚ) ≤ (m : ℚ) := by exact_mod_cast hkm
    linarith
  nlinarith [hN]

/-- The leading entry equals `(n-4)N² + 2N` at `n = m+5`, which is the Cuntz--Holm bound of
Theorem `thm:uniform`. That it is also the LARGEST entry is `fanLead_max` below; this lemma
alone does not say so. -/
theorem fanLead_eq (m : ℕ) (N : ℚ) :
    fanLead m N = ((m : ℚ) + 5 - 4) * N ^ 2 + 2 * N := by
  unfold fanLead; ring

/-! ## Corollary `cor:sharp`: the leading entry is the largest

The rational fan of width `m+5` has quiddity `(fanLead, 1/N, N+1, 2,…,2, N+1, 1/N)`. For
`N ≥ 1` the leading entry dominates each of the other three values, so it is the maximum of
the quiddity, and by `fanLead_eq` it equals the bound of Theorem `thm:uniform`. Since that
theorem bounds EVERY entry of the frieze by the same quantity, an entry attaining it is
necessarily a largest entry, which is what Corollary `cor:sharp` asserts. -/

theorem fanLead_ge_inv (m : ℕ) {N : ℚ} (hN : 1 ≤ N) : 1 / N ≤ fanLead m N := by
  have h1 : (0 : ℚ) < N := by linarith
  have h2 : 1 / N ≤ 1 := by rw [div_le_one h1]; exact hN
  unfold fanLead
  nlinarith [sq_nonneg N, Nat.cast_nonneg (α := ℚ) m]

theorem fanLead_ge_succ (m : ℕ) {N : ℚ} (hN : 1 ≤ N) : N + 1 ≤ fanLead m N := by
  unfold fanLead
  nlinarith [Nat.cast_nonneg (α := ℚ) m, sq_nonneg (N - 1)]

theorem fanLead_ge_two (m : ℕ) {N : ℚ} (hN : 1 ≤ N) : 2 ≤ fanLead m N := by
  unfold fanLead
  nlinarith [Nat.cast_nonneg (α := ℚ) m, sq_nonneg (N - 1)]

/-- **Corollary `cor:sharp`, the extremal entry.** The leading entry dominates every value
occurring in the fan's quiddity, so it is the largest, and it equals the Cuntz--Holm bound. -/
theorem fanLead_max (m : ℕ) {N : ℚ} (hN : 1 ≤ N) :
    (1 / N ≤ fanLead m N ∧ N + 1 ≤ fanLead m N ∧ (2 : ℚ) ≤ fanLead m N) ∧
      fanLead m N = ((m : ℚ) + 5 - 4) * N ^ 2 + 2 * N :=
  ⟨⟨fanLead_ge_inv m hN, fanLead_ge_succ m hN, fanLead_ge_two m hN⟩, fanLead_eq m N⟩

end VicoEnum
