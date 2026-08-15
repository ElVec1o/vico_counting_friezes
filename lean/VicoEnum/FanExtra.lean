/-
  VicoEnum/FanExtra.lean

  The remaining entry of column `0` in the rational fan.

  `fan_col_zero` gives `F_{r,0} = 1 + (n-1-r)N` for `r ≥ 4`, indexed by `k = r - 4 ≥ 0`.
  The value at `r = 3` is the two-factor product, the continuant `K_2(a_0,a_1) = a_0a_1 - 1`
  being the `(0,0)` entry of `M(a_0)M(a_1)`, and is recorded here. With `n = m + 5` it reads
  `1 + (m+1)N = 1 + (n-4)N`, which is the same formula at `r = 3`.
-/
import VicoEnum.Fan

namespace VicoEnum

/-- **Column `0` at `r = 3`.** -/
theorem fan_col_zero_three (m : ℕ) (N : ℚ) (hN : N ≠ 0) :
    (M (fanLead m N) * M (1 / N)) 0 0 = ((m : ℚ) + 1) * N + 1 := by
  simp [M, fanLead, Matrix.mul_fin_two]
  field_simp
  ring

end VicoEnum
