/-
  VicoEnum/Width5AnyRing.lean

  Width five over an arbitrary coefficient ring.

  The width-five frieze recurrence `a_{i+2}(a_i a_{i+1} - 1) = a_i + 1` closes after
  five steps over any field, with the explicit quiddity

      (a₀, a₁, (a₀+1)/D, D, (a₁+1)/D),        D = a₀a₁ - 1.

  Nothing here uses an order. Positivity enters the real theory only to select
  solutions and to make the count finite; it is not part of the reduction. Over
  `(1/N)O` for a domain `O` the lattice conditions on this quiddity are exactly

      N ∣ pq,   (pq - N²) ∣ N²(p+N),   (pq - N²) ∣ N²(q+N),

  which is the system `W5`, now read over `O` rather than over `ℤ`.

  Two nondegeneracy conditions that positivity hides over `ℝ` must be imposed
  separately over a general ring: `p ≠ -N` and `q ≠ -N`. Without them the
  divisibilities are vacuous (`N²(p+N) = 0` is divisible by everything) and the
  solution set is infinite, while the corresponding array has a zero entry and is
  not a frieze.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace VicoEnum

variable {K : Type*} [Field K]

/-- The explicit width-five quiddity attached to a pair `(a₀, a₁)`. -/
noncomputable def quid5 (a₀ a₁ : K) : Fin 5 → K
  | 0 => a₀
  | 1 => a₁
  | 2 => (a₀ + 1) / (a₀ * a₁ - 1)
  | 3 => a₀ * a₁ - 1
  | 4 => (a₁ + 1) / (a₀ * a₁ - 1)

/-- **The width-five recurrence closes after five steps, over any field.**

Each of the five relations `a_{i+2}(a_i a_{i+1} - 1) = a_i + 1` holds for the explicit
quiddity, with indices read cyclically. This is the whole of width five: it needs no
order, no positivity and no arithmetic in `ℤ`. -/
theorem quid5_cycle (a₀ a₁ : K) (hD : a₀ * a₁ - 1 ≠ 0) :
    (quid5 a₀ a₁ 2) * (quid5 a₀ a₁ 0 * quid5 a₀ a₁ 1 - 1) = quid5 a₀ a₁ 0 + 1 ∧
    (quid5 a₀ a₁ 3) * (quid5 a₀ a₁ 1 * quid5 a₀ a₁ 2 - 1) = quid5 a₀ a₁ 1 + 1 ∧
    (quid5 a₀ a₁ 4) * (quid5 a₀ a₁ 2 * quid5 a₀ a₁ 3 - 1) = quid5 a₀ a₁ 2 + 1 ∧
    (quid5 a₀ a₁ 0) * (quid5 a₀ a₁ 3 * quid5 a₀ a₁ 4 - 1) = quid5 a₀ a₁ 3 + 1 ∧
    (quid5 a₀ a₁ 1) * (quid5 a₀ a₁ 4 * quid5 a₀ a₁ 0 - 1) = quid5 a₀ a₁ 4 + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [quid5] <;> field_simp <;> ring

/-- The entry `a₃` of the explicit quiddity vanishes exactly when `a₀a₁ = 1`, which is the
degeneracy already excluded by `hD`. -/
theorem quid5_three_ne_zero (a₀ a₁ : K) (hD : a₀ * a₁ - 1 ≠ 0) : quid5 a₀ a₁ 3 ≠ 0 := hD

/-- **The hidden nondegeneracy.** The entries `a₂` and `a₄` vanish exactly when `a₀ = -1`
or `a₁ = -1`. Over an ordered field with all entries positive these cases cannot occur, so
the real theory never states them; over a general field they are genuine extra conditions,
and the divisibility system that describes friezes is vacuous without them. -/
theorem quid5_two_eq_zero_iff (a₀ a₁ : K) (hD : a₀ * a₁ - 1 ≠ 0) :
    quid5 a₀ a₁ 2 = 0 ↔ a₀ = -1 := by
  simp only [quid5, div_eq_zero_iff, hD, or_false]
  constructor <;> intro h <;> linear_combination h

/-- The companion statement for `a₄`. -/
theorem quid5_four_eq_zero_iff (a₀ a₁ : K) (hD : a₀ * a₁ - 1 ≠ 0) :
    quid5 a₀ a₁ 4 = 0 ↔ a₁ = -1 := by
  simp only [quid5, div_eq_zero_iff, hD, or_false]
  constructor <;> intro h <;> linear_combination h

end VicoEnum
