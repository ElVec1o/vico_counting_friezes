/-
  VicoEnum/PathFriezeIso.lean

  The correspondence runs both ways.

  `PathToFrieze` sends a path to a frieze; this file sends a frieze back to a path. The
  reason both directions work is a single observation: the frieze recurrence and the path
  recurrence are the same recurrence.

  `fdet` is linear in its second argument, so for a fixed base vertex `v j` the function

      i  ↦  fdet (v j) (v i)

  inherits the three-term recurrence `x (i+2) = c i * x (i+1) - x i` from the path. That
  is exactly the recurrence a column of a frieze satisfies. Since a solution of a
  three-term recurrence is determined by its first two values (`recurrence_unique`), a
  frieze column and a path determinant with matching initial data coincide.

  So the path is not extra structure imposed on the frieze: it is the frieze's own columns,
  read as vectors. Together with `path_minor` (all minors one, every width) and
  `clockwise_frieze_pos` (positivity from clockwiseness) this gives the algebraic and the
  ordered content of the correspondence in both directions.

  Still not formalised: the quotient by `SL₂(ℤ)`, and the surjectivity statement that makes
  the classification a bijection of sets rather than a pair of mutually inverse
  constructions on representatives.
-/
import VicoEnum.Clockwise

namespace VicoEnum

/-- **The path determinants satisfy the frieze recurrence.** `fdet` is linear in its second
argument, so a column of the path array obeys the same three-term recurrence as the path
itself. -/
theorem fdet_recurrence (v₀ v₁ : ℤ × ℤ) (c : ℕ → ℤ) (j i : ℕ) :
    fdet (fpath v₀ v₁ c j) (fpath v₀ v₁ c (i + 2))
      = c i * fdet (fpath v₀ v₁ c j) (fpath v₀ v₁ c (i + 1))
        - fdet (fpath v₀ v₁ c j) (fpath v₀ v₁ c i) := by
  rw [show fpath v₀ v₁ c (i + 2) =
    (c i * (fpath v₀ v₁ c (i + 1)).1 - (fpath v₀ v₁ c i).1,
     c i * (fpath v₀ v₁ c (i + 1)).2 - (fpath v₀ v₁ c i).2) from rfl]
  simp only [fdet]
  ring

/-- **A three-term recurrence is determined by its first two values.** -/
theorem recurrence_unique (c : ℕ → ℤ) (f g : ℕ → ℤ)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hf : ∀ i, f (i + 2) = c i * f (i + 1) - f i)
    (hg : ∀ i, g (i + 2) = c i * g (i + 1) - g i) : ∀ i, f i = g i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => exact h0
    | 1 => exact h1
    | (k + 2) => rw [hf k, hg k, ih (k + 1) (by omega), ih k (by omega)]

/-- **A frieze column is a path determinant.** If `m` satisfies the frieze recurrence in its
row index with the same first two values as the path array, then the two agree everywhere.
This is the backward direction of the correspondence: the vertices of the path are the
frieze's own columns. -/
theorem frieze_col_eq_fdet (v₀ v₁ : ℤ × ℤ) (c : ℕ → ℤ) (j : ℕ) (m : ℕ → ℤ)
    (h0 : m 0 = fdet (fpath v₀ v₁ c j) (fpath v₀ v₁ c 0))
    (h1 : m 1 = fdet (fpath v₀ v₁ c j) (fpath v₀ v₁ c 1))
    (hm : ∀ i, m (i + 2) = c i * m (i + 1) - m i) :
    ∀ i, m i = fdet (fpath v₀ v₁ c j) (fpath v₀ v₁ c i) :=
  recurrence_unique c m _ h0 h1 hm (fdet_recurrence v₀ v₁ c j)

/-- The path array is antisymmetric: transposing the frieze negates it. This is the glide
symmetry of a frieze, read on the path. -/
theorem fdet_array_antisymm (v : ℕ → ℤ × ℤ) (i j : ℕ) :
    fdet (v j) (v i) = -fdet (v i) (v j) := fdet_swap _ _

end VicoEnum
