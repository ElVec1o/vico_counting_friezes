/-
  VicoEnum/PathToFrieze.lean

  From a Farey path to a frieze, at every width.

  `FareyPentagon.fpath_det` shows that the quiddity recurrence gives a vertex sequence
  all of whose consecutive determinants are equal, say to `R`. This file goes the other
  way and shows what such a sequence produces: setting

      m i j = (1/R) * fdet (v j) (v i)

  every adjacent two-by-two minor of `m` equals one, `m i i = 0`, and `m (i+1) i = 1`.
  Those are exactly the defining relations of a frieze.

  The proof is one identity. For four vectors in the plane the Plücker relation

      [ab][cd] - [ac][bd] + [ad][bc] = 0

  holds identically, and applying it to `(v j, v i, v (j+1), v (i+1))` turns the minor of
  `m` into the product of two consecutive determinants of the path, which is `R · R`.

  Nothing here is width-dependent. The width-five Ford decomposition and the width-six
  reduced form both need a continuant window and so are tied to their width; this is not.
  It is the algebraic half of the path model, valid at every `n` at once.

  What is *not* proved here: positivity of the entries, the closure condition, and the
  minimality and clockwise conditions on the path. Those are what separate this from the
  full classification, which the paper cites rather than reproves.
-/
import VicoEnum.FareyPentagon

namespace VicoEnum

/-- **The Plücker relation in the plane.** An identity, valid for any four vectors. -/
theorem plucker (a b c d : ℤ × ℤ) :
    fdet a b * fdet c d - fdet a c * fdet b d + fdet a d * fdet b c = 0 := by
  simp only [fdet]; ring

/-- `fdet` is alternating. -/
theorem fdet_self (a : ℤ × ℤ) : fdet a a = 0 := by simp only [fdet]; ring

/-- `fdet` is antisymmetric. -/
theorem fdet_swap (a b : ℤ × ℤ) : fdet a b = -fdet b a := by simp only [fdet]; ring

/-- **The two-by-two minors of the array attached to a path.** If every consecutive pair of
a vertex sequence has determinant `R`, then every adjacent minor of `fdet (v j) (v i)`
equals `R²`. This holds for all `i` and `j` at once, so it is width-uniform. -/
theorem path_minor (v : ℕ → ℤ × ℤ) (R : ℤ) (hR : ∀ i, fdet (v i) (v (i + 1)) = R)
    (i j : ℕ) :
    fdet (v j) (v i) * fdet (v (j + 1)) (v (i + 1))
      - fdet (v j) (v (i + 1)) * fdet (v (j + 1)) (v i) = R * R := by
  have hp := plucker (v j) (v i) (v (j + 1)) (v (i + 1))
  have hswap : fdet (v i) (v (j + 1)) = -fdet (v (j + 1)) (v i) := fdet_swap _ _
  have hi := hR i
  have hj := hR j
  linear_combination hp - fdet (v j) (v (i + 1)) * hswap + fdet (v i) (v (i + 1)) * hj
    + R * hi

/-- **Every adjacent minor of the frieze attached to a path is one.** Dividing the array by
`R` turns `path_minor` into the frieze relation itself, at every width. -/
theorem path_frieze_minor (v : ℕ → ℤ × ℤ) (R : ℤ) (hR0 : R ≠ 0)
    (hR : ∀ i, fdet (v i) (v (i + 1)) = R) (i j : ℕ) :
    ((fdet (v j) (v i) : ℚ) / R) * ((fdet (v (j + 1)) (v (i + 1)) : ℚ) / R)
      - ((fdet (v j) (v (i + 1)) : ℚ) / R) * ((fdet (v (j + 1)) (v i) : ℚ) / R) = 1 := by
  have hRQ : (R : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hR0
  have h := path_minor v R hR i j
  have hQ : (fdet (v j) (v i) : ℚ) * (fdet (v (j + 1)) (v (i + 1)) : ℚ)
      - (fdet (v j) (v (i + 1)) : ℚ) * (fdet (v (j + 1)) (v i) : ℚ) = (R : ℚ) * (R : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h
  field_simp
  linarith [hQ]

/-- The diagonal of the array vanishes: `m i i = 0`, the row of zeros of a frieze. -/
theorem path_diag (v : ℕ → ℤ × ℤ) (i : ℕ) : fdet (v i) (v i) = 0 := fdet_self _

/-- The first subdiagonal is constantly `R`, which after dividing by `R` is the row of ones
of a frieze. -/
theorem path_subdiag (v : ℕ → ℤ × ℤ) (R : ℤ) (hR : ∀ i, fdet (v i) (v (i + 1)) = R)
    (i : ℕ) : fdet (v i) (v (i + 1)) = R := hR i

end VicoEnum
