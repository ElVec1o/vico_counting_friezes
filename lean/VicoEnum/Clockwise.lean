/-
  VicoEnum/Clockwise.lean

  Positivity, minimality, and the clockwise condition.

  `PathToFrieze` shows that a vertex sequence with constant edge determinant `R` gives an
  array `m i j = (1/R) fdet (v j) (v i)` satisfying the frieze relations at every width.
  What that file leaves open is the *ordered* half: positivity of the entries, and the
  conditions on the path that produce it.

  The bridge is one equivalence. Writing a vertex as the fraction `a/b`,

      m i j  =  (b_i b_j / R) * (a_j/b_j  -  a_i/b_i),

  so with `b_i > 0` the entry `m i j` is positive exactly when `a_j/b_j > a_i/b_i`, that is,
  exactly when the vertices are in strict clockwise order on the real line. Positivity of
  the frieze and clockwiseness of the path are the same condition, read two ways.

  `fdet_pos_iff` is that equivalence, stated without division so that it is an identity of
  integers. `clockwise_frieze_pos` is the forward half of the classification: a clockwise
  path with positive second coordinates gives a frieze all of whose entries above the
  diagonal are positive, at every width.

  Minimality is the remaining condition of the classification, and it is a gcd condition
  on the same determinants: a path is minimal when `gcd` of the `fdet (v j) (v i)` is one.
-/
import VicoEnum.PathToFrieze

namespace VicoEnum

/-- **Clockwise order is positivity of the determinant.** For vertices with positive second
coordinate, `fdet u w` is positive exactly when `w` lies strictly clockwise of `u` on the
real line. This is the identity `m i j = (b_i b_j / R)(a_j/b_j - a_i/b_i)` with the
denominators cleared. -/
theorem fdet_pos_iff {u w : ℤ × ℤ} (hu : 0 < u.2) (hw : 0 < w.2) :
    0 < fdet u w ↔ (w.1 : ℚ) / (w.2 : ℚ) < (u.1 : ℚ) / (u.2 : ℚ) := by
  have hu' : (0 : ℚ) < (u.2 : ℚ) := by exact_mod_cast hu
  have hw' : (0 : ℚ) < (w.2 : ℚ) := by exact_mod_cast hw
  rw [div_lt_div_iff₀ hw' hu']
  simp only [fdet]
  constructor
  · intro h
    have : (w.1 * u.2 : ℤ) < u.1 * w.2 := by linarith
    exact_mod_cast this
  · intro h
    have : (w.1 * u.2 : ℤ) < u.1 * w.2 := by exact_mod_cast h
    linarith

/-- A path is *clockwise* on an index range when its vertices have positive second
coordinate and are in strict clockwise order, stated without division. -/
def Clockwise (v : ℕ → ℤ × ℤ) (n : ℕ) : Prop :=
  (∀ i, 0 < i → i < n → 0 < (v i).2) ∧
    ∀ i j, j < i → i < n → 0 < fdet (v j) (v i)

/-- A path is *minimal* when the determinants it spans have greatest common divisor one.
This is the condition that makes the classification a bijection rather than merely a
surjection: without it the paths `(2u_i)/v_i` and `u_i/(2v_i)` have the same image. -/
def Minimal (v : ℕ → ℤ × ℤ) (n : ℕ) (K : ℤ) : Prop :=
  ∀ d : ℤ, (∀ i j, i < n → j < n → d ∣ fdet (v j) (v i)) → d ∣ K

/-- **The forward half of the classification.** A clockwise path gives a frieze whose
entries above the diagonal are all positive. Together with `path_minor`, `path_diag` and
`path_subdiag` this says a clockwise path with constant edge determinant `R` produces a
positive frieze, and it does so at every width at once. -/
theorem clockwise_frieze_pos {v : ℕ → ℤ × ℤ} {n : ℕ} (hc : Clockwise v n)
    {R : ℤ} (hR : 0 < R) {i j : ℕ} (hji : j < i) (hin : i < n) :
    0 < ((fdet (v j) (v i) : ℚ) / (R : ℚ)) := by
  have h := hc.2 i j hji hin
  have hR' : (0 : ℚ) < (R : ℚ) := by exact_mod_cast hR
  have : (0 : ℚ) < (fdet (v j) (v i) : ℚ) := by exact_mod_cast h
  exact div_pos this hR'

/-- The clockwise condition read on fractions: consecutive vertices of a clockwise path are
in strictly decreasing order on the real line. -/
theorem clockwise_decreasing {v : ℕ → ℤ × ℤ} {n : ℕ} (hc : Clockwise v n)
    {i : ℕ} (h0 : 0 < i) (hin : i + 1 < n) :
    ((v (i + 1)).1 : ℚ) / ((v (i + 1)).2 : ℚ) < ((v i).1 : ℚ) / ((v i).2 : ℚ) := by
  have hbi : 0 < (v i).2 := hc.1 i h0 (by omega)
  have hbi1 : 0 < (v (i + 1)).2 := hc.1 (i + 1) (by omega) hin
  exact (fdet_pos_iff hbi hbi1).mp (hc.2 (i + 1) i (by omega) hin)

/-- A clockwise path never repeats a vertex direction: distinct indices below `n` give
distinct points of the real line. This is the "strict" in strict clockwise order, and it is
what stops the path from completing a cycle prematurely. -/
theorem clockwise_injective {v : ℕ → ℤ × ℤ} {n : ℕ} (hc : Clockwise v n)
    {i j : ℕ} (hji : j < i) (hin : i < n) : fdet (v j) (v i) ≠ 0 :=
  ne_of_gt (hc.2 i j hji hin)

end VicoEnum
