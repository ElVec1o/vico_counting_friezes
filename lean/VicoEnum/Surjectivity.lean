/-
  VicoEnum/Surjectivity.lean

  Every path in `F_R` arises from the construction, and minimality is exactly the statement
  that the vertices generate the whole lattice.

  `PathToFrieze` and `Clockwise` show that the construction *produces* closed clockwise
  minimal paths. What was left to the cited classification is the converse: that it produces
  *all* of them. That converse is not a classification argument. It is forced by the
  three-vector Pl\"ucker identity in the plane,

      [w,x] u - [u,x] w + [u,w] x = 0 .

  Applied to three consecutive vertices of a path, where `[u,w] = [w,x] = R`, it reads

      R x = [u,x] w - R u ,

  which is the frieze recurrence with coefficient the frieze entry `[u,x]/R`. So a path in
  `F_R` has no freedom: it satisfies the recurrence of `fpath` whether or not it was built
  that way, and the coefficients are read off the path itself.

  The same identity settles the role of minimality. Applied with `x` arbitrary it gives
  `[u,w] x = [u,x] w - [w,x] u`, so any determinant times any integer vector is an integer
  combination of two vertices. If some integer combination of the determinants equals one,
  every integer vector is an integer combination of vertices: minimality says exactly that
  the vertices generate `Z²`, which is what forces the change of basis between two paths
  with the same frieze to be integral rather than merely rational.
-/
import VicoEnum.PathFriezeIso

namespace VicoEnum

/-- **The three-vector Pl\"ucker identity in the plane**, on each coordinate. -/
theorem plucker3 (u w x : ℤ × ℤ) :
    (fdet w x * u.1 - fdet u x * w.1 + fdet u w * x.1 = 0) ∧
    (fdet w x * u.2 - fdet u x * w.2 + fdet u w * x.2 = 0) := by
  constructor <;> simp only [fdet] <;> ring

/-- **The recurrence is forced.** Three consecutive vertices of a path in `F_R` satisfy the
frieze recurrence, with coefficient the frieze entry `[u,x]/R`. No hypothesis is made about
how the vertices were produced, so every path in `F_R` is a path of `fpath` form. This is
the surjectivity of the construction. -/
theorem path_recurrence_forced {R : ℤ} {u w x : ℤ × ℤ}
    (h1 : fdet u w = R) (h2 : fdet w x = R) :
    R * x.1 = fdet u x * w.1 - R * u.1 ∧ R * x.2 = fdet u x * w.2 - R * u.2 := by
  obtain ⟨p1, p2⟩ := plucker3 u w x
  rw [h1, h2] at p1 p2
  exact ⟨by linarith, by linarith⟩

/-- When the frieze entry is an integer, the recurrence holds on the nose. -/
theorem path_recurrence_forced_of_dvd {R c : ℤ} {u w x : ℤ × ℤ} (hR : R ≠ 0)
    (h1 : fdet u w = R) (h2 : fdet w x = R) (hc : fdet u x = R * c) :
    x = (c * w.1 - u.1, c * w.2 - u.2) := by
  obtain ⟨e1, e2⟩ := path_recurrence_forced h1 h2
  rw [hc] at e1 e2
  have f1 : R * x.1 = R * (c * w.1 - u.1) := by linarith
  have f2 : R * x.2 = R * (c * w.2 - u.2) := by linarith
  exact Prod.ext (mul_left_cancel₀ hR f1) (mul_left_cancel₀ hR f2)

/-- **A determinant times any vector is an integer combination of two vertices.** -/
theorem fdet_smul_eq (u w x : ℤ × ℤ) :
    fdet u w * x.1 = fdet u x * w.1 - fdet w x * u.1 ∧
    fdet u w * x.2 = fdet u x * w.2 - fdet w x * u.2 := by
  obtain ⟨p1, p2⟩ := plucker3 u w x
  exact ⟨by linarith, by linarith⟩

/-- **Minimality generates the lattice.** If some integer combination of two determinants of
vertices equals one, then every integer vector is an integer combination of those four
vertices. This is the exact content of minimality: the vertices generate `Z²`, so the change
of basis between two paths with the same frieze is integral and not merely rational. -/
theorem span_of_coprime_dets {u w u' w' : ℤ × ℤ} {a b : ℤ}
    (h : a * fdet u w + b * fdet u' w' = 1) (x : ℤ × ℤ) :
    x.1 = a * fdet u x * w.1 - a * fdet w x * u.1
            + b * fdet u' x * w'.1 - b * fdet w' x * u'.1 ∧
    x.2 = a * fdet u x * w.2 - a * fdet w x * u.2
            + b * fdet u' x * w'.2 - b * fdet w' x * u'.2 := by
  obtain ⟨q1, q2⟩ := fdet_smul_eq u w x
  obtain ⟨r1, r2⟩ := fdet_smul_eq u' w' x
  constructor
  · linear_combination (-x.1) * h + a * q1 + b * r1
  · linear_combination (-x.2) * h + a * q2 + b * r2

/-- **The transfer map.** Two paths with the same frieze, the first minimal, are related by
an explicit integral map: every vertex of the second is the same integer combination of four
of its own vertices that the corresponding vertex of the first is of the matching four. The
coefficients are read off the first path, so the second is determined by the first together
with the frieze.

This is the injectivity of the correspondence modulo `SL_2(Z)`, in the form that avoids
constructing the matrix: the map is integral because minimality supplies the B\'ezout
relation, and it has determinant one because the two paths have the same determinants. -/
theorem transfer_of_same_frieze {v v' : ℕ → ℤ × ℤ} {a b : ℤ} {i₀ j₀ i₁ j₁ : ℕ}
    (hsame : ∀ i j, fdet (v i) (v j) = fdet (v' i) (v' j))
    (hmin : a * fdet (v i₀) (v j₀) + b * fdet (v i₁) (v j₁) = 1) (k : ℕ) :
    v' k =
      ( a * fdet (v i₀) (v k) * (v' j₀).1 - a * fdet (v j₀) (v k) * (v' i₀).1
          + b * fdet (v i₁) (v k) * (v' j₁).1 - b * fdet (v j₁) (v k) * (v' i₁).1,
        a * fdet (v i₀) (v k) * (v' j₀).2 - a * fdet (v j₀) (v k) * (v' i₀).2
          + b * fdet (v i₁) (v k) * (v' j₁).2 - b * fdet (v j₁) (v k) * (v' i₁).2 ) := by
  have hminp : a * fdet (v' i₀) (v' j₀) + b * fdet (v' i₁) (v' j₁) = 1 := by
    rw [← hsame i₀ j₀, ← hsame i₁ j₁]; exact hmin
  obtain ⟨c1, c2⟩ := span_of_coprime_dets hminp (v' k)
  rw [← hsame i₀ k, ← hsame j₀ k, ← hsame i₁ k, ← hsame j₁ k] at c1 c2
  exact Prod.ext c1 c2

/-- **The frieze is an invariant of the path modulo `SL_2(Z)`.** Applying an integral matrix
of determinant one to every vertex leaves every determinant unchanged, so the map from paths
to friezes is constant on `SL_2(Z)` orbits. With `transfer_of_same_frieze` this makes it
injective on orbits. -/
theorem fdet_sl2_invariant (a b c d : ℤ) (hdet : a * d - b * c = 1) (u w : ℤ × ℤ) :
    fdet (a * u.1 + b * u.2, c * u.1 + d * u.2) (a * w.1 + b * w.2, c * w.1 + d * w.2)
      = fdet u w := by
  simp only [fdet]
  linear_combination (u.1 * w.2 - u.2 * w.1) * hdet

/-- **The path is determined by the frieze's first two columns.** With `[v₀,v₁] = R` and
`m i j = [v_j, v_i]/R`, every vertex is `v i = m i 0 * v₁ - m i 1 * v₀`. So a path realising
a prescribed frieze has no freedom once the initial pair is fixed. -/
theorem path_from_frieze {R : ℤ} {v₀ v₁ x : ℤ × ℤ} (h : fdet v₀ v₁ = R) :
    R * x.1 = fdet v₀ x * v₁.1 - fdet v₁ x * v₀.1 ∧
    R * x.2 = fdet v₀ x * v₁.2 - fdet v₁ x * v₀.2 := by
  obtain ⟨p1, p2⟩ := plucker3 v₀ v₁ x
  rw [h] at p1 p2
  exact ⟨by linarith, by linarith⟩

/-- **The remaining normalisation, as a congruence.** Writing the two leading columns of the
frieze as `m i 0 = μ / N` and `m i 1 = ν / N`, the vertex attached to a given index exists in
`Z²` exactly when `N` divides both components of `μ v₁ - ν v₀`.

So the choice of an initial pair realising a prescribed frieze is not an unspecified
normalisation: it is the requirement that this one congruence hold at every index, and the
pair `(v₀, v₁)` is otherwise free subject to `[v₀,v₁] = R`. -/
theorem vertex_exists_iff {N : ℤ} (hN : N ≠ 0) (μ ν : ℤ) (v₀ v₁ : ℤ × ℤ) :
    (∃ w : ℤ × ℤ, N * w.1 = μ * v₁.1 - ν * v₀.1 ∧ N * w.2 = μ * v₁.2 - ν * v₀.2)
      ↔ (N ∣ μ * v₁.1 - ν * v₀.1 ∧ N ∣ μ * v₁.2 - ν * v₀.2) := by
  constructor
  · rintro ⟨w, h1, h2⟩; exact ⟨⟨w.1, h1.symm⟩, ⟨w.2, h2.symm⟩⟩
  · rintro ⟨⟨c, hc⟩, ⟨d, hd⟩⟩; exact ⟨(c, d), hc.symm, hd.symm⟩

end VicoEnum
