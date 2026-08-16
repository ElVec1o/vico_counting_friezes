/-
  VicoEnum/Transfer.lean

  The transfer between two paths with the same frieze is a linear map.

  `transfer_of_same_frieze` gives, for each index, a formula expressing `v' k` in terms of
  four vertices of `v'` with coefficients read off `v`. That is a pointwise identity. What
  makes it the `SL₂(ℤ)` statement of the classification is that the same formula, read as a
  function of an arbitrary vector, is additive and homogeneous: it is a matrix.

  `transferMap` is that function, and `transferMap_add`, `transferMap_smul` are its
  linearity. Since `fdet u ·` is linear for each `u`, linearity is a ring identity.

  Two consequences complete the fibre description. The map carries `v k` to `v' k` for every
  `k` (`transferMap_apply`, which is `transfer_of_same_frieze` restated), and it preserves
  `fdet` on the pair it is built from, so its determinant is one. A path is therefore
  determined, on its `SL₂(ℤ)` orbit, by its frieze together with a minimal representative.
-/
import VicoEnum.InitialPair

namespace VicoEnum

/-- The transfer attached to a B\'ezout witness `(a,b)` at four vertices of the source path
and the four matching vertices of the target path. -/
def transferMap (a b : ℤ) (p q r s P Q Rt S : ℤ × ℤ) (x : ℤ × ℤ) : ℤ × ℤ :=
  (a * fdet p x * Q.1 - a * fdet q x * P.1 + b * fdet r x * S.1 - b * fdet s x * Rt.1,
   a * fdet p x * Q.2 - a * fdet q x * P.2 + b * fdet r x * S.2 - b * fdet s x * Rt.2)

/-- **The transfer is additive.** -/
theorem transferMap_add (a b : ℤ) (p q r s P Q Rt S x y : ℤ × ℤ) :
    transferMap a b p q r s P Q Rt S (x.1 + y.1, x.2 + y.2)
      = ((transferMap a b p q r s P Q Rt S x).1 + (transferMap a b p q r s P Q Rt S y).1,
         (transferMap a b p q r s P Q Rt S x).2 + (transferMap a b p q r s P Q Rt S y).2) := by
  simp only [transferMap, fdet]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- **The transfer is homogeneous.** -/
theorem transferMap_smul (a b c : ℤ) (p q r s P Q Rt S x : ℤ × ℤ) :
    transferMap a b p q r s P Q Rt S (c * x.1, c * x.2)
      = (c * (transferMap a b p q r s P Q Rt S x).1,
         c * (transferMap a b p q r s P Q Rt S x).2) := by
  simp only [transferMap, fdet]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- **The transfer realises the identity of `transfer_of_same_frieze`.** Two paths with the
same frieze, the source minimal, are related by this one linear map at every index. -/
theorem transferMap_apply {v v' : ℕ → ℤ × ℤ} {a b : ℤ} {i₀ j₀ i₁ j₁ : ℕ}
    (hsame : ∀ i j, fdet (v i) (v j) = fdet (v' i) (v' j))
    (hmin : a * fdet (v i₀) (v j₀) + b * fdet (v i₁) (v j₁) = 1) (k : ℕ) :
    transferMap a b (v i₀) (v j₀) (v i₁) (v j₁)
      (v' i₀) (v' j₀) (v' i₁) (v' j₁) (v k) = v' k := by
  rw [transferMap]
  exact (transfer_of_same_frieze hsame hmin k).symm

/-- **The transfer has determinant one on the pair it is built from.** Combined with
`fdet_sl2_invariant` this is the statement that the change of basis between two paths with
the same frieze lies in `SL₂(ℤ)`, so the fibres of the map from paths to friezes are exactly
the `SL₂(ℤ)` orbits. -/
theorem transferMap_det {v v' : ℕ → ℤ × ℤ} {a b : ℤ} {i₀ j₀ i₁ j₁ : ℕ}
    (hsame : ∀ i j, fdet (v i) (v j) = fdet (v' i) (v' j))
    (hmin : a * fdet (v i₀) (v j₀) + b * fdet (v i₁) (v j₁) = 1) (k l : ℕ) :
    fdet (transferMap a b (v i₀) (v j₀) (v i₁) (v j₁)
            (v' i₀) (v' j₀) (v' i₁) (v' j₁) (v k))
         (transferMap a b (v i₀) (v j₀) (v i₁) (v j₁)
            (v' i₀) (v' j₀) (v' i₁) (v' j₁) (v l))
      = fdet (v k) (v l) := by
  rw [transferMap_apply hsame hmin k, transferMap_apply hsame hmin l]
  exact (hsame k l).symm

end VicoEnum
