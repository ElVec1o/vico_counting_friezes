/-
  VicoEnum/OrbitCount.lean

  Theorem `thm:orbit`: the arithmetic conclusion, and what still separates it from the
  frieze count.

  The theorem has two halves. The combinatorial half is `orbit_split` in `PrimeOrbit.lean`:
  in a positive width-5 quiddity over `(1/p)ℤ` that is not all-integral, exactly two of the
  five positions have `M = p` and three have `M = p^2`. The exceptional orbit is the
  Conway--Coxeter cycle `(2,2,1,3,1)`, where all five have `M = p`; `intcount_five` is what
  identifies that orbit.

  The counting half is here. Writing `R` for the number of rotation orbits, `A` for the
  number of cycles with `M = p` and `B` for the number with `M = p^2`, the split gives
  `A = 2(R-1) + 5` and `B = 3(R-1)`, and the two identities the theorem displays follow by
  arithmetic. They are stated without subtraction or division: `3A = 2B + 15` and
  `2T + 15 = 5A`, which are `3A - 2B = 15` and `T = (5A-15)/2`.

  WHAT IS NOT HERE, and it is the substantial part: that `A` is the cardinality of `ASet p`
  and that `T(p,5) = A + B`. That is the `M`-split of the frieze count, and it requires the
  rotation action on `Friezes5 p` together with the per-orbit statement above. Until it is
  proved, `acount_eq` and the identities below do not compose into `T(p,5) = 5 + 5C(p)`.
-/
import VicoEnum.ACountFull
import VicoEnum.PrimeOrbit

namespace VicoEnum

/-- **Theorem `thm:orbit`, the counting half.** From the per-orbit split, with `R` orbits of
which one is exceptional, the two displayed identities follow. -/
theorem orbit_identities {A B R T : ℕ} (hR : 1 ≤ R)
    (hA : A = 2 * (R - 1) + 5) (hB : B = 3 * (R - 1)) (hT : T = A + B) :
    3 * A = 2 * B + 15 ∧ T = 5 * R ∧ 2 * T + 15 = 5 * A := by
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hA hB
  subst hA; subst hB; subst hT
  exact ⟨by ring, by ring, by ring⟩

/-- The form the paper uses downstream: with `A = 5 + 2C`, the count is `5 + 5C`. -/
theorem orbit_to_count {A T C : ℕ} (hid : 2 * T + 15 = 5 * A) (hA : A = 5 + 2 * C) :
    T = 5 + 5 * C := by
  subst hA; omega

end VicoEnum
