/-
  VicoEnum/ModHyp.lean

  Proposition `prop:modhyp`, the cardinality.

  `modhyp_round_trip` records the identity `(au-1)(av-1) = ap+1` and injectivity of
  `x ↦ ax-1` for a fixed `a`. Its docstring notes what is missing: recovering `a` itself from
  the pair, as `(de-1)/p`. That is what makes the correspondence a bijection rather than a
  family of maps indexed by `a`, and it is what turns the identity into an equality of counts.

  The map is `(a,u,v) ↦ (au-1, av-1)`. Forward it lands on the hyperbola because
  `(au-1)(av-1) = a(auv) - a(u+v) + 1 = ap+1`, and `a` divides both `d+1 = au` and
  `e+1 = av`. Backward, `a` is forced: `de = ap+1` with `p ≠ 0` determines it, and then
  `u = (d+1)/a`, `v = (e+1)/a`. The relation comes back because

      a^2 uv = (au)(av) = (d+1)(e+1) = ap + d + e + 2 = a(p + u + v),

  and `a ≠ 0` cancels. Positivity of `d` needs `p > 0`: were `au = 1` then `a = u = 1` and the
  relation would give `p = -1`.
-/
import VicoEnum.ACount

namespace VicoEnum

/-- The triples counted by `C(p)`: positive solutions of `auv = p+u+v`. -/
def Triples (p : ℤ) : Set (ℤ × ℤ × ℤ) :=
  {x | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2 ∧ x.1 * x.2.1 * x.2.2 = p + x.2.1 + x.2.2}

/-- The points of the modular hyperbola `de ≡ 1 mod p` with `(de-1)/p ∣ gcd(d+1,e+1)`. -/
def Hyper (p : ℤ) : Set (ℤ × ℤ) :=
  {y | 0 < y.1 ∧ 0 < y.2 ∧
    ∃ a : ℤ, 0 < a ∧ y.1 * y.2 = a * p + 1 ∧ a ∣ y.1 + 1 ∧ a ∣ y.2 + 1}

/-- The correspondence of Proposition `prop:modhyp`. -/
def mh : ℤ × ℤ × ℤ → ℤ × ℤ := fun x => (x.1 * x.2.1 - 1, x.1 * x.2.2 - 1)

/-- **Forward.** A solution gives a point of the hyperbola. -/
theorem mh_mapsTo {p : ℤ} (hp : 0 < p) : Set.MapsTo mh (Triples p) (Hyper p) := by
  rintro ⟨a, u, v⟩ ⟨ha, hu, hv, hrel⟩
  dsimp only at ha hu hv hrel
  -- `au ≥ 2`, else `a = u = 1` and `p = -1`
  have hau : 2 ≤ a * u := by
    have h1 : 1 ≤ a * u := by nlinarith
    rcases eq_or_lt_of_le h1 with h | h
    · exfalso
      have hA : a = 1 := Int.eq_one_of_mul_eq_one_right ha.le h.symm
      have hU : u = 1 := Int.eq_one_of_mul_eq_one_right hu.le (by rw [mul_comm]; exact h.symm)
      rw [hA, hU] at hrel; simp at hrel; omega
    · omega
  have hav : 2 ≤ a * v := by
    have h1 : 1 ≤ a * v := by nlinarith
    rcases eq_or_lt_of_le h1 with h | h
    · exfalso
      have hA : a = 1 := Int.eq_one_of_mul_eq_one_right ha.le h.symm
      have hV : v = 1 := Int.eq_one_of_mul_eq_one_right hv.le (by rw [mul_comm]; exact h.symm)
      rw [hA, hV] at hrel; simp at hrel; omega
    · omega
  refine ⟨by simpa [mh] using (by omega : (0:ℤ) < a * u - 1),
    by simpa [mh] using (by omega : (0:ℤ) < a * v - 1), a, ha, ?_, ?_, ?_⟩
  · show (a * u - 1) * (a * v - 1) = a * p + 1
    linear_combination a * hrel
  · exact ⟨u, by show a * u - 1 + 1 = a * u; ring⟩
  · exact ⟨v, by show a * v - 1 + 1 = a * v; ring⟩

/-- **Injective.** `a` is recovered as `(de-1)/p`, then `u` and `v` by cancellation. -/
theorem mh_injOn {p : ℤ} (hp : 0 < p) : Set.InjOn mh (Triples p) := by
  rintro ⟨a, u, v⟩ ⟨ha, hu, hv, hrel⟩ ⟨a', u', v'⟩ ⟨ha', hu', hv', hrel'⟩ hEq
  dsimp only at ha hu hv hrel ha' hu' hv' hrel'
  simp only [mh, Prod.mk.injEq] at hEq
  have h1 : a * u = a' * u' := by linarith [hEq.1]
  have h2 : a * v = a' * v' := by linarith [hEq.2]
  -- the products give `ap = a'p`
  have hd : (a * u - 1) * (a * v - 1) = a * p + 1 := by linear_combination a * hrel
  have hd' : (a' * u' - 1) * (a' * v' - 1) = a' * p + 1 := by linear_combination a' * hrel'
  have hap : a * p = a' * p := by rw [h1, h2] at hd; linarith [hd, hd']
  have haa : a = a' := by
    have := mul_right_cancel₀ hp.ne' hap; exact this
  subst haa
  have hue : u = u' := mul_left_cancel₀ ha.ne' h1
  have hve : v = v' := mul_left_cancel₀ ha.ne' h2
  simp [hue, hve]

/-- **Surjective.** Every point of the hyperbola comes from a solution. Note this direction
needs nothing of `p`: only the forward map needs `p > 0`, to keep `au - 1` positive. -/
theorem mh_surjOn {p : ℤ} : Set.SurjOn mh (Triples p) (Hyper p) := by
  rintro ⟨d, e⟩ ⟨hd, he, a, ha, hde, ⟨u, hu⟩, ⟨v, hv⟩⟩
  have hupos : 0 < u := by nlinarith [hu, hd, ha]
  have hvpos : 0 < v := by nlinarith [hv, he, ha]
  refine ⟨(a, u, v), ⟨ha, hupos, hvpos, ?_⟩, ?_⟩
  · -- `a^2 uv = a(p+u+v)`, then cancel `a`
    have hsq : a * (a * (u * v)) = a * (p + u + v) := by
      have hprod : (d + 1) * (e + 1) = a * p + d + e + 2 := by linear_combination hde
      calc a * (a * (u * v)) = (a * u) * (a * v) := by ring
        _ = (d + 1) * (e + 1) := by rw [← hu, ← hv]
        _ = a * p + d + e + 2 := hprod
        _ = a * p + (a * u) + (a * v) := by rw [← hu, ← hv]; ring
        _ = a * (p + u + v) := by ring
    have := mul_left_cancel₀ ha.ne' hsq
    show a * u * v = p + u + v
    linear_combination this
  · show ((a * u - 1 : ℤ), (a * v - 1 : ℤ)) = (d, e)
    rw [← hu, ← hv]; simp

/-- **Proposition `prop:modhyp`.** The correspondence is a bijection. -/
theorem mh_bijOn {p : ℤ} (hp : 0 < p) : Set.BijOn mh (Triples p) (Hyper p) :=
  ⟨mh_mapsTo hp, mh_injOn hp, mh_surjOn⟩

/-- **Proposition `prop:modhyp`, the cardinality.** `C(p)` counts the points of the modular
hyperbola carrying the divisibility condition. -/
theorem modhyp_card {p : ℤ} (hp : 0 < p) : (Triples p).ncard = (Hyper p).ncard := by
  rw [← (mh_bijOn hp).image_eq, Set.ncard_image_of_injOn (mh_injOn hp)]

/-! ## Non-vacuity

At `p = 5` the solution `(1,2,7)` of `auv = p+u+v` maps to the hyperbola point `(1,6)`, with
`1 * 6 = 1 * 5 + 1`. Both sets are inhabited, so the bijection is not between empty sets. -/

theorem triples_five : ((1 : ℤ), (2 : ℤ), (7 : ℤ)) ∈ Triples 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem hyper_five : ((1 : ℤ), (6 : ℤ)) ∈ Hyper 5 :=
  ⟨by norm_num, by norm_num, 1, by norm_num, by norm_num, ⟨2, by norm_num⟩, ⟨7, by norm_num⟩⟩

theorem mh_five : mh ((1 : ℤ), (2 : ℤ), (7 : ℤ)) = ((1 : ℤ), (6 : ℤ)) := by
  show ((1 * 2 - 1 : ℤ), (1 * 7 - 1 : ℤ)) = _
  norm_num

end VicoEnum
