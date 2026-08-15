/-
  VicoEnum/MSplit.lean

  The `M`-split of the width-5 count at a prime: `T(p,5) = A(p) + B(p)`.

  This is the middle link of the chain to `T(p,5) = 5 + 5C(p)`. `acount_eq` supplies
  `A(p) = 5 + 2C(p)` and `orbit_identities` supplies the arithmetic; what was missing is that
  `A(p)` is a part of the frieze count at all.

  `markov_ncard` counts the friezes by quadruples `(g,u,v,M)` with `M ∣ N^2`. At `N = p`
  prime the divisors of `p^2` are `1`, `p` and `p^2`, and the value `1` cannot occur: it would
  force `p ∣ g` through `N ∣ gM`, and then `guv = p(u+v) + 1` would give `p ∣ 1`. So the count
  splits in two.

  On the `M = p` part the relation reads `guv = p(u+v+1)`, so `g` is determined by `(u,v)` and
  the part is in bijection with `ASet p`. The two positivity clauses `gu > p` and `gv > p` are
  automatic there, since `gu = p(u+v+1)/v > p` reduces to `u + 1 > 0`.
-/
import VicoEnum.MarkovCount
import VicoEnum.ACountFull
import VicoEnum.OrbitCount

namespace VicoEnum

/-- The Markov quadruples with a prescribed value of `M`. -/
def MarkovAt (p M₀ : ℕ) : Set (ℕ × ℕ × ℕ × ℕ) := {z | z ∈ MarkovSet p ∧ z.2.2.2 = M₀}

/-! ## Only `M = p` and `M = p^2` occur -/

/-- **`M = 1` is impossible.** `N ∣ gM` gives `p ∣ g`, and the relation then gives `p ∣ 1`. -/
theorem MarkovAt_one_empty {p : ℕ} (hp : p.Prime) : MarkovAt p 1 = ∅ := by
  ext z
  simp only [MarkovAt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨hrel, -, hNgM, -, -, -⟩ hM
  rw [hM, Nat.mul_one] at hNgM
  have hdvd : p ∣ z.1 * z.2.1 * z.2.2.1 :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right hNgM _) _
  rw [hrel, hM] at hdvd
  have : p ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_right dvd_rfl _)).mp hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- **The trichotomy.** Every quadruple has `M = p` or `M = p^2`. -/
theorem MarkovSet_M_cases {p : ℕ} (hp : p.Prime) {z : ℕ × ℕ × ℕ × ℕ} (hz : z ∈ MarkovSet p) :
    z.2.2.2 = p ∨ z.2.2.2 = p ^ 2 := by
  have hMN : z.2.2.2 ∣ p ^ 2 := hz.2.1
  obtain ⟨k, hk, hMk⟩ := (Nat.dvd_prime_pow hp).mp hMN
  interval_cases k
  · exfalso
    have : z ∈ MarkovAt p 1 := ⟨hz, by simpa using hMk⟩
    rw [MarkovAt_one_empty hp] at this; exact this
  · exact Or.inl (by simpa using hMk)
  · exact Or.inr hMk

/-! ## The `M = p` part is `ASet p` -/

/-- **Forward.** A quadruple with `M = p` gives a pair in `ASet p`. -/
theorem MarkovAt_p_to_ASet {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {z : ℕ × ℕ × ℕ × ℕ}
    (hz : z ∈ MarkovAt p p) : (z.2.1, z.2.2.1) ∈ ASet p := by
  obtain ⟨⟨hrel, -, -, hcop, hgu, hgv⟩, hM⟩ := hz
  rw [hM] at hrel
  -- `g u v = p (u + v + 1)`
  have hkey : z.1 * z.2.1 * z.2.2.1 = p * (z.2.1 + z.2.2.1 + 1) := by
    rw [hrel]; ring
  have hu1 : 1 ≤ z.2.1 := by
    rcases Nat.eq_zero_or_pos z.2.1 with h | h
    · exfalso; rw [h, Nat.mul_zero] at hgu; omega
    · exact h
  have hv1 : 1 ≤ z.2.2.1 := by
    rcases Nat.eq_zero_or_pos z.2.2.1 with h | h
    · exfalso; rw [h, Nat.mul_zero] at hgv; omega
    · exact h
  -- the box: `uv ∣ p(u+v+1)` forces both coordinates below `(p+2)^2`
  have hdvd : z.2.1 * z.2.2.1 ∣ p * (z.2.1 + z.2.2.1 + 1) := ⟨z.1, by rw [← hkey]; ring⟩
  obtain ⟨hb1, hb2⟩ := ASet_bound hp h5 hu1 hv1 hcop hdvd
  exact (mem_ASet).mpr ⟨⟨hu1, hb1⟩, ⟨hv1, hb2⟩, hcop, hdvd⟩

/-- The quadruple a pair in `ASet` determines: `g` is forced by the relation. -/
def mkG (p : ℕ) (x : ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (p * (x.1 + x.2 + 1) / (x.1 * x.2), x.1, x.2, p)

/-- **Backward.** A pair in `ASet p` gives a quadruple with `M = p`. The two positivity
clauses are automatic: `gu * v = p(u+v+1) > p * v` because `u + 1 > 0`. -/
theorem ASet_to_MarkovAt_p {p : ℕ} (hp : p.Prime) {x : ℕ × ℕ} (hx : x ∈ ASet p) :
    mkG p x ∈ MarkovAt p p := by
  obtain ⟨⟨hu1, -⟩, ⟨hv1, -⟩, hcop, hdvd⟩ := (mem_ASet).mp hx
  obtain ⟨g, hg⟩ := hdvd
  have huv : 0 < x.1 * x.2 := by positivity
  have hgval : p * (x.1 + x.2 + 1) / (x.1 * x.2) = g := by
    rw [hg]; exact Nat.mul_div_cancel_left g huv
  have hkey : g * x.1 * x.2 = p * (x.1 + x.2 + 1) := by rw [hg]; ring
  have hgu : p < g * x.1 := by
    have h1 : p * x.2 < g * x.1 * x.2 := by nlinarith [hkey, hu1, hp.pos]
    exact Nat.lt_of_mul_lt_mul_right h1
  have hgv : p < g * x.2 := by
    have h1 : p * x.1 < g * x.2 * x.1 := by nlinarith [hkey, hv1, hp.pos]
    exact Nat.lt_of_mul_lt_mul_right h1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (mkG p x).1 * (mkG p x).2.1 * (mkG p x).2.2.1
      = p * ((mkG p x).2.1 + (mkG p x).2.2.1) + (mkG p x).2.2.2
    simp only [mkG, hgval]; rw [hkey]; ring
  · show (mkG p x).2.2.2 ∣ p ^ 2
    simp only [mkG]; exact ⟨p, by ring⟩
  · show p ∣ (mkG p x).1 * (mkG p x).2.2.2
    simp only [mkG, hgval]; exact ⟨g, by ring⟩
  · show Nat.gcd (mkG p x).2.1 (mkG p x).2.2.1 = 1
    simpa [mkG] using hcop
  · show p < (mkG p x).1 * (mkG p x).2.1
    simpa [mkG, hgval] using hgu
  · show p < (mkG p x).1 * (mkG p x).2.2.1
    simpa [mkG, hgval] using hgv
  · rfl

/-! ## The split -/

/-- **`T(p,5) = A(p) + B(p)`.** The count splits by the value of `M`, which is `p` or `p^2`,
and the `M = p` part is `ASet p`. -/
theorem MarkovAt_p_ncard {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (MarkovAt p p).ncard = (ASet p).card := by
  have himg : MarkovAt p p = (mkG p) '' ↑(ASet p) := by
    ext z
    constructor
    · intro hz
      have hA := MarkovAt_p_to_ASet hp h5 hz
      refine ⟨(z.2.1, z.2.2.1), hA, ?_⟩
      have hrel := hz.1.1
      have hM := hz.2
      have hkey : z.1 * z.2.1 * z.2.2.1 = p * (z.2.1 + z.2.2.1 + 1) := by
        rw [hrel, hM]; ring
      have huv : 0 < z.2.1 * z.2.2.1 := by
        obtain ⟨⟨h1, -⟩, ⟨h2, -⟩, -, -⟩ := (mem_ASet).mp hA
        positivity
      have : p * (z.2.1 + z.2.2.1 + 1) / (z.2.1 * z.2.2.1) = z.1 := by
        rw [← hkey, show z.1 * z.2.1 * z.2.2.1 = z.2.1 * z.2.2.1 * z.1 from by ring]
        exact Nat.mul_div_cancel_left z.1 huv
      simp only [mkG, this]
      exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hM.symm))
    · rintro ⟨x, hx, rfl⟩
      exact ASet_to_MarkovAt_p hp (by simpa using hx)
  rw [himg, Set.ncard_image_of_injOn, Set.ncard_coe_Finset]
  intro a _ b _ hab
  have h1 : a.1 = b.1 := congrArg (fun z => z.2.1) hab
  have h2 : a.2 = b.2 := congrArg (fun z => z.2.2.1) hab
  exact Prod.ext h1 h2

/-- `MarkovSet p` is finite: it injects into the `W5` pairs, which are a `Finset`. -/
theorem MarkovSet_finite {p : ℕ} (hp : 0 < p) : (MarkovSet p).Finite := by
  refine Set.Finite.of_finite_image ?_ (mkv_injOn (N := p))
  rw [(mkv_bijOn hp).image_eq, W5Set]
  have : {x : ℕ × ℕ | W5 p x.1 x.2} = ↑((box5 p).filter (fun x => W5 p x.1 x.2)) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨mem_box5_of_W5 hp h, h⟩, fun h => h.2⟩
  rw [this]
  exact (Finset.finite_toSet _)

/-- **`T(p,5) = A(p) + B(p)`.** The frieze count splits by the value of `M`, and the `M = p`
part is `ASet p`, whose cardinality `acount_eq` computes. -/
theorem T5_split {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    T5 p = (ASet p).card + (MarkovAt p (p ^ 2)).ncard := by
  have hcover : MarkovSet p = MarkovAt p p ∪ MarkovAt p (p ^ 2) := by
    ext z
    constructor
    · intro hz
      rcases MarkovSet_M_cases hp hz with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  have hdisj : Disjoint (MarkovAt p p) (MarkovAt p (p ^ 2)) := by
    rw [Set.disjoint_left]
    rintro z ⟨-, h1⟩ ⟨-, h2⟩
    rw [h1] at h2
    nlinarith [hp.two_le, h2]
  have hfin := MarkovSet_finite hp.pos
  rw [← markov_ncard hp.pos, hcover,
    Set.ncard_union_eq hdisj (hfin.subset (by rw [hcover]; exact Set.subset_union_left))
      (hfin.subset (by rw [hcover]; exact Set.subset_union_right)),
    MarkovAt_p_ncard hp h5]

/-- **`T(p,5) = 5 + 5C(p)`**, the identification the paper is built on, with every link
supplied: `T5_split` for the `M`-split, `acount_eq` for `A(p) = 5 + 2C(p)`, and
`orbit_identities` for the arithmetic. The remaining hypothesis is the orbit count itself. -/
theorem T5_prime_count {p R : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hR : 1 ≤ R)
    (hA : (ASet p).card = 2 * (R - 1) + 5)
    (hB : (MarkovAt p (p ^ 2)).ncard = 3 * (R - 1)) :
    T5 p = 5 + 5 * (cubicTriples p).card := by
  have hsplit := T5_split hp h5
  obtain ⟨-, -, hid⟩ := orbit_identities (A := (ASet p).card)
    (B := (MarkovAt p (p ^ 2)).ncard) (R := R) (T := T5 p) hR hA hB hsplit
  exact orbit_to_count hid (acount_eq hp h5)

end VicoEnum
