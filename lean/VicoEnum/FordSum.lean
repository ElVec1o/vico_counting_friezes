/-
  VicoEnum/FordSum.lean

  `T(N,5)` as a sum of Ford counts, for every `N`.

  `FordGeneral.lean` proves the two pointwise facts: the `M` that contribute are exactly
  those with `(N/gcd(N,M)) ∣ M`, and at such an `M` the width-5 condition on a coprime pair
  is Ford's equation with `A = gcd(N,M)` and `B = M/(N/gcd(N,M))`. This file turns that into
  the count.

  `MarkovAt_ncard_ford` is the bijection at a fixed `M`, sending the quadruple `(g,u,v,M)`
  to `(g/d, u, v)`. `MarkovAt_eq_empty` disposes of the `M` off the support.
  `T5_sum_ford` sums over the divisors of `N^2`.

  At `N = p` the surviving divisors are `p` and `p^2`, and the two Ford counts are the
  paper's `A(p)` and `B(p)`, so this contains `thm:orbit`'s split as its prime case.
-/
import VicoEnum.FordGeneral
import VicoEnum.MSplit

namespace VicoEnum

/-- Ford's solution set for `h u v = A(u+v) + B` on coprime pairs. -/
def FordSet (A B : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {y | y.1 * y.2.1 * y.2.2 = A * (y.2.1 + y.2.2) + B ∧ Nat.gcd y.2.1 y.2.2 = 1 ∧
    0 < y.1 ∧ 0 < y.2.1 ∧ 0 < y.2.2}

/-- **The `M`-part of the width-5 count is a Ford count**, with `A = gcd(N,M)` and
`B = M/(N/gcd(N,M))`. -/
theorem MarkovAt_ncard_ford {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hMN : M ∣ N ^ 2)
    (hd : (N / Nat.gcd N M) ∣ M) :
    (MarkovAt N M).ncard = (FordSet (Nat.gcd N M) (M / (N / Nat.gcd N M))).ncard := by
  have hg0 : 0 < Nat.gcd N M := Nat.gcd_pos_of_pos_left _ hN
  have hNe : Nat.gcd N M * (N / Nat.gcd N M) = N := Nat.mul_div_cancel' (Nat.gcd_dvd_left N M)
  set e := Nat.gcd N M with he
  set d := N / e with hdd
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hz | hp
    · rw [hz, Nat.mul_zero] at hNe; omega
    · exact hp
  obtain ⟨c, hc⟩ := hd
  have hMdc : M / d = c := by rw [hc]; exact Nat.mul_div_cancel_left _ hd0
  have hc0 : 0 < c := by rcases Nat.eq_zero_or_pos c with rfl | h; · omega
                         · exact h
  rw [hMdc]
  have himg : MarkovAt N M =
      (fun y : ℕ × ℕ × ℕ => (d * y.1, y.2.1, y.2.2, M)) '' FordSet e c := by
    ext z
    constructor
    · rintro ⟨⟨hrel, hMN, hNdvd, hcop, hlt1, hlt2⟩, hMz⟩
      rw [hMz] at hNdvd hrel
      obtain ⟨h, hh⟩ := (dvd_mul_iff_div_gcd_dvd hN).mp hNdvd
      have hupos : 0 < z.2.1 := by
        rcases Nat.eq_zero_or_pos z.2.1 with hz0 | hp; · rw [hz0, Nat.mul_zero] at hlt1; omega
        · exact hp
      have hvpos : 0 < z.2.2.1 := by
        rcases Nat.eq_zero_or_pos z.2.2.1 with hz0 | hp; · rw [hz0, Nat.mul_zero] at hlt2; omega
        · exact hp
      have hhpos : 0 < h := by
        rcases Nat.eq_zero_or_pos h with rfl | hp; · rw [hh] at hlt1; simp at hlt1
        · exact hp
      refine ⟨(h, z.2.1, z.2.2.1), ⟨?_, hcop, hhpos, hupos, hvpos⟩, ?_⟩
      · have hkey : d * (h * z.2.1 * z.2.2.1) = d * (e * (z.2.1 + z.2.2.1) + c) := by
          rw [show d * (h * z.2.1 * z.2.2.1) = (d * h) * z.2.1 * z.2.2.1 from by ring, ← hh, hrel,
            show d * (e * (z.2.1 + z.2.2.1) + c) = e * d * (z.2.1 + z.2.2.1) + d * c from by ring,
            hNe, ← hc]
        exact Nat.eq_of_mul_eq_mul_left hd0 hkey
      · exact Prod.ext hh.symm (Prod.ext rfl (Prod.ext rfl hMz.symm))
    · rintro ⟨y, ⟨hfe, hcop, hh0, hu0, hv0⟩, rfl⟩
      have hrel : d * y.1 * y.2.1 * y.2.2 = N * (y.2.1 + y.2.2) + M := by
        rw [show d * y.1 * y.2.1 * y.2.2 = d * (y.1 * y.2.1 * y.2.2) from by ring, hfe,
          show d * (e * (y.2.1 + y.2.2) + c) = e * d * (y.2.1 + y.2.2) + d * c from by ring,
          hNe, ← hc]
      have hprod : 0 < d * y.1 := Nat.mul_pos hd0 hh0
      refine ⟨⟨hrel, ?_, ?_, hcop, ?_, ?_⟩, rfl⟩
      · exact hMN
      · exact (dvd_mul_iff_div_gcd_dvd hN).mpr ⟨y.1, rfl⟩
      · nlinarith [hrel, hu0, hv0, hM, hN]
      · nlinarith [hrel, hu0, hv0, hM, hN]
  rw [himg, Set.ncard_image_of_injOn]
  intro a _ b _ hab
  have h1 : d * a.1 = d * b.1 := congrArg (fun z => z.1) hab
  exact Prod.ext (Nat.eq_of_mul_eq_mul_left hd0 h1)
    (Prod.ext (congrArg (fun z => z.2.1) hab) (congrArg (fun z => z.2.2.1) hab))

/-- `MarkovAt N M` is empty unless the support condition holds. -/
theorem MarkovAt_eq_empty {N M : ℕ} (hN : 0 < N) (hd : ¬ (N / Nat.gcd N M) ∣ M) :
    MarkovAt N M = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hrel, -, hNdvd, -, hlt1, hlt2⟩, hMz⟩
  rw [hMz] at hNdvd hrel
  have hupos : 0 < z.2.1 := by
    rcases Nat.eq_zero_or_pos z.2.1 with hz0 | hp
    · rw [hz0, Nat.mul_zero] at hlt1; omega
    · exact hp
  have hvpos : 0 < z.2.2.1 := by
    rcases Nat.eq_zero_or_pos z.2.2.1 with hz0 | hp
    · rw [hz0, Nat.mul_zero] at hlt2; omega
    · exact hp
  have h1 : z.2.1 * z.2.2.1 ∣ N * (z.2.1 + z.2.2.1) + M := by
    rw [← hrel]; exact ⟨z.1, by ring⟩
  obtain ⟨w, hw⟩ := hNdvd
  have h2 : N * (z.2.1 * z.2.2.1) ∣ M * (N * (z.2.1 + z.2.2.1) + M) :=
    ⟨w, by
      rw [← hrel, show M * (z.1 * z.2.1 * z.2.2.1) = (z.1 * M) * (z.2.1 * z.2.2.1) from by ring,
        hw]; ring⟩
  exact hd (div_gcd_dvd_of_w5 hN (Nat.mul_pos hupos hvpos) h1 h2)

/-- **The width-5 count at every `N`, as a sum of Ford counts.** The sum runs over the
divisors `M` of `N^2` satisfying the support condition `(N/gcd(N,M)) ∣ M`; the others
contribute nothing. -/
theorem T5_sum_ford {N : ℕ} (hN : 0 < N) :
    T5 N = ∑ M ∈ (N ^ 2).divisors.filter (fun M => (N / Nat.gcd N M) ∣ M),
      (FordSet (Nat.gcd N M) (M / (N / Nat.gcd N M))).ncard := by
  classical
  have hfin : (MarkovSet N).Finite := MarkovSet_finite hN
  have hmem : ∀ z ∈ hfin.toFinset, z.2.2.2 ∈ (N ^ 2).divisors := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    obtain ⟨-, hMN, -, -, -, -⟩ := hz
    exact Nat.mem_divisors.mpr ⟨hMN, by positivity⟩
  have hfib : ∀ M : ℕ, (hfin.toFinset.filter (fun z => z.2.2.2 = M)).card
      = (MarkovAt N M).ncard := by
    intro M
    have hMfin : (MarkovAt N M).Finite := hfin.subset (fun z hz => hz.1)
    rw [Set.ncard_eq_toFinset_card _ hMfin]
    congr 1
    ext z
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, MarkovAt, Set.mem_setOf_eq]
  have hstep : T5 N = ∑ M ∈ (N ^ 2).divisors, (MarkovAt N M).ncard := by
    rw [← markov_ncard hN, Set.ncard_eq_toFinset_card _ hfin,
      Finset.card_eq_sum_card_fiberwise hmem]
    exact Finset.sum_congr rfl (fun M _ => hfib M)
  have hzero : ∀ M ∈ (N ^ 2).divisors,
      M ∉ (N ^ 2).divisors.filter (fun M => (N / Nat.gcd N M) ∣ M) →
      (MarkovAt N M).ncard = 0 := by
    intro M hM hnot
    rw [Finset.mem_filter] at hnot
    push_neg at hnot
    rw [MarkovAt_eq_empty hN (hnot hM), Set.ncard_empty]
  rw [hstep, ← Finset.sum_subset (Finset.filter_subset _ _) hzero]
  refine Finset.sum_congr rfl ?_
  intro M hM
  obtain ⟨hMd, hsupp⟩ := Finset.mem_filter.mp hM
  exact MarkovAt_ncard_ford hN (Nat.pos_of_mem_divisors hMd) (Nat.mem_divisors.mp hMd).1 hsupp

end VicoEnum