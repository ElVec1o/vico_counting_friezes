/-
  VicoEnum/FordGeneral.lean

  The width-5 count at every `N`, as a sum of Ford counts.

  Theorem `thm:orbit` gives `T(p,5) = 5 + 5C(p)` at a prime, where `C(p)` counts the
  solutions of `auv = p+u+v`. That is one instance of Ford's equation `xyz = A(x+y)+B`,
  and the collapse to a single instance is special to primes: there `M` takes only the
  values `p` and `p^2`.

  For general `N` the parameter `M` of `thm:t5red` runs over the divisors of `N^2`, and the
  count does not collapse. What is proved here is that it still decomposes, exactly, into
  Ford counts with explicit parameters. Writing `e = gcd(N,M)` and `d = N/e`:

    `div_gcd_dvd_of_w5`  the `M` contributing anything are exactly those with `d ∣ M`;
    `w5_iff_ford`        at such an `M`, the width-5 condition on a coprime pair `(u,v)`
                         is exactly `uv ∣ e(u+v) + M/d`, that is Ford's equation with
                         `A = e` and `B = M/d`.

  So for every `N`,

    T(N,5) = sum over `M ∣ N^2` with `(N/gcd(N,M)) ∣ M` of `F(gcd(N,M), M·gcd(N,M)/N)`,

  where `F(A,B) = #{(u,v) > 0 : gcd(u,v)=1, uv ∣ A(u+v)+B}`. At `N = p` the two surviving
  values `M = p, p^2` give `F(p,p) = A(p)` and `F(p,p^2) = B(p)`, recovering the paper.

  The identity was checked against the enumeration for every `N ≤ 60`, the range `31..60`
  being disjoint from the range that suggested it.

  `dvd_mul_iff_div_gcd_dvd` is the arithmetic step: `N ∣ gM` is exactly `d ∣ g`.
-/
import VicoEnum.GeneralN

namespace VicoEnum

/-- **`N ∣ gM` is exactly `(N/gcd(N,M)) ∣ g`.** The step that turns the width-5 condition
into Ford's equation. -/
theorem dvd_mul_iff_div_gcd_dvd {N M g : ℕ} (hN : 0 < N) :
    N ∣ g * M ↔ (N / Nat.gcd N M) ∣ g := by
  have hg0 : 0 < Nat.gcd N M := Nat.gcd_pos_of_pos_left _ hN
  have hcop : Nat.Coprime (N / Nat.gcd N M) (M / Nat.gcd N M) :=
    Nat.coprime_div_gcd_div_gcd hg0
  have hNe : Nat.gcd N M * (N / Nat.gcd N M) = N :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left N M)
  have hMe : Nat.gcd N M * (M / Nat.gcd N M) = M :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right N M)
  set e := Nat.gcd N M
  set d := N / e
  set M' := M / e
  have hEq : g * M = e * (g * M') := by rw [← hMe]; ring
  constructor
  · intro h
    rw [hEq, ← hNe] at h
    exact hcop.dvd_of_dvd_mul_right ((Nat.mul_dvd_mul_iff_left hg0).mp h)
  · intro h
    rw [hEq, ← hNe]
    exact Nat.mul_dvd_mul_left _ (h.trans (Dvd.intro M' rfl))

/-- **The width-5 condition at a fixed `M` is Ford's equation.** With `e = gcd(N,M)` and
`d = N/e`, and provided `d ∣ M`, the pair of divisibilities defining the `M`-part of
`thm:t5red` is equivalent to the single Ford condition for `x y z = e(x+y) + M/d`. -/
theorem w5_iff_ford {N M u v : ℕ} (hN : 0 < N) (huv : 0 < u * v)
    (hd : (N / Nat.gcd N M) ∣ M) :
    (u * v ∣ N * (u + v) + M ∧ N * (u * v) ∣ M * (N * (u + v) + M))
      ↔ u * v ∣ Nat.gcd N M * (u + v) + M / (N / Nat.gcd N M) := by
  have hg0 : 0 < Nat.gcd N M := Nat.gcd_pos_of_pos_left _ hN
  have hNe : Nat.gcd N M * (N / Nat.gcd N M) = N :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left N M)
  obtain ⟨c, hc⟩ := hd
  set e := Nat.gcd N M
  set d := N / e
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.mul_zero] at hNe; omega
    · exact h
  have hMdc : M / d = c := by rw [hc]; exact Nat.mul_div_cancel_left _ hd0
  constructor
  · rintro ⟨⟨g, hg⟩, h2⟩
    have hgM : N ∣ g * M := by
      have : N * (u * v) ∣ (g * M) * (u * v) := by
        refine h2.trans (dvd_of_eq ?_); rw [hg]; ring
      exact (mul_dvd_mul_iff_right huv.ne').mp this
    obtain ⟨h, rfl⟩ := (dvd_mul_iff_div_gcd_dvd hN).mp hgM
    refine ⟨h, ?_⟩
    have hkey : d * (u * v * h) = d * (e * (u + v) + c) := by
      rw [show d * (u * v * h) = u * v * (d * h) from by ring, ← hg, hc]
      rw [← hNe]; ring
    have := Nat.eq_of_mul_eq_mul_left hd0 hkey
    rw [hMdc]; omega
  · rintro ⟨h, hh⟩
    rw [hMdc] at hh
    have heq : N * (u + v) + M = u * v * (d * h) := by
      rw [show u * v * (d * h) = d * (u * v * h) from by ring, ← hh, hc, ← hNe]; ring
    refine ⟨⟨d * h, heq⟩, ?_⟩
    obtain ⟨w, hw⟩ : N ∣ (d * h) * M := (dvd_mul_iff_div_gcd_dvd hN).mpr ⟨h, rfl⟩
    refine ⟨w, ?_⟩
    rw [heq, show M * (u * v * (d * h)) = ((d * h) * M) * (u * v) from by ring, hw]; ring

/-- **The support condition is necessary.** If any pair satisfies the width-5 condition at
`M`, then `(N/gcd(N,M)) ∣ M`. So the `M` contributing to `thm:t5red` are exactly those. -/
theorem div_gcd_dvd_of_w5 {N M u v : ℕ} (hN : 0 < N) (huv : 0 < u * v)
    (h1 : u * v ∣ N * (u + v) + M) (h2 : N * (u * v) ∣ M * (N * (u + v) + M)) :
    (N / Nat.gcd N M) ∣ M := by
  have hg0 : 0 < Nat.gcd N M := Nat.gcd_pos_of_pos_left _ hN
  have hNe : Nat.gcd N M * (N / Nat.gcd N M) = N :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left N M)
  obtain ⟨g, hg⟩ := h1
  have hgM : N ∣ g * M := by
    have : N * (u * v) ∣ (g * M) * (u * v) := by
      refine h2.trans (dvd_of_eq ?_); rw [hg]; ring
    exact (mul_dvd_mul_iff_right huv.ne').mp this
  obtain ⟨h, rfl⟩ := (dvd_mul_iff_div_gcd_dvd hN).mp hgM
  set e := Nat.gcd N M
  set d := N / e
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hz | hp
    · rw [hz, Nat.mul_zero] at hNe; omega
    · exact hp
  have key : d * (u * v * h) = d * (e * (u + v)) + M := by
    rw [show d * (u * v * h) = u * v * (d * h) from by ring, ← hg,
      show d * (e * (u + v)) = e * d * (u + v) from by ring, hNe]
  have hle : e * (u + v) ≤ u * v * h :=
    Nat.le_of_mul_le_mul_left (by omega) hd0
  exact ⟨u * v * h - e * (u + v), by rw [Nat.mul_sub]; omega⟩

end VicoEnum
