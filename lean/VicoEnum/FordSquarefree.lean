/-
  VicoEnum/FordSquarefree.lean

  The count at a squarefree `N`, in closed form.

  For squarefree `N` the support condition of `T5_sum_ford` collapses: `d = N/gcd(N,M)`
  divides `gcd(N,M)`, so `d^2 | N`, so `d = 1` and `N | M`. The support is exactly
  `{N m : m | N}` and the decomposition becomes

      T(N,5) = sum over m | N of F(N, N m),

  one Ford term per divisor of `N`, with no gcd and no side condition. At `N = p` the two
  terms `m = 1, p` are `A(p)` and `B(p)`.
-/
import VicoEnum.FordParam

namespace VicoEnum

/-- For squarefree `N` the support condition forces `N ∣ M`. -/
theorem support_squarefree {N M : ℕ} (hN : 0 < N) (hsq : Squarefree N)
    (hMN : M ∣ N ^ 2) (hd : (N / Nat.gcd N M) ∣ M) : N ∣ M := by
  have hA0 : 0 < Nat.gcd N M := Nat.gcd_pos_of_pos_left _ hN
  have hNe : Nat.gcd N M * (N / Nat.gcd N M) = N := Nat.mul_div_cancel' (Nat.gcd_dvd_left N M)
  obtain ⟨d, hdd⟩ : ∃ d, N / Nat.gcd N M = d := ⟨_, rfl⟩
  rw [hdd] at hd hNe
  have hdN : d ∣ N := Dvd.intro_left _ hNe
  have hdA : d ∣ Nat.gcd N M := Nat.dvd_gcd hdN hd
  obtain ⟨c, hc⟩ := hdA
  have hh : d * c * d = N := by rw [← hc]; exact hNe
  have hsqd : d * d ∣ N := ⟨c, by rw [← hh]; ring⟩
  have hd1 : d = 1 := Nat.isUnit_iff.mp (hsq _ hsqd)
  rw [hd1, Nat.mul_one] at hNe
  have hgN : Nat.gcd N M = N := hNe
  exact hgN ▸ Nat.gcd_dvd_right N M

/-- **The count at a squarefree `N`.** One Ford term per divisor of `N`, with no gcd and
no support condition:  `T(N,5) = Σ_{m ∣ N} F(N, N m)`. -/
theorem T5_squarefree {N : ℕ} (hN : 0 < N) (hsq : Squarefree N) :
    T5 N = ∑ m ∈ N.divisors, (FordSet N (N * m)).ncard := by
  classical
  rw [T5_sum_ford hN]
  refine Finset.sum_nbij' (fun M => M / N) (fun m => N * m) ?_ ?_ ?_ ?_ ?_
  · intro M hM
    obtain ⟨hMN, hd⟩ := Finset.mem_filter.mp hM
    have hdvd : N ∣ M := support_squarefree hN hsq (Nat.mem_divisors.mp hMN).1 hd
    obtain ⟨m, rfl⟩ := hdvd
    show N * m / N ∈ N.divisors
    rw [Nat.mul_div_cancel_left m hN]
    refine Nat.mem_divisors.mpr ⟨?_, hN.ne'⟩
    have := (Nat.mem_divisors.mp hMN).1
    exact (mul_dvd_mul_iff_left hN.ne').mp (by simpa [pow_two] using this)
  · intro m hm
    obtain ⟨hmN, -⟩ := Nat.mem_divisors.mp hm
    have hg : Nat.gcd N (N * m) = N := Nat.gcd_eq_left ⟨m, rfl⟩
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, by positivity⟩, ?_⟩
    · obtain ⟨c, rfl⟩ := hmN
      exact ⟨c, by ring⟩
    · rw [hg, Nat.div_self hN]; exact one_dvd _
  · intro M hM
    obtain ⟨hMN, hd⟩ := Finset.mem_filter.mp hM
    have hdvd : N ∣ M := support_squarefree hN hsq (Nat.mem_divisors.mp hMN).1 hd
    exact Nat.mul_div_cancel' hdvd
  · intro m hm
    exact Nat.mul_div_cancel_left _ hN
  · intro M hM
    obtain ⟨hMN, hd⟩ := Finset.mem_filter.mp hM
    have hdvd : N ∣ M := support_squarefree hN hsq (Nat.mem_divisors.mp hMN).1 hd
    have hg : Nat.gcd N M = N := Nat.gcd_eq_left hdvd
    rw [hg, Nat.div_self hN, Nat.div_one, Nat.mul_div_cancel' hdvd]

end VicoEnum
