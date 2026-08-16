/-
  VicoEnum/FordDiagonal.lean

  The terms of the decomposition and the reflection-symmetric friezes are the same objects.

  `support_iff_dvd_sq`: for `M | N^2` the support condition `(N/gcd(N,M)) | M` of
  `T5_sum_ford` is exactly `N | M^2`. So the sum of `T5_sum_ford` runs over

      { M : M | N^2  and  N | M^2 }.

  `W5_diag_iff`: a `W5` pair on the diagonal, `(x,x)`, is exactly one with `x > N`,
  `N | x^2` and `x - N | N^2`. These are the pairs fixed by the reflection.

  `W5_diag_shift`: putting the two together, `M -> M + N` is a bijection from the support
  onto the diagonal pairs. The decomposition therefore has exactly one Ford term for each
  reflection-symmetric frieze, and the number of terms is `Qp N`, the number of square
  divisors of `N^3` (OEIS A092520).

  Two consequences, written out in the paper. The reflection is an involution on the `W5`
  pairs whose fixed points are the diagonal ones, so `T(N,5)` and `Qp N` have the same
  parity; with `5 | T(N,5)` from `five_dvd_T5` this gives `T(N,5) = 5 Qp N mod 10`, and
  hence `10 | T(N,5)` if and only if `Qp N` is even, if and only if some exponent in the
  factorisation of `N` is `1` or `2` mod `4`. At a prime this recovers `ten_dvd_T5_prime`.
-/
import VicoEnum.FordCongruence

namespace VicoEnum

/-- **The support condition, simplified.** For `M ∣ N^2` the condition
`(N/gcd(N,M)) ∣ M` is exactly `N ∣ M^2`. -/
theorem support_iff_dvd_sq {N M d : ℕ} (hN : 0 < N) (hdd : N / Nat.gcd N M = d) :
    d ∣ M ↔ N ∣ M ^ 2 := by
  have hg0 : 0 < Nat.gcd N M := Nat.gcd_pos_of_pos_left _ hN
  have hNe : Nat.gcd N M * (N / Nat.gcd N M) = N := Nat.mul_div_cancel' (Nat.gcd_dvd_left N M)
  have hMe : Nat.gcd N M * (M / Nat.gcd N M) = M := Nat.mul_div_cancel' (Nat.gcd_dvd_right N M)
  have hcop : Nat.Coprime (N / Nat.gcd N M) (M / Nat.gcd N M) :=
    Nat.coprime_div_gcd_div_gcd hg0
  obtain ⟨e, he⟩ : ∃ e, Nat.gcd N M = e := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, M / Nat.gcd N M = m := ⟨_, rfl⟩
  rw [hdd, he] at hNe; rw [hm, he] at hMe; rw [hdd, hm] at hcop
  have he0 : 0 < e := he ▸ hg0
  constructor
  · intro h
    have hde : d ∣ e := hcop.dvd_of_dvd_mul_right (hMe ▸ h)
    obtain ⟨c, hc⟩ := hde
    exact ⟨c * m ^ 2, by rw [← hMe, ← hNe, hc]; ring⟩
  · intro h
    have h1 : e * d ∣ e * (e * m ^ 2) := by
      refine (hNe ▸ h).trans (dvd_of_eq ?_); rw [← hMe]; ring
    have h2 : d ∣ e * m ^ 2 := (mul_dvd_mul_iff_left he0.ne').mp h1
    have hde : d ∣ e := (hcop.pow_right 2).dvd_of_dvd_mul_right h2
    exact hMe ▸ hde.mul_right m

/-- **The reflection-symmetric `W5` pairs.** `(x,x)` is a `W5` pair exactly when `x > N`,
`N ∣ x^2` and `x - N ∣ N^2`. -/
theorem W5_diag_iff {N x : ℕ} (hN : 0 < N) :
    W5 N x x ↔ N < x ∧ N ∣ x ^ 2 ∧ (x - N) ∣ N ^ 2 := by
  constructor
  · rintro ⟨hx, -, hlt, hdvd, hd1, -⟩
    have hxN : N < x := by nlinarith [hlt]
    obtain ⟨k, rfl⟩ : ∃ k, x = N + k := ⟨x - N, by omega⟩
    refine ⟨hxN, by simpa [pow_two] using hdvd, ?_⟩
    have hk : N + k - N = k := by omega
    rw [hk]
    have hfac : (N + k) * (N + k) - N ^ 2 = k * (k + 2 * N) := by
      have h : (N + k) * (N + k) = N ^ 2 + k * (k + 2 * N) := by ring
      omega
    rw [hfac] at hd1
    have hkpos : 0 < k + 2 * N := by omega
    exact (mul_dvd_mul_iff_right hkpos.ne').mp
      (hd1.trans (dvd_of_eq (by ring)))
  · rintro ⟨hxN, hsq, hsub⟩
    obtain ⟨k, rfl⟩ : ∃ k, x = N + k := ⟨x - N, by omega⟩
    have hk : N + k - N = k := by omega
    rw [hk] at hsub
    have hk0 : 0 < k := by omega
    have hfac : (N + k) * (N + k) - N ^ 2 = k * (k + 2 * N) := by
      have h : (N + k) * (N + k) = N ^ 2 + k * (k + 2 * N) := by ring
      omega
    obtain ⟨c, hc⟩ := hsub
    refine ⟨by omega, by omega, by nlinarith, by simpa [pow_two] using hsq, ?_, ?_⟩ <;>
      · rw [hfac]; exact ⟨c, by rw [hc]; ring⟩

/-- **The shift bijection.** `M ↦ M + N` carries the support of the decomposition onto the
reflection-symmetric `W5` pairs: `(M+N, M+N)` is a `W5` pair exactly when `M ∣ N^2` and
`N ∣ M^2`, which by `support_iff_dvd_sq` is exactly the support condition. -/
theorem W5_diag_shift {N M : ℕ} (hN : 0 < N) (hM : 0 < M) :
    W5 N (M + N) (M + N) ↔ M ∣ N ^ 2 ∧ N ∣ M ^ 2 := by
  rw [W5_diag_iff hN]
  have hk : M + N - N = M := by omega
  rw [hk]
  constructor
  · rintro ⟨-, hsq, hsub⟩
    refine ⟨hsub, ?_⟩
    have hexp : (M + N) ^ 2 = M ^ 2 + N * (2 * M + N) := by ring
    rw [hexp] at hsq
    exact (Nat.dvd_add_right ⟨2 * M + N, rfl⟩).mp
      (by rwa [Nat.add_comm] at hsq)
  · rintro ⟨hsub, hsq⟩
    refine ⟨by omega, ?_, hsub⟩
    have hexp : (M + N) ^ 2 = M ^ 2 + N * (2 * M + N) := by ring
    rw [hexp]
    exact Nat.dvd_add hsq ⟨2 * M + N, rfl⟩

end VicoEnum
