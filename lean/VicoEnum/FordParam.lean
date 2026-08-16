/-
  VicoEnum/FordParam.lean

  Which instances of Ford's equation occur, exactly.

  `T5_sum_ford` writes `T(N,5)` as a sum of Ford counts `F(A,B)` with `A = gcd(N,M)` and
  `B = M gcd(N,M)/N`. This file determines the set of pairs `(A,B)` that occur, over all
  `N` and all `M` in the support:

      `fordParam_iff`:   (A,B) occurs  iff  B | gcd(A,B)^2.

  Both directions are constructive. Forwards, the support condition forces `d | A` where
  `d = N/gcd(N,M)`, and writing `A = d f` one gets `gcd(A,B) = f` and `B = f M'` with
  `M' | f`. Backwards, given `B | gcd(A,B)^2`, put `f = gcd(A,B)`, `d = A/f`, `m = B/f`,
  and take `N = d^2 f`, `M = d f m`.

  Consequence, written out in the paper. `T(N,5)` is a sum of `N^(o(1))` terms `F(A,B)`
  with `A <= N`, and every pair with `B | gcd(A,B)^2` arises at some `N <= A^2`. So the
  conjecture `T(N,5) = N^(o(1))` for all `N` is EQUIVALENT to Ford's conjecture restricted
  to that family, rather than merely implied by it. The frieze count is a faithful
  reformulation of a subfamily of Ford's problem, not just an instance of it.
-/
import VicoEnum.FordMin

namespace VicoEnum

/-- The pairs `(A,B)` occurring as parameters of a term of `T5_sum_ford`, for some `N`. -/
def FordParam (A B : ℕ) : Prop :=
  ∃ N M : ℕ, 0 < N ∧ M ∣ N ^ 2 ∧ (N / Nat.gcd N M) ∣ M ∧
    Nat.gcd N M = A ∧ M / (N / Nat.gcd N M) = B

/-- **Exactly which instances of Ford's equation occur.** -/
theorem fordParam_iff {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    FordParam A B ↔ B ∣ Nat.gcd A B ^ 2 := by
  constructor
  · rintro ⟨N, M, hN, hMN, hdM, hgcd, hB'⟩
    have hA0 : 0 < A := hgcd ▸ Nat.gcd_pos_of_pos_left M hN
    have hAN : A ∣ N := hgcd ▸ Nat.gcd_dvd_left N M
    have hAM : A ∣ M := hgcd ▸ Nat.gcd_dvd_right N M
    have hcop0 : Nat.Coprime (N / A) (M / A) := by
      have h := Nat.coprime_div_gcd_div_gcd (m := N) (n := M) (Nat.gcd_pos_of_pos_left M hN)
      rwa [hgcd] at h
    rw [hgcd] at hdM hB'
    have hNe : A * (N / A) = N := Nat.mul_div_cancel' hAN
    have hMe : A * (M / A) = M := Nat.mul_div_cancel' hAM
    obtain ⟨d, hd⟩ : ∃ d, N / A = d := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m, M / A = m := ⟨_, rfl⟩
    rw [hd] at hdM hB' hcop0 hNe
    rw [hm] at hcop0 hMe
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with hz | h
      · rw [hz, Nat.mul_zero] at hNe; omega
      · exact h
    have hdN : d ∣ N := ⟨A, by rw [← hNe]; ring⟩
    have hdA : d ∣ A := by
      have h := Nat.dvd_gcd hdN hdM
      rwa [hgcd] at h
    obtain ⟨f, hf⟩ := hdA
    have hf0 : 0 < f := by
      rcases Nat.eq_zero_or_pos f with hz | h
      · rw [hz, Nat.mul_zero] at hf; omega
      · exact h
    have hBval : B = f * m := by
      rw [← hB', ← hMe, hf, show d * f * m = d * (f * m) from by ring,
        Nat.mul_div_cancel_left _ hd0]
    have hgAB : Nat.gcd A B = f := by
      rw [hf, hBval, show d * f = f * d from by ring, Nat.gcd_mul_left, hcop0.gcd_eq_one,
        Nat.mul_one]
    have hMf : m ∣ f := by
      have hMeq : M = (d * f) * m := by rw [← hMe, hf]
      have hNeq : N = (d * f) * d := by rw [← hNe, hf]
      have hcube : (d * f) * m ∣ (d * f) * (d ^ 3 * f) := by
        refine (hMeq ▸ hMN).trans (dvd_of_eq ?_); rw [hNeq]; ring
      have h1 : m ∣ d ^ 3 * f :=
        (mul_dvd_mul_iff_left (by positivity : (0:ℕ) < d * f).ne').mp hcube
      exact (hcop0.symm.pow_right 3).dvd_of_dvd_mul_left h1
    rw [hgAB, hBval, pow_two]
    exact mul_dvd_mul_left f hMf
  · intro hdvd
    set f := Nat.gcd A B with hf
    have hf0 : 0 < f := Nat.gcd_pos_of_pos_left _ hA
    obtain ⟨d, hd⟩ : f ∣ A := Nat.gcd_dvd_left _ _
    obtain ⟨m, hm⟩ : f ∣ B := Nat.gcd_dvd_right _ _
    have hcop : Nat.Coprime d m := by
      have h := Nat.coprime_div_gcd_div_gcd (m := A) (n := B) hf0
      rwa [show A / f = d from by rw [hd]; exact Nat.mul_div_cancel_left _ hf0,
        show B / f = m from by rw [hm]; exact Nat.mul_div_cancel_left _ hf0] at h
    have hd0 : 0 < d := by rcases Nat.eq_zero_or_pos d with rfl | h; · simp at hd; omega
                           · exact h
    have hm0 : 0 < m := by rcases Nat.eq_zero_or_pos m with rfl | h; · simp at hm; omega
                           · exact h
    have hmf : m ∣ f := by
      have : f * m ∣ f * f := by rw [← hm]; simpa [pow_two] using hdvd
      exact (mul_dvd_mul_iff_left hf0.ne').mp this
    refine ⟨d ^ 2 * f, d * f * m, by positivity, ?_, ?_, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hmf
      exact ⟨d ^ 3 * c, by rw [hc]; ring⟩
    · have hg : Nat.gcd (d ^ 2 * f) (d * f * m) = d * f := by
        rw [show d ^ 2 * f = (d * f) * d from by ring, show d * f * m = (d * f) * m from by ring,
          Nat.gcd_mul_left, hcop, Nat.mul_one]
      rw [hg, show d ^ 2 * f = d * f * d from by ring, Nat.mul_div_cancel_left _ (by positivity)]
      exact ⟨f * m, by ring⟩
    · have hg : Nat.gcd (d ^ 2 * f) (d * f * m) = d * f := by
        rw [show d ^ 2 * f = (d * f) * d from by ring, show d * f * m = (d * f) * m from by ring,
          Nat.gcd_mul_left, hcop, Nat.mul_one]
      rw [hg, hd]; ring
    · have hg : Nat.gcd (d ^ 2 * f) (d * f * m) = d * f := by
        rw [show d ^ 2 * f = (d * f) * d from by ring, show d * f * m = (d * f) * m from by ring,
          Nat.gcd_mul_left, hcop, Nat.mul_one]
      rw [hg, show d ^ 2 * f = d * f * d from by ring, Nat.mul_div_cancel_left _ (by positivity),
        show d * f * m = d * (f * m) from by ring, Nat.mul_div_cancel_left _ hd0, hm]

end VicoEnum
