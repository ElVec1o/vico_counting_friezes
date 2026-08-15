/-
  VicoEnum/Counting.lean

  D7c: the product formula `Qp` is the counting function `Q(n) = #{k : k² ∣ n³}`.
  D7 : the full arithmetic content of the Dirichlet series identity.

  The bridge is `M n = ∏_{p^α ‖ n} p^⌊3α/2⌋`. Per prime, `k² ∣ n³` says
  `2·v_p(k) ≤ 3·v_p(n)`, i.e. `v_p(k) ≤ ⌊3·v_p(n)/2⌋`, which is exactly `k ∣ M n`.
  So the counted set is the divisor set of `M n`, and `Nat.card_divisors` turns its
  cardinality into the product formula.
-/
import VicoEnum.Multiplicative

namespace VicoEnum

def Mf (n : ℕ) : ℕ := n.factorization.prod fun p α => p ^ (3 * α / 2)

theorem Mf_ne_zero {n : ℕ} (_hn : n ≠ 0) : Mf n ≠ 0 := by
  unfold Mf Finsupp.prod
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro p hp
  rw [Nat.support_factorization] at hp
  exact pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))

theorem Mf_factorization {n : ℕ} (hn : n ≠ 0) (q : ℕ) :
    (Mf n).factorization q = 3 * n.factorization q / 2 := by
  classical
  have hne : ∀ p ∈ n.factorization.support, p ^ (3 * n.factorization p / 2) ≠ 0 := by
    intro p hp
    rw [Nat.support_factorization] at hp
    exact pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
  unfold Mf Finsupp.prod
  rw [Nat.factorization_prod hne, Finset.sum_apply']
  have key : ∀ p ∈ n.factorization.support,
      (Nat.factorization (p ^ (3 * n.factorization p / 2))) q
        = if p = q then 3 * n.factorization p / 2 else 0 := by
    intro p hp
    rw [Nat.support_factorization] at hp
    rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors hp), Finsupp.single_apply]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' n.factorization.support q]
  by_cases hq : q ∈ n.factorization.support
  · rw [if_pos hq]
  · rw [if_neg hq, Finsupp.not_mem_support_iff.mp hq]
    norm_num

theorem Mf_primeFactors {n : ℕ} (hn : n ≠ 0) : (Mf n).primeFactors = n.primeFactors := by
  rw [← Nat.support_factorization, ← Nat.support_factorization]
  ext q
  simp only [Finsupp.mem_support_iff, ne_eq, Mf_factorization hn]
  omega

def sqDvdCube (n : ℕ) : Finset ℕ := (n ^ 3).divisors.filter fun k => k ^ 2 ∣ n ^ 3

theorem sq_dvd_cube_iff {k n : ℕ} (hk : k ≠ 0) (hn : n ≠ 0) :
    k ^ 2 ∣ n ^ 3 ↔ k ∣ Mf n := by
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hk) (pow_ne_zero 3 hn),
      ← Nat.factorization_le_iff_dvd hk (Mf_ne_zero hn), Finsupp.le_def, Finsupp.le_def]
  constructor
  · intro h q
    have hq := h q
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hq
    rw [Mf_factorization hn]
    omega
  · intro h q
    have hq := h q
    rw [Mf_factorization hn] at hq
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    omega

theorem sqDvdCube_eq {n : ℕ} (hn : n ≠ 0) : sqDvdCube n = (Mf n).divisors := by
  ext k
  simp only [sqDvdCube, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hkd, _⟩, hk2⟩
    have hk : k ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hk2
      exact (pow_ne_zero 3 hn) (Nat.eq_zero_of_zero_dvd hk2)
    exact ⟨(sq_dvd_cube_iff hk hn).mp hk2, Mf_ne_zero hn⟩
  · rintro ⟨hk, _⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact Mf_ne_zero hn (Nat.eq_zero_of_zero_dvd hk)
    have h2 := (sq_dvd_cube_iff hk0 hn).mpr hk
    exact ⟨⟨dvd_trans (dvd_pow_self k two_ne_zero) h2, pow_ne_zero 3 hn⟩, h2⟩

theorem Qp_eq_card {n : ℕ} (hn : n ≠ 0) : Qp n = (sqDvdCube n).card := by
  rw [sqDvdCube_eq hn, Nat.card_divisors (Mf_ne_zero hn)]
  unfold Qp Finsupp.prod
  rw [Nat.support_factorization, ← Mf_primeFactors hn]
  exact Finset.prod_congr rfl fun q _ => by rw [Mf_factorization hn]

/-! ## D7, assembled

`Q` is now known to be the counting function, to be multiplicative, to have local
values `Qlocal`, and to satisfy the prime-power convolution identity. That is
exactly the coefficient content of

    (Σ_n Q(n) n^{-s}) · ζ(3s) = ζ(s)² · ζ(2s).
-/

/-- **D7, multiplicativity of the count.** -/
theorem card_sqDvdCube_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    (sqDvdCube (m * n)).card = (sqDvdCube m).card * (sqDvdCube n).card := by
  rw [← Qp_eq_card (Nat.mul_ne_zero hm hn), ← Qp_eq_card hm, ← Qp_eq_card hn]
  exact Qp_mul_of_coprime hm hn h

/-- **D7, local values of the count.** -/
theorem card_sqDvdCube_prime_pow {p : ℕ} (hp : p.Prime) (α : ℕ) :
    (sqDvdCube (p ^ α)).card = Qlocal α := by
  rw [← Qp_eq_card (pow_ne_zero α hp.ne_zero)]
  exact Qp_prime_pow hp α

/-- **D7.** The three statements that, through the Euler product, are the identity
`Σ Q(n) n^{-s} = ζ(s)² ζ(2s) / ζ(3s)`: the count is multiplicative, its local value
at `p^α` is `⌊3α/2⌋+1`, and at every prime power the cube-side convolution agrees
with the square-side convolution of the divisor function. -/
theorem D7 :
    (∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → Nat.Coprime m n →
        (sqDvdCube (m * n)).card = (sqDvdCube m).card * (sqDvdCube n).card) ∧
    (∀ {p : ℕ} (α : ℕ), p.Prime → (sqDvdCube (p ^ α)).card = Qlocal α) ∧
    (∀ α, convL α = convR α) :=
  ⟨fun hm hn h => card_sqDvdCube_mul hm hn h,
   fun α hp => card_sqDvdCube_prime_pow hp α,
   conv_eq⟩

end VicoEnum
