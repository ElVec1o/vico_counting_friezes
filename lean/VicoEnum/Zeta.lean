/-
  VicoEnum/Zeta.lean

  D7d: the Dirichlet series identity, in its analysis-free form.

      Σ Q(n) n^{-s} = ζ(s)² ζ(2s) / ζ(3s)

  Clearing the denominator and passing to coefficients, this is exactly the
  Dirichlet convolution identity

      Q ∗ c = d ∗ s

  where `c` is the indicator of perfect cubes (the coefficients of `ζ(3s)`),
  `s` the indicator of perfect squares (`ζ(2s)`), and `d = σ₀` the divisor
  function (`ζ(s)²`). Every function involved is multiplicative, so by
  `eq_iff_eq_on_prime_powers` the identity reduces to agreement at prime powers,
  which is `conv_eq`.
-/
import VicoEnum.Counting

namespace VicoEnum

open ArithmeticFunction Finset

/-! ## The three arithmetic functions -/

/-- `Q` as an arithmetic function. -/
def Qa : ArithmeticFunction ℕ := ⟨fun n => if n = 0 then 0 else Qp n, by simp⟩

/-- Indicator of perfect `k`-th powers, as an arithmetic function. -/
def powInd (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => if n = 0 then 0 else
    if ∀ p ∈ n.primeFactors, k ∣ n.factorization p then 1 else 0, by simp⟩

@[simp] theorem Qa_apply {n : ℕ} (hn : n ≠ 0) : Qa n = Qp n := by simp [Qa, hn]

@[simp] theorem powInd_apply {k n : ℕ} (hn : n ≠ 0) :
    powInd k n = if ∀ p ∈ n.primeFactors, k ∣ n.factorization p then 1 else 0 := by
  simp [powInd, hn]

/-- Outside its prime factors, a number's factorization vanishes. -/
theorem fact_eq_zero_of_not_mem {n p : ℕ} (h : p ∉ n.primeFactors) :
    n.factorization p = 0 := by
  rw [← Nat.support_factorization] at h
  exact Finsupp.not_mem_support_iff.mp h

/-! ## Multiplicativity -/

theorem isMultiplicative_Qa : Qa.IsMultiplicative := by
  constructor
  · simp [Qa]
  · intro m n h
    rcases eq_or_ne m 0 with rfl | hm
    · have : n = 1 := Nat.coprime_zero_left n |>.mp h
      subst this; simp [Qa]
    rcases eq_or_ne n 0 with rfl | hn
    · have : m = 1 := Nat.coprime_zero_right m |>.mp h
      subst this; simp [Qa]
    rw [Qa_apply (Nat.mul_ne_zero hm hn), Qa_apply hm, Qa_apply hn]
    exact Qp_mul_of_coprime hm hn h

theorem isMultiplicative_powInd (k : ℕ) : (powInd k).IsMultiplicative := by
  constructor
  · simp [powInd]
  · intro m n h
    rcases eq_or_ne m 0 with rfl | hm
    · have : n = 1 := Nat.coprime_zero_left n |>.mp h
      subst this; simp [powInd]
    rcases eq_or_ne n 0 with rfl | hn
    · have : m = 1 := Nat.coprime_zero_right m |>.mp h
      subst this; simp [powInd]
    have hdisj := Nat.Coprime.disjoint_primeFactors h
    have hpf := Nat.primeFactors_mul hm hn
    have hfm : ∀ p ∈ m.primeFactors, (m * n).factorization p = m.factorization p := by
      intro p hp
      have : p ∉ n.primeFactors := Finset.disjoint_left.mp hdisj hp
      rw [Nat.factorization_mul hm hn]
      simp [fact_eq_zero_of_not_mem this]
    have hfn : ∀ p ∈ n.primeFactors, (m * n).factorization p = n.factorization p := by
      intro p hp
      have : p ∉ m.primeFactors := Finset.disjoint_right.mp hdisj hp
      rw [Nat.factorization_mul hm hn]
      simp [fact_eq_zero_of_not_mem this]
    rw [powInd_apply (Nat.mul_ne_zero hm hn), powInd_apply hm, powInd_apply hn]
    have hiff : (∀ p ∈ (m * n).primeFactors, k ∣ (m * n).factorization p)
        ↔ (∀ p ∈ m.primeFactors, k ∣ m.factorization p)
          ∧ (∀ p ∈ n.primeFactors, k ∣ n.factorization p) := by
      constructor
      · intro hall
        refine ⟨fun p hp => ?_, fun p hp => ?_⟩
        · have := hall p (by rw [hpf]; exact Finset.mem_union_left _ hp)
          rwa [hfm p hp] at this
        · have := hall p (by rw [hpf]; exact Finset.mem_union_right _ hp)
          rwa [hfn p hp] at this
      · rintro ⟨h1, h2⟩ p hp
        rw [hpf] at hp
        rcases Finset.mem_union.mp hp with hp' | hp'
        · rw [hfm p hp']; exact h1 p hp'
        · rw [hfn p hp']; exact h2 p hp'
    by_cases hall : ∀ p ∈ (m * n).primeFactors, k ∣ (m * n).factorization p
    · obtain ⟨h1, h2⟩ := hiff.mp hall
      rw [if_pos hall, if_pos h1, if_pos h2, Nat.one_mul]
    · rw [if_neg hall]
      by_cases h1 : ∀ p ∈ m.primeFactors, k ∣ m.factorization p
      · by_cases h2 : ∀ p ∈ n.primeFactors, k ∣ n.factorization p
        · exact absurd (hiff.mpr ⟨h1, h2⟩) hall
        · rw [if_neg h2, Nat.mul_zero]
      · rw [if_neg h1, Nat.zero_mul]

/-! ## Values at prime powers -/

theorem Qa_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) : Qa (p ^ i) = Qlocal i := by
  rw [Qa_apply (pow_ne_zero i hp.ne_zero)]
  exact Qp_prime_pow hp i

theorem powInd_prime_pow {k p : ℕ} (hp : p.Prime) (i : ℕ) :
    powInd k (p ^ i) = if k ∣ i then 1 else 0 := by
  rw [powInd_apply (pow_ne_zero i hp.ne_zero)]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · have hmem : p ∈ (p ^ i).primeFactors := by
        rw [Nat.primeFactors_prime_pow hi.ne' hp]; simp
      have := h p hmem
      rwa [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at this
  · intro h q _
    rw [Nat.Prime.factorization_pow hp, Finsupp.single_apply]
    split <;> simpa using h

theorem sigma_zero_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) : σ 0 (p ^ i) = i + 1 :=
  sigma_zero_apply_prime_pow hp

/-! ## Convolutions at prime powers -/

/-- Any convolution, evaluated at a prime power, is a sum over `range (i+1)`. -/
theorem mul_prime_pow (f g : ArithmeticFunction ℕ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (f * g) (p ^ i) = ∑ j ∈ range (i + 1), f (p ^ j) * g (p ^ (i - j)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (f := fun a b => f a * g b), Nat.divisors_prime_pow hp]
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by simpa using Nat.lt_succ_iff.mp (mem_range.mp hj)) hp.pos]

/-! ## The convolutions equal the local sums -/

/-- The cube-side local sum. -/
def SL (i : ℕ) : ℕ := ∑ j ∈ range (i + 1), Qlocal j * (if 3 ∣ (i - j) then 1 else 0)

/-- The square-side local sum. -/
def SR (i : ℕ) : ℕ := ∑ j ∈ range (i + 1), (j + 1) * (if 2 ∣ (i - j) then 1 else 0)

theorem SL_eq_convL : ∀ i, SL i = convL i
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | (i + 3) => by
    have ih := SL_eq_convL i
    rw [convL, ← ih]
    unfold SL
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have e1 : ∀ j ∈ range (i + 1),
        Qlocal j * (if 3 ∣ (i + 3 - j) then 1 else 0)
          = Qlocal j * (if 3 ∣ (i - j) then 1 else 0) := by
      intro j hj
      have hji : j ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hrw : i + 3 - j = (i - j) + 3 := by omega
      rw [hrw]
      congr 2
      simp [Nat.dvd_add_self_right]
    rw [Finset.sum_congr rfl e1]
    have t1 : (if 3 ∣ (i + 3 - (i + 1)) then 1 else 0) = 0 := by
      have : i + 3 - (i + 1) = 2 := by omega
      rw [this]; norm_num
    have t2 : (if 3 ∣ (i + 3 - (i + 2)) then 1 else 0) = 0 := by
      have : i + 3 - (i + 2) = 1 := by omega
      rw [this]; norm_num
    have t3 : (if 3 ∣ (i + 3 - (i + 3)) then 1 else 0) = 1 := by
      have : i + 3 - (i + 3) = 0 := by omega
      rw [this]; norm_num
    rw [t1, t2, t3]
    ring

theorem SR_eq_convR : ∀ i, SR i = convR i
  | 0 => by decide
  | 1 => by decide
  | (i + 2) => by
    have ih := SR_eq_convR i
    rw [convR, ← ih]
    unfold SR
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have e1 : ∀ j ∈ range (i + 1),
        (j + 1) * (if 2 ∣ (i + 2 - j) then 1 else 0)
          = (j + 1) * (if 2 ∣ (i - j) then 1 else 0) := by
      intro j hj
      have hji : j ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hrw : i + 2 - j = (i - j) + 2 := by omega
      rw [hrw]
      congr 2
      simp [Nat.dvd_add_self_right]
    rw [Finset.sum_congr rfl e1]
    have t1 : (if 2 ∣ (i + 2 - (i + 1)) then 1 else 0) = 0 := by
      have : i + 2 - (i + 1) = 1 := by omega
      rw [this]; norm_num
    have t2 : (if 2 ∣ (i + 2 - (i + 2)) then 1 else 0) = 1 := by
      have : i + 2 - (i + 2) = 0 := by omega
      rw [this]; norm_num
    rw [t1, t2]
    ring

/-! ## D7d -/

theorem Qa_conv_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (Qa * powInd 3) (p ^ i) = convL i := by
  rw [mul_prime_pow _ _ hp, ← SL_eq_convL]
  unfold SL
  exact Finset.sum_congr rfl fun j _ => by
    rw [Qa_prime_pow hp, powInd_prime_pow hp]

theorem sigma_conv_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) :
    ((σ 0 : ArithmeticFunction ℕ) * powInd 2) (p ^ i) = convR i := by
  rw [mul_prime_pow _ _ hp, ← SR_eq_convR]
  unfold SR
  exact Finset.sum_congr rfl fun j _ => by
    rw [sigma_zero_prime_pow hp, powInd_prime_pow hp]

/-- **D7d.** The Dirichlet convolution identity `Q ∗ c = d ∗ s`, where `c` and `s`
are the indicators of cubes and squares. Passing to Dirichlet series this reads

    (Σ Q(n) n^{-s}) · ζ(3s) = ζ(s)² · ζ(2s),

that is `Σ Q(n) n^{-s} = ζ(s)² ζ(2s) / ζ(3s)`. -/
theorem Q_conv_cube_eq_sigma_conv_square :
    Qa * powInd 3 = (σ 0 : ArithmeticFunction ℕ) * powInd 2 := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_Qa.mul (isMultiplicative_powInd 3)) _
    (isMultiplicative_sigma.mul (isMultiplicative_powInd 2))]
  intro p i hp
  rw [Qa_conv_prime_pow hp, sigma_conv_prime_pow hp]
  exact conv_eq i

end VicoEnum
