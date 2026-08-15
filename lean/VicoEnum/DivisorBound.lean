/-
  VicoEnum/DivisorBound.lean

  The divisor bound `d(n) = O_ε(n^ε)`, in the form the paper consumes.

  Corollary `cor:t5upper` and Theorem `thm:primesqrt` both end with a step of the form
  "and `d(n) = O_ε(n^ε)` gives the bound". That step was the only thing in either proof
  left outside Lean, and Mathlib v4.15.0 carries only the trivial `d(n) ≤ n`.

  Stated over `ℕ` without real exponents, the bound is

      d(n) ^ k  ≤  C k * n,        C k = ((2k)^k)^(2^k),

  which says `d(n) ≤ (C k · n)^{1/k}`, so taking `k` large gives `d(n) = O_ε(n^ε)`.

  The proof is the classical one. Since `d(n)^k = ∏ (a_p+1)^k` and `n = ∏ p^{a_p}`, it is
  enough to bound `(a+1)^k` by `p^a` up to a constant, and a constant is needed only for
  the primes below `2^k`, of which there are fewer than `2^k`.

  The step that usually invokes analysis, that a polynomial is dominated by an
  exponential, is elementary here. Writing `a = kb + r` with `r < k`,

      a + 1 ≤ (k+r)(b+1)   and   b + 1 ≤ 2^b,

  so `(a+1)^k ≤ (k+r)^k (2^b)^k ≤ (2k)^k 2^{kb} ≤ (2k)^k 2^a`.
-/
import VicoEnum.Bounds5

namespace VicoEnum

open Finset

/-- `b + 1 ≤ 2 ^ b`. -/
theorem succ_le_two_pow (b : ℕ) : b + 1 ≤ 2 ^ b := by
  induction b with
  | zero => norm_num
  | succ m ih =>
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega

/-- **A polynomial is dominated by an exponential**, with an explicit constant and no
analysis. -/
theorem poly_le_two_pow (k : ℕ) (hk : 0 < k) (a : ℕ) :
    (a + 1) ^ k ≤ (2 * k) ^ k * 2 ^ a := by
  obtain ⟨b, r, hr, rfl⟩ : ∃ b r, r < k ∧ a = k * b + r :=
    ⟨a / k, a % k, Nat.mod_lt _ hk, (Nat.div_add_mod a k).symm⟩
  have hb : b + 1 ≤ 2 ^ b := succ_le_two_pow b
  have h1 : k * b + r + 1 ≤ (k + r) * (b + 1) := by nlinarith [Nat.zero_le (r * b)]
  have h2 : k + r ≤ 2 * k := by omega
  calc (k * b + r + 1) ^ k ≤ ((k + r) * (b + 1)) ^ k := Nat.pow_le_pow_left h1 k
    _ = (k + r) ^ k * (b + 1) ^ k := mul_pow _ _ _
    _ ≤ (2 * k) ^ k * (2 ^ b) ^ k :=
        Nat.mul_le_mul (Nat.pow_le_pow_left h2 k) (Nat.pow_le_pow_left hb k)
    _ = (2 * k) ^ k * 2 ^ (k * b) := by rw [← pow_mul, Nat.mul_comm b k]
    _ ≤ (2 * k) ^ k * 2 ^ (k * b + r) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **The large primes cost nothing.** If `p ≥ 2^k` then `(a+1)^k ≤ p^a` outright. -/
theorem poly_le_prime_pow {k p a : ℕ} (hp : 2 ^ k ≤ p) : (a + 1) ^ k ≤ p ^ a := by
  have h1 : a + 1 ≤ 2 ^ a := succ_le_two_pow a
  calc (a + 1) ^ k ≤ (2 ^ a) ^ k := Nat.pow_le_pow_left h1 k
    _ = (2 ^ k) ^ a := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ p ^ a := Nat.pow_le_pow_left hp a

/-- The constant. -/
def divBoundConst (k : ℕ) : ℕ := ((2 * k) ^ k) ^ (2 ^ k)

/-- **The divisor bound.** `d(n)^k ≤ C k * n`, so `d(n) ≤ (C k · n)^{1/k}` and taking `k`
large gives `d(n) = O_ε(n^ε)`. This is the step that Corollary `cor:t5upper` and Theorem
`thm:primesqrt` consume, and it mentions no frieze. -/
theorem card_divisors_pow_le (k : ℕ) (hk : 0 < k) {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.card) ^ k ≤ divBoundConst k * n := by
  classical
  have hSpos : 0 < (2 * k) ^ k := by positivity
  have hcard : n.divisors.card = ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
    rw [Nat.card_divisors hn]
  have hnprod : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
    have := Nat.factorization_prod_pow_eq_self hn
    rwa [Finsupp.prod, Nat.support_factorization] at this
  -- per-prime bound
  have key : ∀ p ∈ n.primeFactors, (n.factorization p + 1) ^ k
      ≤ (if p < 2 ^ k then (2 * k) ^ k else 1) * p ^ (n.factorization p) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    by_cases hlt : p < 2 ^ k
    · rw [if_pos hlt]
      calc (n.factorization p + 1) ^ k
          ≤ (2 * k) ^ k * 2 ^ (n.factorization p) := poly_le_two_pow k hk _
        _ ≤ (2 * k) ^ k * p ^ (n.factorization p) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpp.two_le _)
    · rw [if_neg hlt, one_mul]
      exact poly_le_prime_pow (not_lt.mp hlt)
  -- the constant product
  have hconst : ∏ p ∈ n.primeFactors, (if p < 2 ^ k then (2 * k) ^ k else 1)
      ≤ ((2 * k) ^ k) ^ (2 ^ k) := by
    rw [← Finset.prod_filter]
    rw [Finset.prod_const]
    refine Nat.pow_le_pow_right hSpos ?_
    have hsub : n.primeFactors.filter (fun p => p < 2 ^ k) ⊆ Finset.range (2 ^ k) := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      exact Finset.mem_range.mpr hp.2
    simpa using Finset.card_le_card hsub
  calc (n.divisors.card) ^ k
      = ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ k := by
        rw [hcard, ← Finset.prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors,
          ((if p < 2 ^ k then (2 * k) ^ k else 1) * p ^ (n.factorization p)) :=
        Finset.prod_le_prod' key
    _ = (∏ p ∈ n.primeFactors, (if p < 2 ^ k then (2 * k) ^ k else 1))
          * ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := Finset.prod_mul_distrib
    _ ≤ ((2 * k) ^ k) ^ (2 ^ k) * n := by
        rw [hnprod]
        exact Nat.mul_le_mul_right _ hconst

/-- The bound in the form actually used: `d(n) ≤ C k * m` whenever `n ≤ m^k`, which is how
a `n^{1/k}` factor enters the sums of Corollary `cor:t5upper` and
Theorem `thm:primesqrt`. -/
theorem card_divisors_le_of_pow (k : ℕ) (hk : 0 < k) {n m : ℕ} (hn : n ≠ 0)
    (h : n ≤ m ^ k) : (n.divisors.card) ^ k ≤ divBoundConst k * m ^ k := by
  exact le_trans (card_divisors_pow_le k hk hn) (Nat.mul_le_mul_left _ h)

/-! ## The `O_ε` step, as an inequality over `ℕ`

`t5_prime_count_bound` bounds the width-5 count at a prime by `∑_{t ≤ K} d(p+t)`, and
`card_divisors_pow_le` bounds each `d`. Combining them removes the last appeal to
`O`-notation from Theorem `thm:primesqrt`: the count is at most `K · b` for a `b` with
`b^k ≤ C_k (p+K)`, that is at most `K (C_k(p+K))^{1/k}`. With `K = 1 + ⌊√p⌋` this reads
`O_k(p^{1/2 + 1/k})`, and `k` is arbitrary.
-/

/-- **The sum of divisor counts, bounded.** Every `d(p+t)` for `t ≤ K` is at most a common
`b` whose `k`-th power is at most `C_k (p+K)`. -/
theorem sum_card_divisors_le (k K p : ℕ) (hk : 0 < k) (hp : 0 < p) (hK : 0 < K) :
    ∃ b : ℕ, (∑ t ∈ Finset.Icc 1 K, (p + t).divisors.card) ≤ K * b ∧
      b ^ k ≤ divBoundConst k * (p + K) := by
  classical
  have hne : (Finset.Icc 1 K).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hK⟩⟩
  refine ⟨(Finset.Icc 1 K).sup (fun t => (p + t).divisors.card), ?_, ?_⟩
  · have hle : ∀ t ∈ Finset.Icc 1 K,
        (p + t).divisors.card ≤ (Finset.Icc 1 K).sup (fun t => (p + t).divisors.card) :=
      fun t ht => Finset.le_sup (f := fun t => (p + t).divisors.card) ht
    have hcard : (Finset.Icc 1 K).card = K := by rw [Nat.card_Icc]; omega
    calc ∑ t ∈ Finset.Icc 1 K, (p + t).divisors.card
        ≤ (Finset.Icc 1 K).card *
            (Finset.Icc 1 K).sup (fun t => (p + t).divisors.card) := by
          simpa using Finset.sum_le_card_nsmul _ _ _ hle
      _ = K * (Finset.Icc 1 K).sup (fun t => (p + t).divisors.card) := by rw [hcard]
  · obtain ⟨t, ht, hbt⟩ :=
      Finset.exists_mem_eq_sup (Finset.Icc 1 K) hne (fun t => (p + t).divisors.card)
    have htK : t ≤ K := (Finset.mem_Icc.mp ht).2
    have hpt : p + t ≠ 0 := by omega
    rw [hbt]
    calc ((p + t).divisors.card) ^ k
        ≤ divBoundConst k * (p + t) := card_divisors_pow_le k hk hpt
      _ ≤ divBoundConst k * (p + K) := Nat.mul_le_mul_left _ (by omega)

/-- **Theorem `thm:primesqrt`, with no `O` left in it.** The pairs counted by
`t5_prime_count_bound` number at most `K · b` with `b^k ≤ C_k (p+K)`. Taking
`K = 1 + ⌊√p⌋`, which `t5_cubic_hyperbola_nat` licenses, this is
`p^{1/2 + 1/k}` up to a constant depending only on `k`. -/
theorem t5_prime_sqrt_bound (k K B p : ℕ) (hk : 0 < k) (hp : 0 < p) (hK : 0 < K)
    (hKb : ∀ t m : ℕ, 0 < t → 0 < m → t ≤ m → t * m ∣ p + t + m → t ≤ K) :
    ∃ b : ℕ,
      (((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter
        (fun x : ℕ × ℕ => x.1 ≤ x.2 ∧ x.1 * x.2 ∣ p + x.1 + x.2)).card ≤ K * b ∧
      b ^ k ≤ divBoundConst k * (p + K) := by
  obtain ⟨b, hb1, hb2⟩ := sum_card_divisors_le k K p hk hp hK
  exact ⟨b, le_trans (t5_prime_count_bound p K B hp hKb) hb1, hb2⟩

end VicoEnum
