/-
  VicoEnum/SupportCount.lean

  Proposition `prop:support`, the local count.

  `support_dvd_nat` is the vanishing condition: the `M`-th term of `eq:decomp` vanishes
  unless `d_M ∣ M`. At a prime with `p^a ‖ N` and `p^b ‖ M` that condition reads
  `max(0, a-b) ≤ b`, which is `a ≤ 2b`, and `M ∣ N^2` reads `b ≤ 2a`. So the exponents that
  contribute at that prime are exactly

      ⌈a/2⌉ ≤ b ≤ 2a,

  and there are `2a - ⌈a/2⌉ + 1` of them. In `ℕ` division `⌈a/2⌉` is `(a+1)/2`.

  WHAT IS AND IS NOT PROVED. The interval arithmetic is here: `a - b ≤ b` is `a ≤ 2b`, the
  two-sided condition is membership of `Finset.Icc ⌈a/2⌉ (2a)`, and that interval has the
  stated cardinality. The `p`-adic step is here too: `factorization_dM` computes the exponent
  of `d_M` and `dM_dvd_iff` turns the divisibility into the exponent condition at every prime.
  What is NOT here is the product over primes, which is what Proposition `prop:support`
  actually concludes. So `prop:support` is not closed by this file.
-/
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace VicoEnum

/-- `⌈a/2⌉` in `ℕ` division. -/
def halfUp (a : ℕ) : ℕ := (a + 1) / 2

/-- **The arithmetic translation.** The exponent of `d_M = N/gcd(N,M)` at a prime is
`max(0, a-b)`, which in `ℕ` subtraction is `a - b`, so `d_M ∣ M` reads `a - b ≤ b`. That is
`a ≤ 2b`. This lemma is the arithmetic step alone; the `p`-adic fact that the exponent of
`d_M` really is `a - b` is `factorization_dM` below. -/
theorem local_translate (a b : ℕ) : a - b ≤ b ↔ a ≤ 2 * b := by omega

/-- `a ≤ 2b` is `⌈a/2⌉ ≤ b`. -/
theorem local_condition (a b : ℕ) : a ≤ 2 * b ↔ halfUp a ≤ b := by
  unfold halfUp; omega

/-- The contributing exponents at a prime are exactly the interval. -/
theorem local_mem (a b : ℕ) : (a ≤ 2 * b ∧ b ≤ 2 * a) ↔ b ∈ Finset.Icc (halfUp a) (2 * a) := by
  rw [Finset.mem_Icc, ← local_condition]

/-- **Proposition `prop:support`, the local count.** -/
theorem local_count (a : ℕ) :
    (Finset.Icc (halfUp a) (2 * a)).card = 2 * a - halfUp a + 1 := by
  rw [Nat.card_Icc]
  unfold halfUp
  omega

/-- The count is at least one, so no prime kills the whole product. -/
theorem local_count_pos (a : ℕ) : 0 < (Finset.Icc (halfUp a) (2 * a)).card := by
  rw [local_count]; omega

/-- The exponent `b = a` always contributes, which is the divisor `M = N`. -/
theorem local_mem_self (a : ℕ) : a ∈ Finset.Icc (halfUp a) (2 * a) := by
  rw [← local_mem]; omega

/-- The first few local counts: exponents `a = 0,1,2,3,4` contribute `1,2,4,5,7` divisors.
Cross-checked by direct enumeration in `code/support_local.py`. -/
theorem local_count_small :
    (Finset.Icc (halfUp 0) (2 * 0)).card = 1 ∧
    (Finset.Icc (halfUp 1) (2 * 1)).card = 2 ∧
    (Finset.Icc (halfUp 2) (2 * 2)).card = 4 ∧
    (Finset.Icc (halfUp 3) (2 * 3)).card = 5 ∧
    (Finset.Icc (halfUp 4) (2 * 4)).card = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [local_count]; unfold halfUp; norm_num)

/-! ## The `p`-adic step

`d_M = N/gcd(N,M)`, so its exponent at a prime is `a - min(a,b) = max(0, a-b)`, which in `ℕ`
subtraction is `a - b`. Combined with `local_translate` this turns the divisibility `d_M ∣ M`
into the two-sided exponent condition, with no reference to any single prime. -/

/-- **The exponent of `d_M`.** `ν_p(N/gcd(N,M)) = max(0, ν_p N - ν_p M)`. -/
theorem factorization_dM {N M : ℕ} (hN : N ≠ 0) (hM : M ≠ 0) (p : ℕ) :
    (N / Nat.gcd N M).factorization p = N.factorization p - M.factorization p := by
  rw [Nat.factorization_div (Nat.gcd_dvd_left N M), Nat.factorization_gcd hN hM]
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.inf_apply]
  omega

/-- **The vanishing condition, globally.** `d_M ∣ M` is `ν_p N ≤ 2 ν_p M` at every prime.
This is Proposition `prop:support`'s condition with the `p`-adic step included. -/
theorem dM_dvd_iff {N M : ℕ} (hN : N ≠ 0) (hM : M ≠ 0) :
    (N / Nat.gcd N M) ∣ M ↔ ∀ p, N.factorization p ≤ 2 * M.factorization p := by
  have hg : 0 < Nat.gcd N M :=
    Nat.pos_of_ne_zero (fun h => hN (Nat.eq_zero_of_gcd_eq_zero_left h))
  have hd : N / Nat.gcd N M ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.gcd_dvd_left N M)) hg).ne'
  rw [← Nat.factorization_le_iff_dvd hd hM]
  constructor
  · intro h p
    have := h p
    rw [factorization_dM hN hM p] at this
    omega
  · intro h
    intro p
    rw [factorization_dM hN hM p]
    have := h p
    omega

end VicoEnum
