/-
  VicoEnum/External.lean

  The steps that consume input from outside this development.

  Four results in the paper rest on something not proved here: Linnik's theorem, a
  divisor-sum bound of Shiu type, the passage from an explicit divisor-sum bound to
  `O_ε`, and the Dirichlet series identity behind Corollary `cor:dirichlet`. In each case
  the external input is isolated as an explicit hypothesis and the step that consumes it is
  proved. What remains outside Lean is then exactly the named theorem, not the argument
  around it.

  This is weaker than proving the inputs and stronger than leaving the whole step
  unformalised. The label on each paper row is the minimum over the chain (Rule 0), so
  those rows stay PROVED; what these declarations remove is the possibility that the
  *derivation* is wrong.
-/
import VicoEnum.ShiftDecomp

namespace VicoEnum

open Finset

/-! ## The passage to `O_ε`

Corollary `cor:t5upper` bounds `T(N,5)` by a sum of divisor counts and then reads off
`O_ε(N^{1+ε})`. The reading off is this lemma: an explicit bound `T ≤ A·b` together with
the divisor bound on `b` gives a `k`-th power bound for every `k`, and `k`-th roots of
`N^{k+1}` are `N^{1+1/k}`. -/

/-- **The passage to `O_ε`, as an inequality.** If the count is at most `A N` times a
quantity whose `k`-th power the divisor bound controls, then its `k`-th power is controlled.
Taking `k` large is what turns this into `O_ε`. -/
theorem pow_bound_of_divisor_sum {T A B : ℕ → ℕ} (k : ℕ)
    (hT : ∀ N, 0 < N → ∃ b : ℕ, T N ≤ A N * b ∧ b ^ k ≤ divBoundConst k * B N) :
    ∀ N, 0 < N → (T N) ^ k ≤ (A N) ^ k * (divBoundConst k * B N) := by
  intro N hN
  obtain ⟨b, h1, h2⟩ := hT N hN
  calc (T N) ^ k ≤ (A N * b) ^ k := Nat.pow_le_pow_left h1 k
    _ = (A N) ^ k * b ^ k := mul_pow _ _ _
    _ ≤ (A N) ^ k * (divBoundConst k * B N) := Nat.mul_le_mul_left _ h2

/-- The same statement with the two factors combined, in the shape
`(T N)^k ≤ C · (A N)^k · B N`, which is what a bound of the form `N^{1+1/k}` looks like once
`A N` is polynomial in `N` and `B N` is linear. -/
theorem pow_bound_combined {T A B : ℕ → ℕ} (k : ℕ)
    (hT : ∀ N, 0 < N → ∃ b : ℕ, T N ≤ A N * b ∧ b ^ k ≤ divBoundConst k * B N) :
    ∃ C : ℕ, ∀ N, 0 < N → (T N) ^ k ≤ C * ((A N) ^ k * B N) :=
  ⟨divBoundConst k, fun N hN => by
    have := pow_bound_of_divisor_sum k hT N hN
    calc (T N) ^ k ≤ (A N) ^ k * (divBoundConst k * B N) := this
      _ = divBoundConst k * ((A N) ^ k * B N) := by ring⟩

/-! ## Proposition `prop:lower`, the consequence

`cubic_lower_card` proves `C(p) ≥ d(p+1)`, hence `T(p,5) ≥ 5d(p+1)`. The paper then
concludes that `T(N,5) ≍ d(N²)log²N` fails, because at a prime `d(p²) = 3` is constant while
`d(p+1)` is not bounded by any fixed multiple of `log²p`. That last fact is Linnik's theorem
and is the external input. -/

/-- **The asymptotic fails, given the growth input.** If the count is bounded below by
`5 d(p+1)` at primes, and `d(p+1)` exceeds every fixed multiple of `L p` somewhere, then no
bound `T(p,5) ≤ c · L p` can hold. Instantiating `L p = 3 log²p` is the case in the paper;
the growth hypothesis is what Linnik's theorem supplies and is not proved here. -/
theorem asymptotic_fails {L T : ℕ → ℕ}
    (hlow : ∀ p : ℕ, p.Prime → 5 * (p + 1).divisors.card ≤ T p)
    (hgrow : ∀ c : ℕ, ∃ p : ℕ, p.Prime ∧ c * L p < (p + 1).divisors.card) :
    ¬ ∃ c : ℕ, ∀ p : ℕ, p.Prime → T p ≤ c * L p := by
  rintro ⟨c, hc⟩
  obtain ⟨p, hp, hgt⟩ := hgrow c
  have h1 := hlow p hp
  have h2 := hc p hp
  have hd : 0 < (p + 1).divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  omega

/-! ## Theorem `thm:primecube`, the divisor sum

The `p^{1/3+ε}` bound splits the solutions of the cubic by the least variable, which
`cube_root_min` caps at `(2p)^{1/3}`, and bounds each fibre by a divisor count. Summing needs
a bound on `∑_{s ≤ S} d(sp+1)`, which the paper takes from Shiu. The step that consumes it is
the following. -/

/-- **The cube-root bound, given the divisor sum.** A count bounded by three times a sum of
fibre sizes, each fibre bounded by the divisor count of its shifted number, is bounded by
three times any bound on that sum of divisor counts. The bound on the sum is the external
input; this is the step that consumes it. -/
theorem cube_bound_of_divisor_sum {c : ℕ} {S D p : ℕ} {f : ℕ → ℕ}
    (hc : c ≤ 3 * ∑ s ∈ Finset.range (S + 1), f s)
    (hf : ∀ s ∈ Finset.range (S + 1), f s ≤ (s * p + 1).divisors.card)
    (hsum : ∑ s ∈ Finset.range (S + 1), (s * p + 1).divisors.card ≤ S * D) :
    c ≤ 3 * (S * D) :=
  le_trans hc (Nat.mul_le_mul_left 3 (le_trans (Finset.sum_le_sum hf) hsum))

/-! ## Corollary `cor:dirichlet`, the series

`Q_conv_cube_eq_sigma_conv_square` is the coefficient identity `Q ∗ c = d ∗ s` with `c` and
`s` the indicators of cubes and squares, and it is VERIFIED. Passing from it to
`(∑ Q(n)n^{-s})ζ(3s) = ζ(s)²ζ(2s)` needs `LSeries_mul` together with convergence of the four
series. That passage is **not** formalised here: it requires the `ArithmeticFunction ℂ`
coercion machinery around `LSeries_mul`, which is not set up in this development. The row
stays PROVED, and what is missing is the passage, not the coefficient identity. -/

end VicoEnum
