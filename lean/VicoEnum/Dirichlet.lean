/-
  VicoEnum/Dirichlet.lean

  D7, arithmetic core.

  The identity  Σ Q(N) N^{-s} = ζ(s)² ζ(2s) / ζ(3s)  is, after clearing the
  denominator, the Dirichlet convolution identity

        Q ∗ c  =  d ∗ s

  where c is the indicator of perfect cubes (↔ ζ(3s)), s the indicator of perfect
  squares (↔ ζ(2s)) and d the divisor function (↔ ζ(s)²). All four functions are
  multiplicative, so the identity is equivalent to its value at every prime power.
  This file proves that prime-power identity: both sides at `p^n` equal
  `(⌊n/2⌋+1)(⌈n/2⌉+1)`.

  Concretely, at `p^n`:
    (Q ∗ c)(p^n) = Σ_{3j ≤ n} Q(p^{n-3j}) = Σ_{3j ≤ n} (⌊3(n-3j)/2⌋ + 1)   =: convL n
    (d ∗ s)(p^n) = Σ_{2i ≤ n} d(p^{n-2i}) = Σ_{2i ≤ n} (n - 2i + 1)        =: convR n
-/
import VicoEnum.Count6

namespace VicoEnum

/-- The local convolution `(Q ∗ c)(p^n)`, summed over the cube part. -/
def convL : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | (n + 3) => Qlocal (n + 3) + convL n

/-- The local convolution `(d ∗ s)(p^n)`, summed over the square part. -/
def convR : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | (n + 2) => (n + 3) + convR n

/-- The common closed form `(⌊n/2⌋+1)(⌈n/2⌉+1)`, written with `ℕ` division. -/
def closedForm (n : ℕ) : ℕ := (n / 2 + 1) * ((n + 1) / 2 + 1)

theorem convR_closed : ∀ n, convR n = closedForm n
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => by
    have ih := convR_closed n
    rw [convR, ih]
    unfold closedForm
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩ <;> subst hm
    · have h1 : (m + m) / 2 = m := by omega
      have h2 : (m + m + 1) / 2 = m := by omega
      have h3 : (m + m + 2) / 2 = m + 1 := by omega
      have h4 : (m + m + 2 + 1) / 2 = m + 1 := by omega
      rw [h1, h2, h3, h4]; ring
    · have h1 : (2 * m + 1) / 2 = m := by omega
      have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have h3 : (2 * m + 1 + 2) / 2 = m + 1 := by omega
      have h4 : (2 * m + 1 + 2 + 1) / 2 = m + 2 := by omega
      rw [h1, h2, h3, h4]; ring

theorem convL_closed : ∀ n, convL n = closedForm n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (n + 3) => by
    have ih := convL_closed n
    rw [convL, ih]
    unfold closedForm Qlocal
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩ <;> subst hm
    · have h1 : (m + m) / 2 = m := by omega
      have h2 : (m + m + 1) / 2 = m := by omega
      have h3 : (m + m + 3) / 2 = m + 1 := by omega
      have h4 : (m + m + 3 + 1) / 2 = m + 2 := by omega
      have h5 : 3 * (m + m + 3) / 2 = 3 * m + 4 := by omega
      rw [h1, h2, h3, h4, h5]; ring
    · have h1 : (2 * m + 1) / 2 = m := by omega
      have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have h3 : (2 * m + 1 + 3) / 2 = m + 2 := by omega
      have h4 : (2 * m + 1 + 3 + 1) / 2 = m + 2 := by omega
      have h5 : 3 * (2 * m + 1 + 3) / 2 = 3 * m + 6 := by omega
      rw [h1, h2, h3, h4, h5]; ring

/-- **D7, the prime-power identity.** The two local convolutions agree, which is
exactly `(Q ∗ c)(p^n) = (d ∗ s)(p^n)` and hence, by multiplicativity and the Euler
product, `Σ Q(N)N^{-s} · ζ(3s) = ζ(s)²ζ(2s)`. -/
theorem conv_eq (n : ℕ) : convL n = convR n := by
  rw [convL_closed, convR_closed]

/-- Sanity: the shared value at small `n` is `1, 2, 4, 6, 9, 12, 16`. -/
example : (List.range 7).map convL = [1, 2, 4, 6, 9, 12, 16] := by decide
example : (List.range 7).map convR = [1, 2, 4, 6, 9, 12, 16] := by decide

end VicoEnum
