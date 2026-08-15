/-
  VicoEnum/Markov.lean

  The algebraic core of the Markov-type reduction of T(N,5).

  With `x + N = gu`, `y + N = gv` and `M = guv - N(u+v)`, the quantity
  `e = xy - N^2` factors as `gM`, and the divisibility `f | Ng` governing the outer
  frieze entries is equivalent to `M | N^2`. Those two facts are what turn the
  width-5 conditions into

      g u v = N(u+v) + M,    M | N^2,    N | gM.
-/
import VicoEnum.Basic

namespace VicoEnum

/-- **The factorisation.** Writing `x + N = gu` and `y + N = gv`, the quantity
`e = xy - N^2` equals `g` times `M = guv - N(u+v)`. This is why the reduction has a
factor of `g` to spare, and it is a ring identity. -/
theorem markov_factor (N g u v : ℤ) :
    (g * u - N) * (g * v - N) - N ^ 2 = g * (g * u * v - N * (u + v)) := by
  ring

/-- **The divisibility exchange.** If `N f = g M` with `N` and `g` nonzero, then
`f ∣ N g` is equivalent to `M ∣ N^2`. This is the step that replaces the condition on
the outer frieze entries by a condition on `M` alone. Both hypotheses are used: the
forward direction cancels `g`, the reverse cancels `N`. -/
theorem markov_dvd_iff {N f g M : ℤ} (hN : N ≠ 0) (hg : g ≠ 0) (hNf : N * f = g * M) :
    f ∣ N * g ↔ M ∣ N ^ 2 := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h : g * (N ^ 2 - M * t) = 0 := by linear_combination N * ht + t * hNf
    have := mul_eq_zero.mp h
    rcases this with h1 | h1
    · exact absurd h1 hg
    · linarith [h1]
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h : N * (N * g - f * t) = 0 := by linear_combination g * ht - t * hNf
    have := mul_eq_zero.mp h
    rcases this with h1 | h1
    · exact absurd h1 hN
    · linarith [h1]

/-- **The gcd is automatic.** With `gcd(u,v) = 1`, the pair `(gu, gv)` has gcd exactly
`g`, so requiring `g = gcd(x+N, y+N)` imposes nothing beyond `gcd(u,v) = 1`. The
adversarial review of the reduction found this condition to be redundant. -/
theorem markov_gcd (g u v : ℕ) (h : Nat.gcd u v = 1) :
    Nat.gcd (g * u) (g * v) = g := by
  rw [Nat.gcd_mul_left, h, Nat.mul_one]

end VicoEnum
