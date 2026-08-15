/-
  VicoEnum/GeneralWidth.lean

  The Markov-type reduction at arbitrary width.

  Widths 5 and 6 each produced a reduction of the same shape, with `N` replaced by
  `N^2`. This module proves that both are instances of one statement holding at every
  width, and identifies the mechanism as a determinant.

  Write the quiddity entries as `a i = p i / N` and let `Cw N p i k` be the
  homogenised frieze continuant of the window `p i, …, p (i+k-1)`:

      Cw i 0 = 1,   Cw i 1 = p i,   Cw i (k+2) = p (i+k+1) * Cw i (k+1) - N^2 * Cw i k,

  so that `K_k (a i, …) = Cw N p i k / N^k`. At width `n` the parameterisation of
  Proposition 2.1 involves exactly four windows,

      E  = Cw 0 (n-3),   A = Cw 0 (n-4),   B = Cw 1 (n-4),   R = Cw 1 (n-5),

  and `Cw_desnanot` below states the relation between them:

      E * R - A * B = -(N^2)^(n-4).

  That is the Desnanot--Jacobi identity, equivalently `det` of a product of the
  matrices `!![p i, -N^2; 1, 0]`, each of determinant `N^2`. Combined with the ring
  identity `general_factor` and the divisibility exchange `general_dvd_iff`, it gives
  the reduction

      g U V = N^(n-4) (U + V) + M,     N^(n-4) R ∣ g M,     M ∣ N^2 R,

  whose `n = 5` case (`R = 1`) is the width-5 theorem and whose `n = 6` case
  (`R = p 1`) is the width-6 statement.
-/
import VicoEnum.Markov

namespace VicoEnum

/-- The homogenised frieze continuant of the window `p i, …, p (i+k-1)`. Substituting
`a j = p j / N` into the frieze continuant `K` and clearing denominators gives
`K_k (a i, …) = Cw N p i k / N ^ k`, which is why the powers of `N` in the reduction
are the ones they are. -/
def Cw (N : ℤ) (p : ℕ → ℤ) (i : ℕ) : ℕ → ℤ
  | 0 => 1
  | 1 => p i
  | (k + 2) => p (i + k + 1) * Cw N p i (k + 1) - N ^ 2 * Cw N p i k

@[simp] theorem Cw_zero (N : ℤ) (p : ℕ → ℤ) (i : ℕ) : Cw N p i 0 = 1 := rfl

@[simp] theorem Cw_one (N : ℤ) (p : ℕ → ℤ) (i : ℕ) : Cw N p i 1 = p i := rfl

theorem Cw_succ_succ (N : ℤ) (p : ℕ → ℤ) (i k : ℕ) :
    Cw N p i (k + 2) = p (i + k + 1) * Cw N p i (k + 1) - N ^ 2 * Cw N p i k := rfl

/-- **Desnanot--Jacobi for the homogenised continuant.** The four windows appearing in
the width-`n` parameterisation satisfy one relation, and it is the determinant of a
product of `k+2` matrices `!![p j, -N^2; 1, 0]`, each of determinant `N^2`.

The proof is the two-term recurrence applied to both leading windows: the two terms in
`p (i+k+2)` cancel, leaving exactly `-N^2` times the previous instance. -/
theorem Cw_desnanot (N : ℤ) (p : ℕ → ℤ) (i k : ℕ) :
    Cw N p i (k + 2) * Cw N p (i + 1) k - Cw N p i (k + 1) * Cw N p (i + 1) (k + 1)
      = -(N ^ 2) ^ (k + 1) := by
  induction k with
  | zero =>
    show (p (i + 0 + 1) * p i - N ^ 2 * 1) * 1 - p i * p (i + 1) = -(N ^ 2) ^ 1
    have : i + 0 + 1 = i + 1 := by omega
    rw [this]; ring
  | succ j ih =>
    have hidx : i + 1 + j + 1 = i + (j + 1) + 1 := by omega
    rw [Cw_succ_succ N p i (j + 1), Cw_succ_succ N p (i + 1) j, hidx]
    have : -(N ^ 2) ^ (j + 1 + 1) = N ^ 2 * -(N ^ 2) ^ (j + 1) := by ring
    rw [this, ← ih]
    ring

/-- **The factorisation, at every width.** Writing the two shifted continuants as
`A = g U` and `B = g V`, the quantity `M = g U V - N^(k+1) (U + V)` satisfies
`g M = A B - N^(k+1) (A + B)`. This is the identity that gives the reduction a factor
of `g` to spare; at `k = 0` it is `markov_factor`. -/
theorem general_factor (N g U V : ℤ) (k : ℕ) :
    g * (g * U * V - N ^ (k + 1) * (U + V))
      = (g * U) * (g * V) - N ^ (k + 1) * (g * U + g * V) := by
  ring

/-- **The divisibility exchange, at every width.** Given the relation
`N^(k+1) R e = g M` supplied by Desnanot--Jacobi, the lattice condition on the two
outer quiddity entries, `e N^k ∣ N g`, is equivalent to the single condition
`M ∣ N^2 R` on `M` alone.

At `k = 0` and `R = 1` this is `markov_dvd_iff`. The forward direction cancels
`e N^k`, the reverse cancels `R` and then one factor of `N`, so all four
nonvanishing hypotheses are used. -/
theorem general_dvd_iff {N R e g M : ℤ} {k : ℕ}
    (hN : N ≠ 0) (hR : R ≠ 0) (he : e ≠ 0)
    (hrel : N ^ (k + 1) * R * e = g * M) :
    e * N ^ k ∣ N * g ↔ M ∣ N ^ 2 * R := by
  have hNk : (N : ℤ) ^ k ≠ 0 := pow_ne_zero _ hN
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h : e * N ^ k * (N ^ 2 * R - M * t) = 0 := by
      linear_combination (N : ℤ) * hrel + M * ht
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (mul_ne_zero he hNk)
    · linear_combination h1
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h : N * R * (N * g - e * N ^ k * t) = 0 := by
      linear_combination (-t) * hrel + g * ht
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (mul_ne_zero hN hR)
    · linear_combination h1

/-- **The reduction at general width, assembled.** With `A = g U`, `B = g V`,
`gcd(U,V) = 1`, `M = g U V - N^(k+1)(U+V)`, and the Desnanot--Jacobi relation in the
form `N^(k+1) R e = g M`, the width-`n` lattice conditions (`k = n - 5`) collapse to

    g U V = N^(k+1) (U + V) + M,   N^(k+1) R ∣ g M,   M ∣ N^2 R.

The second is the integrality of the middle entry `a_{n-2} = e/N`, and by
`general_dvd_iff` the third is the integrality of the two outer entries. -/
theorem general_reduction {N R e g U V M : ℤ} {k : ℕ}
    (hN : N ≠ 0) (hR : R ≠ 0) (he : e ≠ 0)
    (hM : M = g * U * V - N ^ (k + 1) * (U + V))
    (hrel : N ^ (k + 1) * R * e = g * M) :
    g * U * V = N ^ (k + 1) * (U + V) + M ∧
      N ^ (k + 1) * R ∣ g * M ∧
      (e * N ^ k ∣ N * g ↔ M ∣ N ^ 2 * R) := by
  refine ⟨by rw [hM]; ring, ⟨e, hrel.symm⟩, general_dvd_iff hN hR he hrel⟩

/-- The width-5 case: `k = 0` and `R = 1`, giving `M ∣ N^2` and `N ∣ g M`. -/
theorem general_reduction_width5 {N e g U V M : ℤ}
    (hN : N ≠ 0) (he : e ≠ 0)
    (hM : M = g * U * V - N * (U + V))
    (hrel : N * e = g * M) :
    g * U * V = N * (U + V) + M ∧ N ∣ g * M ∧ (e ∣ N * g ↔ M ∣ N ^ 2) := by
  have h := general_reduction (k := 0) (R := 1) hN one_ne_zero he
    (by simpa using hM) (by simpa using hrel)
  simpa using h

/-- The width-6 case: `k = 1` and `R = p 1 = q`, giving `M ∣ N^2 q` and `N^2 ∣ g M`.
The pattern `N → N^2` observed between widths 5 and 6 is the step `k → k + 1`. -/
theorem general_reduction_width6 {N q e g U V M : ℤ}
    (hN : N ≠ 0) (hq : q ≠ 0) (he : e ≠ 0)
    (hM : M = g * U * V - N ^ 2 * (U + V))
    (hrel : N ^ 2 * q * e = g * M) :
    g * U * V = N ^ 2 * (U + V) + M ∧ N ^ 2 * q ∣ g * M ∧
      (e * N ∣ N * g ↔ M ∣ N ^ 2 * q) := by
  have h := general_reduction (k := 1) (R := q) hN hq he (by simpa using hM)
    (by simpa using hrel)
  simpa using h

/-! ## Discharging `general_reduction`'s hypothesis from Desnanot--Jacobi

`Cw_desnanot` is the identity `lem:dj` states, and `general_reduction` consumes the relation
`N^{k+1} R e = g M`. Nothing connected the two. The passage is pure algebra: writing
`Â = A + N^{k+1} = gU` and `B̂ = B + N^{k+1} = gV`,

    g M = (gU)(gV) - N^{k+1}(gU + gV) = ÂB̂ - N^{k+1}(Â + B̂) = AB - N^{2(k+1)},

and `lem:dj` says `AB = ER + N^{2(k+1)}`, so `g M = ER = N^{k+1} R e`. -/

/-- **From `lem:dj` to the relation `general_reduction` needs.** -/
theorem general_hrel {N e g U V M A B E R : ℤ} {k : ℕ}
    (hdj : E * R - A * B = -(N ^ 2) ^ (k + 1))
    (hE : E = N ^ (k + 1) * e)
    (hU : g * U = A + N ^ (k + 1)) (hV : g * V = B + N ^ (k + 1))
    (hM : M = g * U * V - N ^ (k + 1) * (U + V)) :
    N ^ (k + 1) * R * e = g * M := by
  have hgM : g * M = (g * U) * (g * V) - N ^ (k + 1) * ((g * U) + (g * V)) := by
    rw [hM]; ring
  rw [hU, hV] at hgM
  have hAB : g * M = A * B - (N ^ 2) ^ (k + 1) := by rw [hgM]; ring
  rw [hAB]
  rw [hE] at hdj
  linear_combination hdj

/-- **Theorem `thm:general` with the Desnanot--Jacobi hypothesis discharged.** -/
theorem general_reduction_dj {N e g U V M A B E R : ℤ} {k : ℕ}
    (hN : N ≠ 0) (hR : R ≠ 0) (he : e ≠ 0)
    (hdj : E * R - A * B = -(N ^ 2) ^ (k + 1))
    (hE : E = N ^ (k + 1) * e)
    (hU : g * U = A + N ^ (k + 1)) (hV : g * V = B + N ^ (k + 1))
    (hM : M = g * U * V - N ^ (k + 1) * (U + V)) :
    g * U * V = N ^ (k + 1) * (U + V) + M ∧
      N ^ (k + 1) * R ∣ g * M ∧
      (e * N ^ k ∣ N * g ↔ M ∣ N ^ 2 * R) :=
  general_reduction hN hR he hM (general_hrel hdj hE hU hV hM)

/-- The four windows of `lem:dj` at `i = 0`, which is the instance `thm:general` applies. -/
theorem dj_windows (N : ℤ) (p : ℕ → ℤ) (k : ℕ) :
    Cw N p 0 (k + 2) * Cw N p 1 k - Cw N p 0 (k + 1) * Cw N p 1 (k + 1)
      = -(N ^ 2) ^ (k + 1) :=
  Cw_desnanot N p 0 k

/-- **Theorem `thm:general` with the Desnanot--Jacobi hypothesis actually discharged.**

`general_reduction_dj` still carries `hdj` in its signature; it trades one assumed equation
for another. This is the version where the four windows are the `Cw` continuants and `hdj` is
supplied by `Cw_desnanot`, so nothing about Desnanot--Jacobi is assumed.

What remains hypothesis is the frieze input: that the top window is `N^{k+1} e`, and that `g`
splits the two shifted windows as `gU` and `gV`. Note also that `thm:general` additionally
concludes `gcd(U,V) = 1`, which is not stated here, because `g` is a free integer rather than
the gcd. -/
theorem general_reduction_Cw {N e g U V M : ℤ} {k : ℕ} (p : ℕ → ℤ)
    (hN : N ≠ 0) (hR : Cw N p 1 k ≠ 0) (he : e ≠ 0)
    (hE : Cw N p 0 (k + 2) = N ^ (k + 1) * e)
    (hU : g * U = Cw N p 0 (k + 1) + N ^ (k + 1))
    (hV : g * V = Cw N p 1 (k + 1) + N ^ (k + 1))
    (hM : M = g * U * V - N ^ (k + 1) * (U + V)) :
    g * U * V = N ^ (k + 1) * (U + V) + M ∧
      N ^ (k + 1) * Cw N p 1 k ∣ g * M ∧
      (e * N ^ k ∣ N * g ↔ M ∣ N ^ 2 * Cw N p 1 k) :=
  general_reduction_dj hN hR he (dj_windows N p k) hE hU hV hM

end VicoEnum
