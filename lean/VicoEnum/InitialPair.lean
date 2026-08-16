/-
  VicoEnum/InitialPair.lean

  The initial pair exists. This closes the last step of the correspondence.

  Realising a prescribed frieze as a path in `F_R` is the choice of a pair `(v₀, v₁)` with
  `[v₀,v₁] = R`, since every other vertex is then `m_{i,0} v₁ - m_{i,1} v₀`. Writing the two
  leading columns as `μ_i / N` and `ν_i / N`, and taking

      v₀ = (g₀/K, 0),   v₁ = (e, N/g₀),      g₀ = gcd_i μ_i,

  the second coordinate is integral automatically (`second_coord_integral`) and only one
  congruence remains,

      N ∣ μ_i e - ν_i (g₀/K)   for every i,

  in the single unknown `e`. This file solves it, explicitly.

  Two ingredients. The first is the two-column identity

      m_{i,0} m_{j,1} - m_{i,1} m_{j,0} = m_{j,i},

  which says a frieze is determined by any two adjacent columns. It is not imported from the
  path model, which would be circular: both sides satisfy the same three-term recurrence in
  `i` and agree at `i = j` and `i = j+1`, so `recurrence_unique` gives it. Cleared of
  denominators it reads `μ_i ν_j - ν_i μ_j = N w_{j,i}` with `w_{j,i}` a frieze numerator,
  hence divisible by `K`.

  The second is B\'ezout. Choosing `λ` with `∑ λ_j μ_j = g₀` and setting `K e = ∑ λ_j ν_j`,
  which is possible because `K` divides every `ν_j`, one computes

      K(μ_i e - ν_i d) = ∑_j λ_j (μ_i ν_j - ν_i μ_j) = N ∑_j λ_j w_{j,i} = N K ∑_j λ_j w'_{j,i},

  and cancelling `K` gives the congruence. That is `initial_pair_congruence`.
-/
import VicoEnum.Surjectivity
import Mathlib.Algebra.BigOperators.Ring

namespace VicoEnum

open Finset

/-- **A frieze is determined by two adjacent columns.** Any column satisfying the frieze
recurrence and agreeing with a fixed combination of columns zero and one at two consecutive
indices agrees with it everywhere. Applied with `a = m_{j,0}` and `b = m_{j,1}` this is the
two-column identity `m_{i,j} = m_{j,0} m_{i,1} - m_{j,1} m_{i,0}`.

The proof is `recurrence_unique`, so it uses only the frieze recurrence. It does not use the
path model, which would be circular here: the path is what this identity is used to build. -/
theorem two_column {c : ℕ → ℤ} {f g h : ℕ → ℤ} {a b : ℤ}
    (hf : ∀ i, f (i + 2) = c i * f (i + 1) - f i)
    (hg : ∀ i, g (i + 2) = c i * g (i + 1) - g i)
    (hh : ∀ i, h (i + 2) = c i * h (i + 1) - h i)
    (h0 : h 0 = a * g 0 - b * f 0) (h1 : h 1 = a * g 1 - b * f 1) :
    ∀ i, h i = a * g i - b * f i := by
  refine recurrence_unique c h (fun i => a * g i - b * f i) h0 h1 hh ?_
  intro i
  show a * g (i + 2) - b * f (i + 2)
      = c i * (a * g (i + 1) - b * f (i + 1)) - (a * g i - b * f i)
  rw [hf i, hg i]
  ring

/-- **The two-column identity, cleared of denominators.** If the columns `μ` and `ν` and the
array `w` satisfy `μ_i ν_j - ν_i μ_j = N w_{j,i}`, then any common divisor of the `w` is a
common divisor of the corresponding combinations. This is the shape in which the identity
enters the argument. -/
theorem sum_dvd_of_dvd {K : ℤ} {n : ℕ} {lam : ℕ → ℤ} {w : ℕ → ℕ → ℤ} (i : ℕ)
    (hKw : ∀ j, K ∣ w j i) : K ∣ ∑ j ∈ range n, lam j * w j i :=
  Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (hKw j) (lam j)

/-- **The initial pair exists.** Given the two-column relation `μ_i ν_j - ν_i μ_j = N w_{j,i}`
with `K` dividing every `w_{j,i}`, a B\'ezout combination `∑ λ_j μ_j = g` and the value `e`
determined by `K e = ∑ λ_j ν_j`, the congruence `N ∣ μ_i e - ν_i d` holds for every `i`,
where `K d = g`.

This is the last step of the correspondence between positive friezes over `(1/N)ℤ` and
minimal clockwise paths, and it is constructive: `e` is exhibited, not merely shown to
exist. -/
theorem initial_pair_congruence {N K g d e : ℤ} {n : ℕ} {μ ν lam : ℕ → ℤ} {w : ℕ → ℕ → ℤ}
    (hK : K ≠ 0) (hd : K * d = g)
    (hg : ∑ j ∈ range n, lam j * μ j = g)
    (he : K * e = ∑ j ∈ range n, lam j * ν j)
    (hkey : ∀ i j, μ i * ν j - ν i * μ j = N * w j i)
    (hKw : ∀ i j, K ∣ w j i) (i : ℕ) :
    N ∣ μ i * e - ν i * d := by
  obtain ⟨S, hS⟩ := sum_dvd_of_dvd (K := K) (n := n) (lam := lam) (w := w) i (fun j => hKw i j)
  refine ⟨S, mul_left_cancel₀ hK ?_⟩
  calc K * (μ i * e - ν i * d)
      = μ i * (K * e) - ν i * (K * d) := by ring
    _ = μ i * (∑ j ∈ range n, lam j * ν j) - ν i * (∑ j ∈ range n, lam j * μ j) := by
        rw [he, hd, hg]
    _ = ∑ j ∈ range n, lam j * (μ i * ν j - ν i * μ j) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j ∈ range n, lam j * (N * w j i) := by
        exact Finset.sum_congr rfl fun j _ => by rw [hkey]
    _ = N * ∑ j ∈ range n, lam j * w j i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = N * (K * S) := by rw [hS]
    _ = K * (N * S) := by ring

/-- The value `e` is available: `K` divides `∑ λ_j ν_j` whenever it divides every `ν_j`,
which it does, `K` being the greatest common divisor of all the frieze numerators. -/
theorem e_exists {K : ℤ} {n : ℕ} {ν lam : ℕ → ℤ} (hKν : ∀ j, K ∣ ν j) :
    K ∣ ∑ j ∈ range n, lam j * ν j :=
  Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (hKν j) (lam j)

end VicoEnum
