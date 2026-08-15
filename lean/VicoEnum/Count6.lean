/-
  VicoEnum/Count6.lean

  D9:  the width-6 enumeration is complete.
  D7:  the local generating function behind the Dirichlet series.
-/
import VicoEnum.Count
import VicoEnum.Palindromic

namespace VicoEnum

/-! ## D9: width-6 completeness

With `a₀ = p/N`, `a₁ = q/N`, `a₂ = r/N` and `e` the middle quiddity numerator,
the defining relations are `pqr = N²(e+p+r)` together with `e ∣ pq`, `e ∣ qr`
and `e ∣ N(p+r)`.
-/

/-- The arithmetic conditions on the numerators of a width-6 frieze over `(1/N)ℤ`. -/
def W6 (N p q r e : ℕ) : Prop :=
  0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < e ∧
    p * q * r = N ^ 2 * (e + p + r) ∧ e ∣ p * q ∧ e ∣ q * r ∧ e ∣ N * (p + r)

instance (N p q r e : ℕ) : Decidable (W6 N p q r e) := by unfold W6; infer_instance

/-- **D9, the search bound.** Ordering the outer pair so that `p ≤ r`, the product
`pq` is bounded by `2N²(N+1)`. This is the `ℕ` form of `width6_bound`, and it is
what makes the width-6 enumeration complete rather than truncated. -/
theorem width6_bound_nat {N p q r e : ℕ} (hN : 0 < N) (hpr : p ≤ r)
    (h : W6 N p q r e) : p * q ≤ 2 * N ^ 2 * (N + 1) := by
  obtain ⟨hp, hq, hr, he, hkey, _, _, hdvd⟩ := h
  have hNZ : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hrZ : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hprZ : (p : ℤ) ≤ (r : ℤ) := by exact_mod_cast hpr
  have hdvdZ : (e : ℤ) ∣ (N : ℤ) * ((p : ℤ) + (r : ℤ)) := by
    have := Int.natCast_dvd_natCast.mpr hdvd
    push_cast at this
    exact this
  have hkeyZ : (p : ℤ) * (q : ℤ) * (r : ℤ)
      = (N : ℤ) ^ 2 * ((e : ℤ) + (p : ℤ) + (r : ℤ)) := by exact_mod_cast hkey
  have := width6_bound hNZ hpZ hqZ hrZ heZ hprZ hdvdZ hkeyZ
  exact_mod_cast this

/-- Every width-6 solution has its outer pair inside an explicit box. Swapping
`p` and `r` covers the other ordering, so the enumeration over
`{(p,q) : pq ≤ 2N²(N+1)}` together with the solved `r` misses nothing. -/
theorem W6_mem_box {N p q r e : ℕ} (hN : 0 < N) (h : W6 N p q r e) :
    p * q ≤ 2 * N ^ 2 * (N + 1) ∨ r * q ≤ 2 * N ^ 2 * (N + 1) := by
  rcases le_total p r with hpr | hrp
  · exact Or.inl (width6_bound_nat hN hpr h)
  · obtain ⟨hp, hq, hr, he, hkey, h1, h2, h3⟩ := h
    refine Or.inr (width6_bound_nat (e := e) hN hrp ⟨hr, hq, hp, he, ?_, ?_, ?_, ?_⟩)
    · rw [show r * q * p = p * q * r by ring, hkey, show e + r + p = e + p + r by ring]
    · rwa [mul_comm q r] at h2
    · rwa [mul_comm p q] at h1
    · rwa [show r + p = p + r from Nat.add_comm r p]

/-! ## D7: the local generating function

`Q(p^α) = ⌊3α/2⌋ + 1`. The Dirichlet series `Σ Q(N)N^{-s} = ζ(s)²ζ(2s)/ζ(3s)`
is, by multiplicativity and the Euler product, exactly the statement that the
local generating function is

    Σ_α (⌊3α/2⌋+1) x^α = (1 - x³) / ((1-x)²(1-x²)).

Clearing denominators, `(1-x)²(1-x²) = 1 - 2x + 2x³ - x⁴`, so the identity is
equivalent to the linear recurrence proved below together with the four initial
values.
-/

/-- The local factor `Q(p^α)`. -/
def Qlocal (α : ℕ) : ℕ := 3 * α / 2 + 1

@[simp] theorem Qlocal_zero : Qlocal 0 = 1 := rfl
@[simp] theorem Qlocal_one : Qlocal 1 = 2 := rfl
@[simp] theorem Qlocal_two : Qlocal 2 = 4 := rfl
@[simp] theorem Qlocal_three : Qlocal 3 = 5 := rfl

/-- **D7, local form.** The coefficient recurrence equivalent to
`Σ_α Qlocal α · xᵅ = (1-x³)/((1-x)²(1-x²))`, namely
`aₙ - 2aₙ₋₁ + 2aₙ₋₃ - aₙ₋₄ = 0` for `n ≥ 4`, written without subtraction. -/
theorem Qlocal_rec (α : ℕ) :
    Qlocal (α + 4) + 2 * Qlocal (α + 1) = 2 * Qlocal (α + 3) + Qlocal α := by
  unfold Qlocal
  omega

/-- The closed form of the partial sums appearing in the Euler factor:
`Qlocal` is `⌊3α/2⌋+1`, so consecutive values differ by `1` and `2` alternately. -/
theorem Qlocal_succ (α : ℕ) :
    Qlocal (α + 2) = Qlocal α + 3 := by
  unfold Qlocal
  omega

end VicoEnum
