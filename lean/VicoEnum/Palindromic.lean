/-
  VicoEnum/Palindromic.lean

  D3  the width-6 search bound `pq ≤ 2N²(N+1)`
  D5  the palindromic width-5 family `(t(t+2), 1/t, t+1, t+1, 1/t)`
  D6  the criterion `k² ∣ N³` governing which members lie in `(1/N)ℤ`
-/
import VicoEnum.Basic

namespace VicoEnum

/-! ## D3: the width-6 search bound -/

/-- **D3.** With `p ≤ r`, `e ≥ 1`, `e ∣ N(p+r)` and `pqr = N²(e+p+r)`, the product
`pq` is bounded by `2N²(N+1)`. -/
theorem width6_bound {N p q r e : ℤ} (hN : 0 < N) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (he : 0 < e) (hpr : p ≤ r)
    (hdvd : e ∣ N * (p + r)) (hkey : p * q * r = N ^ 2 * (e + p + r)) :
    p * q ≤ 2 * N ^ 2 * (N + 1) := by
  have hple : e ≤ N * (p + r) := Int.le_of_dvd (by positivity) hdvd
  -- p q r = N²(e + p + r) ≤ N²(N+1)(p+r) ≤ 2 N²(N+1) r
  have hNsq : (0 : ℤ) ≤ N ^ 2 := sq_nonneg N
  have hstep : N ^ 2 * e ≤ N ^ 2 * (N * (p + r)) := mul_le_mul_of_nonneg_left hple hNsq
  have h1 : p * q * r ≤ N ^ 2 * (N + 1) * (p + r) := by rw [hkey]; nlinarith [hstep]
  have hc : (0 : ℤ) ≤ N ^ 2 * (N + 1) := by positivity
  have h3 : p * q * r ≤ 2 * N ^ 2 * (N + 1) * r := by nlinarith [h1, hpr, hc]
  have h4 : (p * q) * r ≤ (2 * N ^ 2 * (N + 1)) * r := by linarith [h3]
  exact le_of_mul_le_mul_right h4 hr

/-- **The width-6 case of the uniform bound.** Since `q ≥ 1`, the product bound of
`width6_bound` bounds the first parameter itself by `2N³ + 2N²`, which is
`(n-4)N³ + 2N²` at `n = 6`. -/
theorem width6_bound_entry {N p q r e : ℤ} (hN : 0 < N) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (he : 0 < e) (hpr : p ≤ r)
    (hdvd : e ∣ N * (p + r)) (hkey : p * q * r = N ^ 2 * (e + p + r)) :
    p ≤ 2 * N ^ 3 + 2 * N ^ 2 := by
  have h := width6_bound hN hp hq hr he hpr hdvd hkey
  have : p ≤ p * q := le_mul_of_one_le_right hp.le hq
  nlinarith [h, this]

/-! ## D5: the palindromic width-5 family

A positive width-5 frieze is determined by `a₀, a₁` through
`a₂ = (a₀+1)/D`, `a₃ = D`, `a₄ = (a₁+1)/D` with `D = a₀a₁ - 1`.
-/

/-- The data determining a positive rational width-5 frieze. -/
structure Frieze5 where
  a0 : ℚ
  a1 : ℚ
  pos0 : 0 < a0
  pos1 : 0 < a1
  posD : 0 < a0 * a1 - 1

namespace Frieze5

/-- The middle quiddity entry `a₃ = D`. -/
def D (f : Frieze5) : ℚ := f.a0 * f.a1 - 1

def a2 (f : Frieze5) : ℚ := (f.a0 + 1) / f.D
def a3 (f : Frieze5) : ℚ := f.D
def a4 (f : Frieze5) : ℚ := (f.a1 + 1) / f.D

lemma D_ne_zero (f : Frieze5) : f.D ≠ 0 := f.posD.ne'

end Frieze5

/-- **D5.** The width-5 cycles fixed by the reflection through index `0` (that is,
`a₁ = a₄`) are exactly those of the form `a₀ = t(t+2)`, `a₁ = 1/t` for rational
`t > 0`. The remaining palindromic condition `a₂ = a₃` is then automatic. -/
theorem palindromic_iff (f : Frieze5) :
    f.a1 = f.a4 ↔ ∃ t : ℚ, 0 < t ∧ f.a0 = t * (t + 2) ∧ f.a1 = 1 / t := by
  have hD := f.D_ne_zero
  constructor
  · intro h
    refine ⟨1 / f.a1, one_div_pos.mpr f.pos1, ?_, by field_simp⟩
    -- a₁ = (a₁+1)/D gives D = (a₁+1)/a₁, hence a₀ = 2/a₁ + 1/a₁²
    have h1 : f.a1 * f.D = f.a1 + 1 := by
      have := h
      rw [Frieze5.a4] at this
      field_simp at this
      linarith [this]
    have ha1 : f.a1 ≠ 0 := f.pos1.ne'
    have h2 : f.a0 * f.a1 ^ 2 = 2 * f.a1 + 1 := by
      have : f.a1 * (f.a0 * f.a1 - 1) = f.a1 + 1 := by rw [← Frieze5.D]; exact h1
      nlinarith [this]
    field_simp
    nlinarith [h2, ha1, f.pos1]
  · rintro ⟨t, ht, h0, h1⟩
    have htne : t ≠ 0 := ht.ne'
    have hDt : f.D = t + 1 := by
      rw [Frieze5.D, h0, h1]; field_simp; ring
    rw [Frieze5.a4, hDt, h1]
    field_simp
    ring

/-- With `a₁ = a₄`, the second palindromic condition `a₂ = a₃` holds automatically. -/
theorem palindromic_a2_eq_a3 (f : Frieze5) (h : f.a1 = f.a4) : f.a2 = f.a3 := by
  obtain ⟨t, ht, h0, h1⟩ := (palindromic_iff f).mp h
  have htne : t ≠ 0 := ht.ne'
  have hDt : f.D = t + 1 := by rw [Frieze5.D, h0, h1]; field_simp; ring
  have hne : t + 1 ≠ 0 := by positivity
  rw [Frieze5.a2, Frieze5.a3, hDt, h0]
  field_simp
  ring

/-! ## D6: the arithmetic criterion `k² ∣ N³`

For `t = N/k` the three lattice conditions on `(t(t+2), 1/t, t+1)` are
`k ∣ N²` and `k² ∣ N²(N+2k)`, and together they collapse to the single
condition `k² ∣ N³`.
-/

/-- If `k² ∣ N³` then `k ∣ N²`. Locally `2β ≤ 3α ≤ 4α` gives `β ≤ 2α`. -/
theorem dvd_sq_of_sq_dvd_cube {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (h : k ^ 2 ∣ N ^ 3) : k ∣ N ^ 2 := by
  have hk0 : k ≠ 0 := hk.ne'
  have hN0 : N ≠ 0 := hN.ne'
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hk0) (pow_ne_zero 3 hN0)] at h
  rw [← Nat.factorization_le_iff_dvd hk0 (pow_ne_zero 2 hN0), Finsupp.le_def]
  intro p
  have hp := Finsupp.le_def.mp h p
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hp ⊢
  omega

/-- **D6, arithmetic core.** The two lattice conditions collapse to `k² ∣ N³`. -/
theorem lattice_criterion {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    (k ∣ N ^ 2 ∧ k ^ 2 ∣ N ^ 2 * (N + 2 * k)) ↔ k ^ 2 ∣ N ^ 3 := by
  have hexp : N ^ 2 * (N + 2 * k) = N ^ 3 + 2 * N ^ 2 * k := by ring
  constructor
  · rintro ⟨h1, h2⟩
    -- k ∣ N² gives k² ∣ 2N²k, so k² ∣ N³
    obtain ⟨c, hc⟩ := h1
    have hk2 : k ^ 2 ∣ 2 * N ^ 2 * k := ⟨2 * c, by rw [hc]; ring⟩
    rw [hexp] at h2
    simpa using Nat.dvd_sub' h2 hk2
  · intro h
    refine ⟨dvd_sq_of_sq_dvd_cube hk hN h, ?_⟩
    obtain ⟨c, hc⟩ := dvd_sq_of_sq_dvd_cube hk hN h
    obtain ⟨e, he⟩ := h
    rw [hexp]
    exact ⟨e + 2 * c, by rw [he, hc]; ring⟩

/-! ## W7: the width-7 bound on the fourth parameter

With `a_i = p_i/N`, the continuants are `K_2 = u/N²`, `K_3 = G/N³`, `K_4 = E/N⁴`
where `u = p₀p₁ - N²`, `G = p₂u - p₀N²`, `E = p₃G - N²u`. Positivity of frieze rows
3 and 4 makes `u` and `G` positive integers, and `a₅ = E/N⁴` lying in `(1/N)ℤ` gives
`E = eN³`. The lattice condition on `a₄ = (G+N³)/(eN²)` is `eN ∣ G+N³`, and that
bounds `p₃`.
-/

/-- **W7.** The width-7 fourth parameter is bounded by `N²(N³ + u + 1)`, where
`u = p₀p₁ - N²`. Same mechanism as `width5_bound` and `width6_bound`: a positive
divisor is at most what it divides, and integrality of `G` finishes it. -/
theorem width7_bound_p3 {N p3 u G e : ℤ} (hN : 0 < N)
    (hupos : 0 < u) (hGpos : 0 < G) (he : 0 < e)
    (hE : e * N ^ 3 = p3 * G - N ^ 2 * u)
    (hdvd : (e * N) ∣ (G + N ^ 3)) :
    p3 ≤ N ^ 2 * (N ^ 3 + u + 1) := by
  have hpos : 0 < G + N ^ 3 := by positivity
  have h1 : e * N ≤ G + N ^ 3 := Int.le_of_dvd hpos hdvd
  have hNsq : (0 : ℤ) ≤ N ^ 2 := sq_nonneg N
  -- multiply by N² and substitute eN³ = p₃G - N²u
  have h2 : e * N ^ 3 ≤ N ^ 2 * (G + N ^ 3) := by nlinarith [h1, hNsq]
  have h3 : G * (p3 - N ^ 2) ≤ N ^ 2 * (u + N ^ 3) := by nlinarith [h2, hE]
  have hN3 : (0 : ℤ) < N ^ 3 := pow_pos hN 3
  rcases le_or_lt p3 (N ^ 2) with hle | hgt
  · have hone : (1 : ℤ) ≤ N ^ 3 + u + 1 := by linarith
    have := mul_le_mul_of_nonneg_left hone hNsq
    linarith [hle, this]
  · have h4 : 0 < p3 - N ^ 2 := by omega
    have h5 : p3 - N ^ 2 ≤ G * (p3 - N ^ 2) := le_mul_of_one_le_left h4.le hGpos
    nlinarith [h3, h5]

/-- **The value of the fixed middle entries.** For a cycle fixed by the reflection, the two
middle quiddity entries are both `t + 1`. Theorem `thm:family` states this alongside
`a₀ = t(t+2)` and `a₁ = 1/t`; `palindromic_iff` gives the latter two, this gives the first. -/
theorem palindromic_a2_value (f : Frieze5) (h : f.a1 = f.a4) :
    ∃ t : ℚ, 0 < t ∧ f.a0 = t * (t + 2) ∧ f.a1 = 1 / t ∧ f.a2 = t + 1 ∧ f.a3 = t + 1 := by
  obtain ⟨t, ht, h0, h1⟩ := (palindromic_iff f).mp h
  have hDt : f.D = t + 1 := by rw [Frieze5.D, h0, h1]; field_simp; ring
  refine ⟨t, ht, h0, h1, ?_, ?_⟩
  · rw [Frieze5.a2, hDt, h0]
    field_simp
    ring
  · rw [Frieze5.a3, hDt]

/-- **Lemma `lem:w6bound`, the formula for `r`.** The relation `pqr = N²(e+p+r)` solved for
`r`. Stated multiplicatively, so no division and no hypothesis that `pq ≠ N²`. -/
theorem width6_r_formula {N p q r e : ℤ} (hkey : p * q * r = N ^ 2 * (e + p + r)) :
    r * (p * q - N ^ 2) = N ^ 2 * (e + p) := by linear_combination hkey

end VicoEnum
