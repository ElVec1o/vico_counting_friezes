/-
  VicoEnum/Width6Reduced.lean

  The width-six reduced form.

  At width five the numerator conditions collapse to Ford's equation in the three
  variables `(g, U, V)` with `gUV = N²(U+V) + M`. This file carries the same
  reduction to width six. Writing

      A = pq - N²,   B = qr - N²,   g = gcd(A,B),   U = A/g,   V = B/g,   R = q,

  the defining relation `pqr = N²(e+p+r)` is equivalent to the single master
  identity

      A · B = N⁴ + N² q e,        that is        g²UV = N⁴ + N² R e,

  which is again of Ford type. The remaining conditions become divisibilities in
  `(g, U, V, R)` alone, and `R` ranges over the divisors of `gcd(gU+N², gV+N²)`
  rather than over an index set attached to `N`.
-/
import VicoEnum.Count6

namespace VicoEnum

/-- **The width-six master identity.** With `A = pq - N²` and `B = qr - N²` written
additively, the defining relation `pqr = N²(e+p+r)` gives `AB = N⁴ + N²qe`. -/
theorem width6_master {N p q r e A B : ℕ}
    (hA : A + N ^ 2 = p * q) (hB : B + N ^ 2 = q * r)
    (hkey : p * q * r = N ^ 2 * (e + p + r)) :
    A * B = N ^ 4 + N ^ 2 * q * e := by
  have hAZ : (A : ℤ) + (N : ℤ) ^ 2 = (p : ℤ) * (q : ℤ) := by exact_mod_cast hA
  have hBZ : (B : ℤ) + (N : ℤ) ^ 2 = (q : ℤ) * (r : ℤ) := by exact_mod_cast hB
  have hkZ : (p : ℤ) * (q : ℤ) * (r : ℤ)
      = (N : ℤ) ^ 2 * ((e : ℤ) + (p : ℤ) + (r : ℤ)) := by exact_mod_cast hkey
  have hZ : (A : ℤ) * (B : ℤ) = (N : ℤ) ^ 4 + (N : ℤ) ^ 2 * (q : ℤ) * (e : ℤ) := by
    have h4 : ((A : ℤ) + (N : ℤ) ^ 2) * ((B : ℤ) + (N : ℤ) ^ 2)
        = (N : ℤ) ^ 2 * (q : ℤ) * ((e : ℤ) + (p : ℤ) + (r : ℤ)) := by
      rw [hAZ, hBZ]; linear_combination (q : ℤ) * hkZ
    linear_combination h4 - (N : ℤ) ^ 2 * hAZ - (N : ℤ) ^ 2 * hBZ
  exact_mod_cast hZ

/-- The reduced width-six system in the variables `(g, U, V, R)`, with `p`, `r` and `e`
recovered by `pR = gU + N²`, `rR = gV + N²` and `g²UV = N⁴ + N²Re`.

The two conditions `N ∣ gU` and `N ∣ gV` are the lattice condition on the row below the
quiddity: that entry equals `(pq - N²)/N² = A/N²`, which lies in `(1/N)ℤ` exactly when
`N ∣ A`. They are what the three `W6` divisibilities alone do not supply. -/
def Red6 (N g U V R e p r : ℕ) : Prop :=
  0 < g ∧ 0 < U ∧ 0 < V ∧ 0 < R ∧ 0 < e ∧ 0 < p ∧ 0 < r ∧
    Nat.gcd U V = 1 ∧
    N ∣ g * U ∧ N ∣ g * V ∧
    p * R = g * U + N ^ 2 ∧ r * R = g * V + N ^ 2 ∧
    g ^ 2 * U * V = N ^ 4 + N ^ 2 * R * e ∧
    e ∣ g * U + N ^ 2 ∧ e ∣ g * V + N ^ 2 ∧
    e * R ∣ N * (g * (U + V) + 2 * N ^ 2)

/-- **Sufficiency.** Every solution of the reduced system is a width-six solution:
`Red6` implies `W6` on the recovered numerators, with `q = R`. -/
theorem W6_of_red6 {N g U V R e p r : ℕ} (h : Red6 N g U V R e p r) :
    W6 N p R r e := by
  obtain ⟨hg, hU, hV, hR, he, hp, hr, _, _, _, hpR, hrR, hkey, hepq, heqr, hedvd⟩ := h
  have h1 : (p : ℤ) * R = (g : ℤ) * U + (N : ℤ) ^ 2 := by exact_mod_cast hpR
  have h2 : (r : ℤ) * R = (g : ℤ) * V + (N : ℤ) ^ 2 := by exact_mod_cast hrR
  have hk : (g : ℤ) ^ 2 * U * V = (N : ℤ) ^ 4 + (N : ℤ) ^ 2 * R * e := by exact_mod_cast hkey
  have hEq : N * (g * (U + V) + 2 * N ^ 2) = (N * (p + r)) * R := by
    have : (N : ℤ) * ((g : ℤ) * ((U : ℤ) + V) + 2 * (N : ℤ) ^ 2)
        = ((N : ℤ) * ((p : ℤ) + r)) * R := by
      linear_combination (-(N : ℤ)) * h1 - (N : ℤ) * h2
    exact_mod_cast this
  refine ⟨hp, hR, hr, he, ?_, ?_, ?_, ?_⟩
  · have hmul : (p * R * r) * R = (N ^ 2 * (e + p + r)) * R := by
      have : ((p : ℤ) * R * r) * R = ((N : ℤ) ^ 2 * ((e : ℤ) + p + r)) * R := by
        linear_combination ((r : ℤ) * R) * h1 + ((g : ℤ) * U + (N : ℤ) ^ 2) * h2
          + hk - (N : ℤ) ^ 2 * h1 - (N : ℤ) ^ 2 * h2
      exact_mod_cast this
    exact Nat.eq_of_mul_eq_mul_right hR hmul
  · rw [hpR]; exact hepq
  · rw [mul_comm R r, hrR]; exact heqr
  · rw [hEq] at hedvd
    obtain ⟨c, hc⟩ := hedvd
    refine ⟨c, Nat.eq_of_mul_eq_mul_right hR ?_⟩
    calc N * (p + r) * R = e * R * c := hc
      _ = e * c * R := by ring

/-- **Necessity.** A width-six solution whose row below the quiddity is integral produces a
solution of the reduced system, with `g = gcd(A,B)`, `U = A/g`, `V = B/g` and `R = q`. -/
theorem red6_of_W6 {N p q r e A B : ℕ}
    (hA : A + N ^ 2 = p * q) (hB : B + N ^ 2 = q * r) (hA0 : 0 < A) (hB0 : 0 < B)
    (hNA : N ∣ A) (hNB : N ∣ B) (h : W6 N p q r e) :
    Red6 N (Nat.gcd A B) (A / Nat.gcd A B) (B / Nat.gcd A B) q e p r := by
  obtain ⟨hp, hq, hr, he, hkey, hepq, heqr, hedvd⟩ := h
  set g := Nat.gcd A B with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hA0
  have hUA : g * (A / g) = A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
  have hVB : g * (B / g) = B := Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)
  refine ⟨hgpos, Nat.div_pos (Nat.le_of_dvd hA0 (Nat.gcd_dvd_left A B)) hgpos,
    Nat.div_pos (Nat.le_of_dvd hB0 (Nat.gcd_dvd_right A B)) hgpos, hq, he, hp, hr,
    Nat.coprime_div_gcd_div_gcd hgpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hUA]; exact hNA
  · rw [hVB]; exact hNB
  · rw [hUA]; exact hA.symm
  · rw [hVB, hB]; ring
  · have hexp : g ^ 2 * (A / g) * (B / g) = (g * (A / g)) * (g * (B / g)) := by ring
    rw [hexp, hUA, hVB]
    exact width6_master hA hB hkey
  · rw [hUA, hA]; exact hepq
  · rw [hVB, hB]; exact heqr
  · have hsum : g * (A / g + B / g) = A + B := by rw [Nat.mul_add, hUA, hVB]
    have hEq : N * (g * (A / g + B / g) + 2 * N ^ 2) = (N * (p + r)) * q := by
      rw [hsum]
      have : A + B + 2 * N ^ 2 = p * q + q * r := by rw [← hA, ← hB]; ring
      rw [show N * (A + B + 2 * N ^ 2) = N * (A + B + 2 * N ^ 2) from rfl, this]; ring
    rw [hEq]
    exact mul_dvd_mul_right hedvd q

end VicoEnum
