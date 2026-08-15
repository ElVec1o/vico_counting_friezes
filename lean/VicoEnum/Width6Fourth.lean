/-
  VicoEnum/Width6Fourth.lean

  The fourth divisibility of `W6`, from the definition.

  `width6_from_frieze` derives the defining relation of `W6` and two of its three
  divisibilities from `IsFrieze 6` alone. The third, `e ∣ N(p+r)`, is stated there to need "a
  lattice condition on a row other than the quiddity", and that is exactly right: the two it
  does derive read off row `2`, and this one reads off row `3`.

  The proof of Lemma `lem:w6bound` says the row-3 entry equals `(p+r)/e`. Here that entry is
  `m 3 2`, which `entry_eq_continuant` makes `a_3 a_2 - 1`. Proposition `prop:param` at width
  `6` gives `a_3 a_4 = a_0 a_1`, so `c_3 e = pq` in numerators, and `a_4 = a_2(a_1a_0-1)-a_0`
  gives `pqr = N^2(e+p+r)`. Together

      e (c_3 r - N^2) = pqr - eN^2 = N^2(p+r),

  so `m 3 2 = (c_3 r - N^2)/N^2 = (p+r)/e`. Membership of that single entry in `(1/N)ℤ` is
  then precisely `e ∣ N(p+r)`.

  Note what is *not* claimed. `code/w6_fourth.py` shows the first three `W6` conditions do not
  imply the fourth, so this divisibility is genuinely extra information and could not have
  come from the quiddity alone.
-/
import VicoEnum.Frieze
import VicoEnum.Count6

namespace VicoEnum

/-- **The fourth `W6` divisibility.** A positive width-6 frieze whose quiddity numerators are
`p, q, r, c₃, e` and whose row-3 entry at column `2` lies in `(1/N)ℤ` satisfies
`e ∣ N(p+r)`. -/
theorem width6_fourth {N : ℕ} (hN : 0 < N) {m : ℕ → ℤ → ℚ} (hm : IsFrieze 6 m)
    (hpos : ∀ r j, 0 < r → r < 6 → 0 < m r j) {p q r c₃ e : ℕ}
    (h0 : (N : ℚ) * quiddity m 0 = p) (h1 : (N : ℚ) * quiddity m 1 = q)
    (h2 : (N : ℚ) * quiddity m 2 = r) (h3 : (N : ℚ) * quiddity m 3 = c₃)
    (h4 : (N : ℚ) * quiddity m 4 = e)
    (hlat : InLattice N (m 3 2)) :
    e ∣ N * (p + r) := by
  have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨eA, eB, -⟩ := param_formulas (p := 1) (by simpa using hm) (by simpa using hpos)
  set a := quiddity m with ha
  norm_num at eA eB
  have hK2 : Kc a 0 2 = a 1 * a 0 - 1 := by rw [Kc_succ_succ a 0 0]; norm_num
  have hK3 : Kc a 0 3 = a 2 * (a 1 * a 0 - 1) - a 0 := by
    rw [Kc_succ_succ a 0 1, hK2]; norm_num
  rw [hK3] at eA eB
  rw [hK2] at eB
  -- `a₃ a₄ = a₀ a₁`, hence `c₃ e = pq`
  have hprod : a 3 * a 4 = a 0 * a 1 := by rw [eA]; linarith [eB]
  have hc3e : (c₃ : ℚ) * e = (p : ℚ) * q := by
    rw [← h3, ← h4, ← h0, ← h1]
    calc (N : ℚ) * a 3 * ((N : ℚ) * a 4) = (N : ℚ) ^ 2 * (a 3 * a 4) := by ring
      _ = (N : ℚ) ^ 2 * (a 0 * a 1) := by rw [hprod]
      _ = (N : ℚ) * a 0 * ((N : ℚ) * a 1) := by ring
  -- the defining relation `pqr = N²(e+p+r)`
  have hkey : (p : ℚ) * q * r = (N : ℚ) ^ 2 * ((e : ℚ) + p + r) := by
    rw [← h0, ← h1, ← h2, ← h4, eA]; ring
  -- the row-3 entry
  have hentry : m 3 2 = a 3 * a 2 - 1 := by
    have := entry_eq_continuant hm hpos 3 (by omega) (by omega) 2
    rw [this, Kc_succ_succ a 2 0]; norm_num
  -- it lies in the lattice, so `c₃ r - N² = kN`
  obtain ⟨k, hk⟩ := hlat
  have hcr : (c₃ : ℚ) * r - (N : ℚ) ^ 2 = (k : ℚ) * N := by
    have h32 : (N : ℚ) ^ 2 * (a 3 * a 2 - 1) = (c₃ : ℚ) * r - (N : ℚ) ^ 2 := by
      rw [← h3, ← h2]; ring
    rw [hentry] at hk
    rw [← h32, hk]
    field_simp
    ring
  -- and `e (c₃ r - N²) = N²(p+r)`
  have hfin : (e : ℚ) * ((k : ℚ) * N) = (N : ℚ) ^ 2 * ((p : ℚ) + r) := by
    rw [← hcr]
    have : (e : ℚ) * ((c₃ : ℚ) * r) = (p : ℚ) * q * r := by
      calc (e : ℚ) * ((c₃ : ℚ) * r) = ((c₃ : ℚ) * e) * r := by ring
        _ = ((p : ℚ) * q) * r := by rw [hc3e]
        _ = (p : ℚ) * q * r := by ring
    rw [mul_sub, this, hkey]; ring
  -- cancel one `N` and descend to `ℤ`
  have hZ : (e : ℤ) * k = (N : ℤ) * ((p : ℤ) + r) := by
    have : ((e : ℚ)) * (k : ℚ) = ((N : ℚ)) * ((p : ℚ) + r) := by
      refine mul_right_cancel₀ hNQ ?_
      calc (e : ℚ) * (k : ℚ) * N = (e : ℚ) * ((k : ℚ) * N) := by ring
        _ = (N : ℚ) ^ 2 * ((p : ℚ) + r) := hfin
        _ = (N : ℚ) * ((p : ℚ) + r) * N := by ring
    exact_mod_cast this
  have : ((e : ℤ)) ∣ ((N * (p + r) : ℕ) : ℤ) := by
    refine ⟨k, ?_⟩
    push_cast
    exact_mod_cast hZ.symm
  exact_mod_cast this

end VicoEnum
