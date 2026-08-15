/-
  VicoEnum/W5Converse.lean

  The converse of Proposition `prop:w5cond`: a `W5` pair gives a positive frieze over the
  lattice.

  `width5_build` supplies the frieze over `ℚ`. Two things remain, and both are conditions on
  the five quiddity entries alone, because rows `1` and `4` are constant `1` and row `3` is a
  permutation of the quiddity:

      row 3 at columns 0..4  =  D, a₄, a₀, a₁, a₂.

  That identity is `quid5fn_row3` below, and it is what makes both remaining conditions
  finite checks.

  * Positivity. `D > 0` is `N² < pq`, and the other four entries are quotients of positive
    quantities by `D`.
  * Lattice. `N·D = (pq-N²)/N` is integral because `N ∣ pq`; `N·a₂ = N²(p+N)/(pq-N²)` and
    `N·a₄ = N²(q+N)/(pq-N²)` are integral because of the two divisibilities. These are
    exactly the three arithmetic clauses of `W5` beyond positivity. The reverse implication,
    that a lattice frieze gives a `W5` pair, is `W5_of_frieze` and is not proved here.
-/
import VicoEnum.Width5Build

namespace VicoEnum

open Finset

/-! ## Row three is a permutation of the quiddity -/

/-- Row `3` of the generated array, at each of the five columns. -/
theorem quid5fn_row3 {a0 a1 : ℚ} (hD : a0 * a1 - 1 ≠ 0) (j : ℤ) :
    Kc (quid5fn a0 a1) j 2 = quid5fn a0 a1 (j + 3) := by
  rw [Kc_two]
  rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4)
    with h | h | h | h | h
  · rw [q0 a0 a1 j h, q1 a0 a1 (j+1) (by omega), q3 a0 a1 (j+3) (by omega)]; ring
  · rw [q1 a0 a1 j h, q2 a0 a1 (j+1) (by omega), q4 a0 a1 (j+3) (by omega)]
    field_simp; all_goals ring
  · rw [q2 a0 a1 j h, q3 a0 a1 (j+1) (by omega), q0 a0 a1 (j+3) (by omega)]
    field_simp; all_goals ring
  · rw [q3 a0 a1 j h, q4 a0 a1 (j+1) (by omega), q1 a0 a1 (j+3) (by omega)]
    field_simp; all_goals ring
  · rw [q4 a0 a1 j h, q0 a0 a1 (j+1) (by omega), q2 a0 a1 (j+3) (by omega)]
    field_simp; all_goals ring

/-! ## Positivity -/

/-- Every quiddity entry is positive when `a₀`, `a₁` and `D` are. -/
theorem quid5fn_pos {a0 a1 : ℚ} (h0 : 0 < a0) (h1 : 0 < a1) (hD : 0 < a0 * a1 - 1) (j : ℤ) :
    0 < quid5fn a0 a1 j := by
  rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4)
    with h | h | h | h | h
  · rw [q0 a0 a1 j h]; exact h0
  · rw [q1 a0 a1 j h]; exact h1
  · rw [q2 a0 a1 j h]; positivity
  · rw [q3 a0 a1 j h]; exact hD
  · rw [q4 a0 a1 j h]; positivity

/-- **The generated array is positive.** Rows `1` and `4` are constant `1`, row `2` is the
quiddity and row `3` is the permutation of it given by `quid5fn_row3`. -/
theorem width5_build_pos {a0 a1 : ℚ} (h0 : 0 < a0) (h1 : 0 < a1) (hD : 0 < a0 * a1 - 1) :
    ∀ r j, 0 < r → r < 5 → 0 < friezeOf (quid5fn a0 a1) r j := by
  intro r j hr0 hr5
  rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with rfl | rfl | rfl | rfl
  · exact zero_lt_one
  · exact quid5fn_pos h0 h1 hD j
  · show (0 : ℚ) < Kc (quid5fn a0 a1) j 2
    rw [quid5fn_row3 hD.ne' j]
    exact quid5fn_pos h0 h1 hD (j + 3)
  · show (0 : ℚ) < Kc (quid5fn a0 a1) j 3
    rw [quid5fn_three hD.ne' j]
    exact zero_lt_one

/-- **The construction, positive.** -/
theorem width5_build_positive {a0 a1 : ℚ} (h0 : 0 < a0) (h1 : 0 < a1)
    (hD : 0 < a0 * a1 - 1) : IsPositiveFrieze 5 (friezeOf (quid5fn a0 a1)) :=
  ⟨width5_build hD.ne', width5_build_pos h0 h1 hD⟩

/-! ## The lattice condition -/

/-- **Every entry of rows `0` to `5` lies in the lattice**, given that the five quiddity
entries do. Rows `1` and `4` are `1 = N/N`, row `3` is a permutation of the quiddity, and
rows `0` and `5` vanish. -/
theorem width5_build_lattice {N : ℕ} (hN : 0 < N) {a0 a1 : ℚ} (hD : a0 * a1 - 1 ≠ 0)
    (hq : ∀ j : ℤ, InLattice N (quid5fn a0 a1 j)) :
    ∀ r j, r ≤ 5 → InLattice N (friezeOf (quid5fn a0 a1) r j) := by
  intro r j hr
  have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hone : InLattice N (1 : ℚ) := ⟨(N : ℤ), by push_cast; field_simp⟩
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5)
    with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact hone
  · exact hq j
  · show InLattice N (Kc (quid5fn a0 a1) j 2)
    rw [quid5fn_row3 hD j]; exact hq (j + 3)
  · show InLattice N (Kc (quid5fn a0 a1) j 3)
    rw [quid5fn_three hD j]; exact hone
  · show InLattice N (Kc (quid5fn a0 a1) j 4)
    rw [quid5fn_four hD j]; exact ⟨0, by simp⟩

/-! ## The quiddity of a `W5` pair lies in the lattice

This is the last step, and it is where the three arithmetic clauses of `W5` are consumed.
Writing `pq = N² + Ne`, which is `N ∣ pq`, the entries are

    a₀ = p/N,   a₁ = q/N,   D = e/N,   a₂ = c/N,   a₄ = c'/N,

with `N(p+N) = ec` and `N(q+N) = ec'`, the two divisibilities of `W5` after cancelling one
factor of `N`. So `W5` says exactly that this array lies in the lattice. -/

theorem quid5fn_lattice {N p q : ℕ} (hN : 0 < N) (h : W5 N p q) :
    ∀ j : ℤ, InLattice N (quid5fn ((p : ℚ) / N) ((q : ℚ) / N) j) := by
  obtain ⟨hp, hq, hlt, hdvd, hdp, hdq⟩ := h
  have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  -- pq = N² + Ne
  obtain ⟨e, hpq⟩ : ∃ e, p * q = N ^ 2 + N * e := by
    obtain ⟨c, hc⟩ := hdvd
    have hcN : N ≤ c := by nlinarith [hN, hlt, hc]
    obtain ⟨d, rfl⟩ : ∃ d, c = N + d := ⟨c - N, by omega⟩
    have hx : N * (N + d) = N * N + N * d := by ring
    exact ⟨d, by have : N ^ 2 = N * N := sq N; omega⟩
  have hesub : p * q - N ^ 2 = N * e := by omega
  have hepos : 0 < e := by nlinarith [hlt, hpq, hN]
  rw [hesub] at hdp hdq
  -- N(p+N) = e c  and  N(q+N) = e c'
  obtain ⟨c, hc⟩ : ∃ c, N * (p + N) = e * c := by
    obtain ⟨c, hc⟩ := hdp
    refine ⟨c, ?_⟩
    have : N * (N * (p + N)) = N * (e * c) := by
      calc N * (N * (p + N)) = N ^ 2 * (p + N) := by ring
        _ = N * e * c := hc
        _ = N * (e * c) := by ring
    exact Nat.eq_of_mul_eq_mul_left hN this
  obtain ⟨c', hc'⟩ : ∃ c', N * (q + N) = e * c' := by
    obtain ⟨d, hd⟩ := hdq
    refine ⟨d, ?_⟩
    have : N * (N * (q + N)) = N * (e * d) := by
      calc N * (N * (q + N)) = N ^ 2 * (q + N) := by ring
        _ = N * e * d := hd
        _ = N * (e * d) := by ring
    exact Nat.eq_of_mul_eq_mul_left hN this
  -- the rational identities
  have hDQ : ((p : ℚ) / N) * ((q : ℚ) / N) - 1 = (e : ℚ) / N := by
    have hpqQ : ((p : ℚ)) * q = (N : ℚ) ^ 2 + N * e := by exact_mod_cast hpq
    rw [div_mul_div_comm, hpqQ]
    field_simp
    all_goals ring
  have heQ : ((e : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hepos.ne'
  intro j
  rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4)
    with hj | hj | hj | hj | hj
  · rw [q0 _ _ j hj]; exact ⟨(p : ℤ), by push_cast; ring⟩
  · rw [q1 _ _ j hj]; exact ⟨(q : ℤ), by push_cast; ring⟩
  · rw [q2 _ _ j hj, hDQ]
    refine ⟨(c : ℤ), ?_⟩
    have hcQ : ((N : ℚ)) * (p + N) = e * c := by exact_mod_cast hc
    field_simp
    push_cast
    linarith [hcQ]
  · rw [q3 _ _ j hj, hDQ]; exact ⟨(e : ℤ), by push_cast; ring⟩
  · rw [q4 _ _ j hj, hDQ]
    refine ⟨(c' : ℤ), ?_⟩
    have hcQ : ((N : ℚ)) * (q + N) = e * c' := by exact_mod_cast hc'
    field_simp
    push_cast
    linarith [hcQ]

/-- **The converse of Proposition `prop:w5cond`.** A `W5` pair generates a positive width-5
frieze all of whose entries lie in `(1/N)ℤ`. -/
theorem w5cond_converse {N p q : ℕ} (hN : 0 < N) (h : W5 N p q) :
    IsPositiveFrieze 5 (friezeOf (quid5fn ((p : ℚ) / N) ((q : ℚ) / N))) ∧
      (∀ r j, r ≤ 5 → InLattice N (friezeOf (quid5fn ((p : ℚ) / N) ((q : ℚ) / N)) r j)) ∧
      quiddity (friezeOf (quid5fn ((p : ℚ) / N) ((q : ℚ) / N))) 0 = (p : ℚ) / N ∧
      quiddity (friezeOf (quid5fn ((p : ℚ) / N) ((q : ℚ) / N))) 1 = (q : ℚ) / N := by
  have hp := h.1
  have hq := h.2.1
  have hlt := h.2.2.1
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have h0 : (0 : ℚ) < (p : ℚ) / N := by positivity
  have h1 : (0 : ℚ) < (q : ℚ) / N := by positivity
  have hD : (0 : ℚ) < ((p : ℚ) / N) * ((q : ℚ) / N) - 1 := by
    have hc : ((N : ℚ)) ^ 2 < (p : ℚ) * q := by exact_mod_cast hlt
    rw [div_mul_div_comm, lt_sub_iff_add_lt, zero_add, lt_div_iff (by positivity)]
    nlinarith [hc]
  exact ⟨width5_build_positive h0 h1 hD,
    width5_build_lattice hN hD.ne' (quid5fn_lattice hN h),
    (by show quid5fn ((p : ℚ) / N) ((q : ℚ) / N) 0 = (p : ℚ) / N
        exact q0 _ _ 0 (by norm_num)),
    (by show quid5fn ((p : ℚ) / N) ((q : ℚ) / N) 1 = (q : ℚ) / N
        exact q1 _ _ 1 (by norm_num))⟩

end VicoEnum
