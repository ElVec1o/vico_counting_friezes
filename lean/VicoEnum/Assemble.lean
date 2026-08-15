/-
  VicoEnum/Assemble.lean

  From `W5` to `Quid5`: the rotation iterates are the quiddity numerators.

  `Cycle5` proves the rotation closes after five steps, given that the five numerators
  satisfy `Quid5`. This file supplies that: starting from a pair satisfying `W5` and
  applying the rotation step three times produces numerators satisfying `Quid5`, so the
  closure applies to the iterates themselves.

  The chain runs on one identity. Writing `e = p₀p₁ - N²` and `e₂ = p₁p₂ - N²`,

      e₂ · e = N³(p₁ + N),

  which with `p₃e₂ = N²(p₁+N)` cancels to `e = Np₃`. That is the `mid` clause; `left`
  follows by substituting it into the first step, and `right` by cancelling `p₀`.

  Verified against the parameterisation for the 820 pairs satisfying `W5` with `N < 11`
  over the full search box, with no discrepancy.
-/
import VicoEnum.Cycle5
import VicoEnum.Golden
import VicoEnum.Orbit

namespace VicoEnum

/-- The product of two consecutive rotation denominators. This needs only the first step,
not the full `W5`. -/
theorem rot_denom_prod {N p0 p1 p2 e : ℕ} (hpq : p0 * p1 = N ^ 2 + e) (hepos : 0 < e)
    (h2 : p2 * e = N ^ 2 * (p0 + N)) :
    (p1 * p2 - N ^ 2) * e = N ^ 3 * (p1 + N) := by
  have hmul : p1 * p2 * e = N ^ 2 * (N ^ 2 + e + N * p1) := by
    calc p1 * p2 * e = p1 * (p2 * e) := by ring
      _ = p1 * (N ^ 2 * (p0 + N)) := by rw [h2]
      _ = N ^ 2 * (p0 * p1) + N ^ 2 * (N * p1) := by ring
      _ = N ^ 2 * (N ^ 2 + e) + N ^ 2 * (N * p1) := by rw [hpq]
      _ = N ^ 2 * (N ^ 2 + e + N * p1) := by ring
  have hge : N ^ 2 ≤ p1 * p2 := by
    by_contra hc
    push_neg at hc
    have : p1 * p2 * e < N ^ 2 * e := by
      exact Nat.mul_lt_mul_of_lt_of_le hc (le_refl e) hepos
    rw [hmul] at this
    have hexp : N ^ 2 * (N ^ 2 + e + N * p1)
        = N ^ 2 * N ^ 2 + N ^ 2 * e + N ^ 2 * (N * p1) := by ring
    omega
  obtain ⟨g, hg⟩ : ∃ g, p1 * p2 = N ^ 2 + g := ⟨p1 * p2 - N ^ 2, by omega⟩
  have hgsub : p1 * p2 - N ^ 2 = g := by omega
  rw [hgsub]
  have h1 : (N ^ 2 + g) * e = N ^ 2 * (N ^ 2 + e + N * p1) := by rw [← hg]; exact hmul
  have h2' : (N ^ 2 + g) * e = N ^ 2 * e + g * e := by ring
  have h3 : N ^ 2 * (N ^ 2 + e + N * p1) = N ^ 2 * e + N ^ 3 * (p1 + N) := by ring
  omega

/-- **The rotation iterates satisfy `Quid5`.** Three steps out of a `W5` pair produce the
five quiddity numerators. -/
theorem quid5_of_rot {N p0 p1 p2 p3 p4 : ℕ} (hN : 0 < N) (h : W5 N p0 p1)
    (h2 : RotStep N p0 p1 p2) (h3 : RotStep N p1 p2 p3) (h4 : RotStep N p2 p3 p4) :
    Quid5 N p0 p1 p2 p3 p4 := by
  obtain ⟨hp0, hp1, hlt, -, -, -⟩ := h
  simp only [RotStep] at h2 h3 h4
  obtain ⟨e, hpq, hepos⟩ : ∃ e, p0 * p1 = N ^ 2 + e ∧ 0 < e :=
    ⟨p0 * p1 - N ^ 2, by omega, by omega⟩
  have hesub : p0 * p1 - N ^ 2 = e := by omega
  rw [hesub] at h2
  -- e₂ e = N³(p₁+N)
  have hprod := rot_denom_prod hpq hepos h2
  -- p₃ e₂ = N²(p₁+N), so p₃ N³(p₁+N) = N²(p₁+N) e, so e = N p₃
  have hmid : e = N * p3 := by
    have h1 : p3 * ((p1 * p2 - N ^ 2) * e) = (N ^ 2 * (p1 + N)) * e := by rw [← h3]; ring
    rw [hprod] at h1
    have h2' : (N ^ 2 * (p1 + N)) * (N * p3) = (N ^ 2 * (p1 + N)) * e := by
      rw [← h1]; ring
    have hpos : 0 < N ^ 2 * (p1 + N) := by positivity
    exact (Nat.eq_of_mul_eq_mul_left hpos h2').symm
  -- positivity of p₂ and p₃
  have hp2 : 0 < p2 := by
    rcases Nat.eq_zero_or_pos p2 with rfl | hc
    · exfalso; simp only [zero_mul] at h2
      have : 0 < N ^ 2 * (p0 + N) := by positivity
      omega
    · exact hc
  have hp3 : 0 < p3 := by
    rcases Nat.eq_zero_or_pos p3 with rfl | hc
    · exfalso; omega
    · exact hc
  refine ⟨hp1, hp2, hp3, by omega, ?_, ?_⟩
  · -- left : p₂p₃ = N(p₀+N)
    rw [hmid] at h2
    have h1 : N * (p2 * p3) = N * (N * (p0 + N)) := by
      calc N * (p2 * p3) = p2 * (N * p3) := by ring
        _ = N ^ 2 * (p0 + N) := h2
        _ = N * (N * (p0 + N)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hN h1
  · -- right : p₄p₃ = N(p₁+N), by cancelling p₀
    have hleft : p2 * p3 = N * (p0 + N) := by
      rw [hmid] at h2
      have h1 : N * (p2 * p3) = N * (N * (p0 + N)) := by
        calc N * (p2 * p3) = p2 * (N * p3) := by ring
          _ = N ^ 2 * (p0 + N) := h2
          _ = N * (N * (p0 + N)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hN h1
    have hden : p2 * p3 - N ^ 2 = N * p0 := by
      rw [hleft]
      have hsq : N ^ 2 = N * N := sq N
      have hexp : N * (p0 + N) = N * p0 + N * N := by ring
      omega
    rw [hden] at h4
    -- p₄ N p₀ = N²(p₂+N), so p₄p₀ = N(p₂+N)
    have hp4p0 : p4 * p0 = N * (p2 + N) := by
      have h1 : N * (p4 * p0) = N * (N * (p2 + N)) := by
        calc N * (p4 * p0) = p4 * (N * p0) := by ring
          _ = N ^ 2 * (p2 + N) := h4
          _ = N * (N * (p2 + N)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hN h1
    -- multiply by p₃ and compare
    have h1 : (p4 * p3) * p0 = (N * (p1 + N)) * p0 := by
      calc (p4 * p3) * p0 = (p4 * p0) * p3 := by ring
        _ = (N * (p2 + N)) * p3 := by rw [hp4p0]
        _ = N * (p2 * p3) + N ^ 2 * p3 := by ring
        _ = N * (N * (p0 + N)) + N ^ 2 * p3 := by rw [hleft]
        _ = N ^ 2 * (p0 + N + p3) := by ring
        _ = N * (N * p0 + (N ^ 2 + N * p3)) := by ring
        _ = N * (N * p0 + p0 * p1) := by rw [← hmid, ← hpq]
        _ = (N * (p1 + N)) * p0 := by ring
    exact Nat.eq_of_mul_eq_mul_right hp0 h1

/-! ## The rotation as a function, and its order

`RotStep` is a relation. `rotPair` realises it as a function, using that `W5` makes the
division exact, and `rotPair_five` states the conclusion: five rotations of a `W5` pair
return it. That is the order-five property `five_dvd_card_of_free` requires. -/

/-- **The third rotation returns the shifted entry.** With `e = p0 p1 - N^2`, three rotation
steps from `(p0,p1)` land on `p3` with `p3 N = e`. This is `eq:w5cyc` in the pair language:
combining `rot_denom_prod` with the step at position one and cancelling `N^2 (p1+N)` leaves
`p3 N = e`, so the rotation orbit really is the quiddity cycle. -/
theorem rot3_fst {N p0 p1 p2 p3 e : ℕ} (hN : 0 < N)
    (hpq : p0 * p1 = N ^ 2 + e) (hepos : 0 < e)
    (h2 : p2 * e = N ^ 2 * (p0 + N)) (h3 : RotStep N p1 p2 p3) :
    p3 * N = e := by
  have hden := rot_denom_prod hpq hepos h2
  -- multiply the step at position one through by `e`
  have hmul : p3 * ((p1 * p2 - N ^ 2) * e) = N ^ 2 * (p1 + N) * e := by
    have : p3 * (p1 * p2 - N ^ 2) = N ^ 2 * (p1 + N) := h3
    calc p3 * ((p1 * p2 - N ^ 2) * e) = (p3 * (p1 * p2 - N ^ 2)) * e := by ring
      _ = N ^ 2 * (p1 + N) * e := by rw [this]
  rw [hden] at hmul
  -- `p3 * N^3 * (p1+N) = N^2 * (p1+N) * e`, cancel `N^2 * (p1+N)`
  have hpos : 0 < N ^ 2 * (p1 + N) := by positivity
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc N ^ 2 * (p1 + N) * (p3 * N) = p3 * (N ^ 3 * (p1 + N)) := by ring
    _ = N ^ 2 * (p1 + N) * e := hmul

/-- The rotation on numerator pairs, as a function. -/
def rotPair (N : ℕ) (x : ℕ × ℕ) : ℕ × ℕ :=
  (x.2, N ^ 2 * (x.1 + N) / (x.1 * x.2 - N ^ 2))

/-- On a `W5` pair the division is exact, so `rotPair` realises `RotStep`. -/
theorem rotPair_step {N : ℕ} {x : ℕ × ℕ} (h : W5 N x.1 x.2) :
    RotStep N x.1 x.2 (rotPair N x).2 := by
  obtain ⟨-, -, hlt, -, hdp, -⟩ := h
  simp only [RotStep, rotPair]
  exact Nat.div_mul_cancel hdp

/-- `W5` is preserved, in the functional form. -/
theorem W5_rotPair {N : ℕ} {x : ℕ × ℕ} (hN : 0 < N) (h : W5 N x.1 x.2) :
    W5 N (rotPair N x).1 (rotPair N x).2 :=
  W5_rot hN h (rotPair_step h)

/-- **Five rotations return the pair.** This is the order-five property on the index set of
`T5`, and with `no_golden_pair` for fixed points and `five_dvd_card_of_free` for the count it
is what `5 ∣ T(N,5)` needs. -/
theorem rotPair_five {N : ℕ} {x : ℕ × ℕ} (hN : 0 < N) (h : W5 N x.1 x.2) :
    rotPair N (rotPair N (rotPair N (rotPair N (rotPair N x)))) = x := by
  have hw1 : W5 N (rotPair N x).1 (rotPair N x).2 := W5_rotPair hN h
  have hw2 := W5_rotPair hN hw1
  have hw3 := W5_rotPair hN hw2
  have s2 : RotStep N x.1 x.2 (rotPair N x).2 := rotPair_step h
  have s3 : RotStep N x.2 (rotPair N x).2 (rotPair N (rotPair N x)).2 := rotPair_step hw1
  have s4 : RotStep N (rotPair N x).2 (rotPair N (rotPair N x)).2
      (rotPair N (rotPair N (rotPair N x))).2 := rotPair_step hw2
  have s5 : RotStep N (rotPair N (rotPair N x)).2 (rotPair N (rotPair N (rotPair N x))).2
      (rotPair N (rotPair N (rotPair N (rotPair N x)))).2 := rotPair_step hw3
  have hw4 := W5_rotPair hN hw3
  have s6 : RotStep N (rotPair N (rotPair N (rotPair N x))).2
      (rotPair N (rotPair N (rotPair N (rotPair N x)))).2
      (rotPair N (rotPair N (rotPair N (rotPair N (rotPair N x))))).2 := rotPair_step hw4
  obtain ⟨h5, h6⟩ := rot_five_closes hN (quid5_of_rot hN h s2 s3 s4) s5 s6
  exact Prod.ext h5 h6

/-! ## `5 ∣ T5 N`, the `W5`-pair count

The three hypotheses of `five_dvd_card_of_free` now hold on the index set of `T5`. What
remains is to see `{(p,q) : W5}` inside `box5` as a `Finset`: closure needs the search bound
`width5_bound_nat`, which bounds either coordinate since `W5` is symmetric in its two
arguments. -/

/-- `W5` is symmetric in its two arguments. -/
theorem W5_symm {N p q : ℕ} (h : W5 N p q) : W5 N q p := by
  obtain ⟨hp, hq, hlt, hd, hdp, hdq⟩ := h
  refine ⟨hq, hp, by rwa [Nat.mul_comm], by rwa [Nat.mul_comm], ?_, ?_⟩
  · rwa [Nat.mul_comm q p]
  · rwa [Nat.mul_comm q p]

/-- A `W5` pair lies in the search box. -/
theorem mem_box5_of_W5 {N p q : ℕ} (hN : 0 < N) (h : W5 N p q) : (p, q) ∈ box5 N := by
  obtain ⟨hp, hq, hlt, -, hdp, hdq⟩ := h
  have hb1 : p ≤ N ^ 3 + 2 * N ^ 2 := width5_bound_nat hN hq hlt hdq
  have hb2 : q ≤ N ^ 3 + 2 * N ^ 2 := by
    refine width5_bound_nat hN hp ?_ ?_
    · rwa [Nat.mul_comm]
    · rwa [Nat.mul_comm]
  simp only [box5, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hp, hb1⟩, ⟨hq, hb2⟩⟩

/-- **The rotation has no fixed point on a `W5` pair.** A fixed point would make the cycle
constant, and the closing condition then forces the golden ratio, which `golden_of_fixed`
excludes. Extracted from `five_dvd_T5`, which proved it inline; the orbit count of
`thm:orbit` needs it as a statement in its own right. -/
theorem rotPair_free {N : ℕ} (hN : 0 < N) {x : ℕ × ℕ} (hw : W5 N x.1 x.2) :
    rotPair N x ≠ x := by
  intro hcon
  have hfst : x.2 = x.1 := congrArg Prod.fst hcon
  have hsnd : (rotPair N x).2 = x.2 := congrArg Prod.snd hcon
  have hstep2 : (rotPair N x).2 * (x.1 * x.2 - N ^ 2) = N ^ 2 * (x.1 + N) :=
    rotPair_step hw
  rw [hsnd, hfst] at hstep2
  obtain ⟨hp, -, hlt, -, -, -⟩ := hw
  rw [hfst] at hlt
  refine golden_of_fixed hN hp ?_ hlt
  linarith [hstep2]

/-- **`5 ∣ T5 N`**, the `W5`-pair count; `friezes5_ncard` in `Count5.lean` transfers this
to `T(N,5)`. Theorem `thm:free` in the form Proposition `prop:tenprime` consumes:
the rotation acts freely with order five on the pairs `T5` counts. -/
theorem five_dvd_T5 {N : ℕ} (hN : 0 < N) : 5 ∣ T5 N := by
  classical
  set f : ℕ × ℕ → ℕ × ℕ := fun x => if W5 N x.1 x.2 then rotPair N x else x with hf
  have hstep : ∀ x, W5 N x.1 x.2 → f x = rotPair N x := by
    intro x h; simp only [hf]; exact if_pos h
  have hord : ∀ x, f (f (f (f (f x)))) = x := by
    intro x
    by_cases h : W5 N x.1 x.2
    · have i1 := W5_rotPair hN h
      have i2 := W5_rotPair hN i1
      have i3 := W5_rotPair hN i2
      have i4 := W5_rotPair hN i3
      rw [hstep x h, hstep _ i1, hstep _ i2, hstep _ i3, hstep _ i4]
      exact rotPair_five hN h
    · have hid : f x = x := by simp only [hf]; exact if_neg h
      simp only [hid]
  refine five_dvd_card_of_free hord _ ?_ ?_
  · -- maps the filtered box to itself
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    obtain ⟨-, hw⟩ := hx
    have hw' := W5_rotPair hN hw
    rw [hstep x hw]
    refine ⟨?_, hw'⟩
    have := mem_box5_of_W5 hN hw'
    simpa using this
  · -- no fixed point
    intro x hx hcon
    simp only [Finset.mem_filter] at hx
    obtain ⟨-, hw⟩ := hx
    rw [hstep x hw] at hcon
    -- the first coordinate gives x.2 = x.1
    have hfst : x.2 = x.1 := congrArg Prod.fst hcon
    have hsnd : (rotPair N x).2 = x.2 := congrArg Prod.snd hcon
    have hstep2 : (rotPair N x).2 * (x.1 * x.2 - N ^ 2) = N ^ 2 * (x.1 + N) :=
      rotPair_step hw
    rw [hsnd, hfst] at hstep2
    obtain ⟨hp, -, hlt, -, -, -⟩ := hw
    rw [hfst] at hlt
    refine golden_of_fixed hN hp ?_ hlt
    linarith [hstep2]

end VicoEnum
