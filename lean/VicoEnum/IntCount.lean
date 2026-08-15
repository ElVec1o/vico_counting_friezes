/-
  VicoEnum/IntCount.lean

  Proposition `prop:intcount`: at a prime `p`, the number of integer entries in the quiddity
  cycle of a positive width-5 frieze over `(1/p)ℤ` is `3` or `5`, and it is `5` exactly for
  the Conway--Coxeter frieze `(2,2,1,3,1)` and its rotations.

  Three steps, each self-contained.

  The valuation step. Writing the quiddity numerators as `P : ℤ/5 → ℤ`, equation `eq:w5cyc`
  reads `P j * P (j+1) = p (P (j+3) + p)`. If `p ∤ P (j+3)` the right side has `p`-valuation
  exactly one, so exactly one of `P j`, `P (j+1)` is divisible by `p`. That is
  `exactly_one_dvd`, and it needs only primality.

  MOST OF THE FIRST TWO STEPS ARE ALREADY IN `PrimeOrbit.lean` and are restated here over
  `Fin 5` rather than `ZMod 5`: `exactly_one_dvd` is `w5_val_step`, `alt_card` is
  `zmod5_card`, and `alt_three` is `zmod5_three_structure`. None of those three is new. What
  is genuinely new is the derivation of the glide hypothesis from a frieze (`quid5fn_glide`,
  `glide_of_frieze`, `w5cyc_fin`), the classification at size five (`cc_classify`), and the
  two frieze-level statements `intcount_frieze` and `intcount_five_frieze`.

  The combinatorial step. Let `I = {j : p ∣ P j}`. Reindexing the above by `j = m+2` says:
  for every `m ∉ I`, exactly one of `m+2`, `m+3` lies in `I`. Over `ℤ/5` there are `32`
  subsets, so this is a finite check; `decide` returns that the only ones have cardinality
  `3` or `5`, the former being exactly `{i, i+1, i+3}`.

  The classification. If `I` is everything, every `a j = P j / p` is a positive integer and
  the relation becomes `a j a_{j+1} = a_{j+3} + 1`. Taking `k` at which `a` is largest,
  `a k + 1 = a_{k+2} a_{k+3}` with both factors at least `2` (a factor `1` would make the
  other exceed the maximum), and `a_{k+2} = a_{k+4} a_k - 1` then forces `a k ≤ 3`. The three
  cases `a k = 1, 2, 3` leave only `(3,1,2,2,1)` read from `k`, which is `(2,2,1,3,1)` rotated.
  No search over tuples is needed.
-/
import VicoEnum.Basic
import VicoEnum.Bijection
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

namespace VicoEnum

open Finset

/-! ## The valuation step -/

/-- **Exactly one of two consecutive numerators is divisible by `p`**, whenever the one three
places on is not. This is the consequence of the `p`-valuation of `eq:w5cyc` being one; the
valuation itself is not computed. Same content as `w5_val_step` in `PrimeOrbit.lean`. -/
theorem exactly_one_dvd {p : ℕ} (hp : p.Prime) {x y z : ℤ}
    (hcyc : x * y = (p : ℤ) * (z + p)) (h : ¬ ((p : ℤ) ∣ z)) :
    ((p : ℤ) ∣ x) ↔ ¬ ((p : ℤ) ∣ y) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hor : ((p : ℤ) ∣ x) ∨ ((p : ℤ) ∣ y) := by
    refine hpZ.dvd_mul.mp ?_
    exact ⟨z + p, hcyc⟩
  constructor
  · rintro ⟨u, rfl⟩ ⟨v, rfl⟩
    -- both divisible forces `p ∣ z`
    apply h
    have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.pos.ne'
    have : (p : ℤ) * ((p : ℤ) * (u * v)) = (p : ℤ) * (z + p) := by rw [← hcyc]; ring
    have h2 : (p : ℤ) * (u * v) = z + p := by
      exact mul_left_cancel₀ hp0 this
    exact ⟨u * v - 1, by linarith [h2]⟩
  · intro hy
    rcases hor with hx | hx
    · exact hx
    · exact absurd hx hy

/-! ## The combinatorial step

`I ⊆ ℤ/5` has the property that every `m` outside it has exactly one of `m+2`, `m+3` inside.
Both statements below are finite checks over the `32` subsets. -/

/-- The property the divisibility set inherits from `exactly_one_dvd`. -/
def Alt (I : Finset (Fin 5)) : Prop :=
  ∀ m : Fin 5, m ∉ I → ((m + 2 ∈ I) ↔ (m + 3 ∉ I))

instance (I : Finset (Fin 5)) : Decidable (Alt I) := by unfold Alt; infer_instance

/-- **Three or five.** -/
theorem alt_card (I : Finset (Fin 5)) (h : Alt I) : I.card = 3 ∨ I.card = 5 := by
  revert h; revert I; decide

/-- **A set of size three is of the form `{i, i+1, i+3}`.** The converse, that every such set
has the property, is true but not stated. Same content as `zmod5_three_structure`. -/
theorem alt_three (I : Finset (Fin 5)) (h : Alt I) (hc : I.card = 3) :
    ∃ i : Fin 5, I = {i, i + 1, i + 3} := by
  revert hc; revert h; revert I; decide

/-- **Five means everything.** -/
theorem alt_five (I : Finset (Fin 5)) (hc : I.card = 5) : I = univ := by
  revert hc; revert I; decide



/-! ## The Conway--Coxeter classification

If every numerator is divisible by `p`, the entries `a j = P j / p` are positive integers and
`eq:w5cyc` becomes `a j a_{j+1} = a_{j+3} + 1`. That relation has exactly one solution up to
rotation. -/

/-- **The only positive integer solution of `a_j a_{j+1} = a_{j+3}+1` on `ℤ/5`** is
`(3,1,2,2,1)` read from a suitable starting point, which is `(2,2,1,3,1)` rotated. -/
theorem cc_classify (a : Fin 5 → ℕ) (hpos : ∀ j, 0 < a j)
    (hrel : ∀ j, a j * a (j + 1) = a (j + 3) + 1) :
    ∃ k : Fin 5, a k = 3 ∧ a (k + 1) = 1 ∧ a (k + 2) = 2 ∧ a (k + 3) = 2 ∧ a (k + 4) = 1 := by
  obtain ⟨k, hk⟩ := Finite.exists_max a
  -- index identities in `ℤ/5`
  have i1 : ∀ k : Fin 5, k + 2 + 1 = k + 3 := by decide
  have i2 : ∀ k : Fin 5, k + 2 + 3 = k := by decide
  have i3 : ∀ k : Fin 5, k + 4 + 1 = k := by decide
  have i4 : ∀ k : Fin 5, k + 4 + 3 = k + 2 := by decide
  -- the two relations that see the maximum
  have e2 : a (k + 2) * a (k + 3) = a k + 1 := by
    have := hrel (k + 2); rwa [i1, i2] at this
  have e4 : a (k + 4) * a k = a (k + 2) + 1 := by
    have := hrel (k + 4); rwa [i3, i4] at this
  -- neither factor of `a k + 1` can be `1`
  have h2 : 2 ≤ a (k + 2) := by
    by_contra hc
    have h1 : a (k + 2) = 1 := by have := hpos (k + 2); omega
    rw [h1, one_mul] at e2
    have := hk (k + 3); omega
  have h3 : 2 ≤ a (k + 3) := by
    by_contra hc
    have h1 : a (k + 3) = 1 := by have := hpos (k + 3); omega
    rw [h1, mul_one] at e2
    have := hk (k + 2); omega
  -- the maximum is at most `3`
  have hle : a k ≤ 3 := by
    have hb : 2 * a (k + 2) ≤ a k + 1 := by nlinarith [e2, h3]
    have hc : a k ≤ a (k + 2) + 1 := by nlinarith [e4, hpos (k + 4)]
    omega
  -- and it is exactly `3`
  have hk3 : a k = 3 := by
    interval_cases h : a k
    · exact absurd h (hpos k).ne'
    · -- everything is `1`
      exfalso
      have hall : ∀ j, a j = 1 := fun j => by have := hk j; have := hpos j; omega
      have := hrel 0; rw [hall, hall, hall] at this; omega
    · exfalso; nlinarith [e2, h2, h3]
    · rfl
  -- read off the remaining four entries
  rw [hk3] at e2 e4
  have h2e : a (k + 2) = 2 := by
    rcases (by omega : a (k + 2) = 2 ∨ 3 ≤ a (k + 2)) with h | h
    · exact h
    · exfalso; nlinarith [e2, h3]
  have h3e : a (k + 3) = 2 := by rw [h2e] at e2; omega
  have h4e : a (k + 4) = 1 := by rw [h2e] at e4; omega
  have h1e : a (k + 1) = 1 := by
    have := hrel k; rw [hk3, h3e] at this; omega
  exact ⟨k, hk3, h1e, h2e, h3e, h4e⟩

/-! ## Equation `eq:w5cyc`

The hypothesis `hcyc` above is not free: it is what a positive width-5 frieze over `(1/N)ℤ`
gives. Remark `rem:glide` says the width-5 glide is `a_{j+3} = a_j a_{j+1} - 1` at every
column, and that is a five-case check on `quid5fn`; passing to numerators over `N` turns it
into `eq:w5cyc`. -/

/-- **The glide relation of Remark `rem:glide`**, at every column. -/
theorem quid5fn_glide {a0 a1 : ℚ} (hD : a0 * a1 - 1 ≠ 0) (j : ℤ) :
    quid5fn a0 a1 (j + 3) = quid5fn a0 a1 j * quid5fn a0 a1 (j + 1) - 1 := by
  rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4)
    with h | h | h | h | h
  · rw [q3 _ _ (j + 3) (by omega), q0 _ _ j h, q1 _ _ (j + 1) (by omega)]
  · rw [q4 _ _ (j + 3) (by omega), q1 _ _ j h, q2 _ _ (j + 1) (by omega)]
    field_simp; ring
  · rw [q0 _ _ (j + 3) (by omega), q2 _ _ j h, q3 _ _ (j + 1) (by omega)]
    field_simp
  · rw [q1 _ _ (j + 3) (by omega), q3 _ _ j h, q4 _ _ (j + 1) (by omega)]
    field_simp
  · rw [q2 _ _ (j + 3) (by omega), q4 _ _ j h, q0 _ _ (j + 1) (by omega)]
    field_simp; ring

/-- **The glide relation for a frieze.** -/
theorem glide_of_frieze {m : ℕ → ℤ → ℚ} (hm : IsPositiveFrieze 5 m) (j : ℤ) :
    quiddity m (j + 3) = quiddity m j * quiddity m (j + 1) - 1 := by
  have hD : quiddity m 0 * quiddity m 1 - 1 = quiddity m 3 := by
    obtain ⟨e3, -, -⟩ := width5_from_frieze hm.1 hm.2; linarith [e3]
  have hDne : quiddity m 0 * quiddity m 1 - 1 ≠ 0 := by
    rw [hD]; exact (hm.2 2 3 (by omega) (by omega)).ne'
  rw [quiddity_eq_quid5fn hm.1 hm.2 (j + 3), quiddity_eq_quid5fn hm.1 hm.2 j,
    quiddity_eq_quid5fn hm.1 hm.2 (j + 1)]
  exact quid5fn_glide hDne j

/-- **Equation `eq:w5cyc`.** In numerators over `N`, the glide relation reads
`P_j P_{j+1} = N (P_{j+3} + N)`. This is the `ℤ`-indexed form, matching `eq:w5cyc` literally;
the counting arguments use the `ℤ/5`-indexed `w5cyc_fin` below. -/
theorem w5cyc_of_frieze {N : ℕ} (hN : 0 < N) {m : ℕ → ℤ → ℚ} (hm : IsPositiveFrieze 5 m)
    {P : ℤ → ℤ} (hP : ∀ j, quiddity m j = (P j : ℚ) / N) (j : ℤ) :
    P j * P (j + 1) = (N : ℤ) * (P (j + 3) + N) := by
  have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hg := glide_of_frieze hm j
  rw [hP j, hP (j + 1), hP (j + 3)] at hg
  have : ((P j : ℚ)) * (P (j + 1)) = (N : ℚ) * ((P (j + 3)) + N) := by
    field_simp at hg
    refine mul_left_cancel₀ hNQ ?_
    linear_combination -hg
  exact_mod_cast this

/-! ## Proposition `prop:intcount` -/

/-- The columns at which the numerator is divisible by `p`. -/
def divSet (p : ℕ) (P : Fin 5 → ℤ) : Finset (Fin 5) :=
  univ.filter (fun j => (p : ℤ) ∣ P j)

/-- The divisibility set has the alternation property. This is `exactly_one_dvd` reindexed
by `j = m+2`, using `(m+2)+3 = m` in `ℤ/5`. -/
theorem divSet_alt {p : ℕ} (hp : p.Prime) {P : Fin 5 → ℤ}
    (hcyc : ∀ j, P j * P (j + 1) = (p : ℤ) * (P (j + 3) + p)) :
    Alt (divSet p P) := by
  have i1 : ∀ m : Fin 5, m + 2 + 1 = m + 3 := by decide
  have i2 : ∀ m : Fin 5, m + 2 + 3 = m := by decide
  intro m hm
  have hmd : ¬ ((p : ℤ) ∣ P m) := by
    simpa [divSet] using hm
  have hc := hcyc (m + 2)
  rw [i1 m, i2 m] at hc
  have := exactly_one_dvd hp hc hmd
  simpa [divSet] using this

/-- **Proposition `prop:intcount`, the count.** The number of integer entries is `3` or `5`. -/
theorem intcount_card {p : ℕ} (hp : p.Prime) {P : Fin 5 → ℤ}
    (hcyc : ∀ j, P j * P (j + 1) = (p : ℤ) * (P (j + 3) + p)) :
    (divSet p P).card = 3 ∨ (divSet p P).card = 5 :=
  alt_card _ (divSet_alt hp hcyc)

/-- **Proposition `prop:intcount`, the shape at three.** -/
theorem intcount_three {p : ℕ} (hp : p.Prime) {P : Fin 5 → ℤ}
    (hcyc : ∀ j, P j * P (j + 1) = (p : ℤ) * (P (j + 3) + p))
    (hc : (divSet p P).card = 3) :
    ∃ i : Fin 5, divSet p P = {i, i + 1, i + 3} :=
  alt_three _ (divSet_alt hp hcyc) hc

/-- **Proposition `prop:intcount`, the case of five.** All five entries integral forces the
Conway--Coxeter quiddity `(2,2,1,3,1)` up to rotation. -/
theorem intcount_five {p : ℕ} (hp : p.Prime) {P : Fin 5 → ℤ}
    (hpos : ∀ j, 0 < P j)
    (hcyc : ∀ j, P j * P (j + 1) = (p : ℤ) * (P (j + 3) + p))
    (hc : (divSet p P).card = 5) :
    ∃ (k : Fin 5) (a : Fin 5 → ℕ), (∀ j, P j = (p : ℤ) * a j) ∧
      a k = 3 ∧ a (k + 1) = 1 ∧ a (k + 2) = 2 ∧ a (k + 3) = 2 ∧ a (k + 4) = 1 := by
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hall : ∀ j, (p : ℤ) ∣ P j := by
    intro j
    have : j ∈ divSet p P := by rw [alt_five _ hc]; exact mem_univ j
    simpa [divSet] using this
  have key : ∀ j, ∃ c : ℕ, 0 < c ∧ P j = (p : ℤ) * c := by
    intro j
    obtain ⟨c, hc⟩ := hall j
    have hcpos : 0 < c := by
      by_contra hcon
      push_neg at hcon
      have : P j ≤ 0 := by rw [hc]; exact mul_nonpos_of_nonneg_of_nonpos hpZ.le hcon
      exact absurd this (not_le.mpr (hpos j))
    exact ⟨c.toNat, by omega, by rw [hc]; congr 1; exact (Int.toNat_of_nonneg hcpos.le).symm⟩
  choose a hapos hPa using key
  have hrel : ∀ j, a j * a (j + 1) = a (j + 3) + 1 := by
    intro j
    have hc' := hcyc j
    rw [hPa j, hPa (j + 1), hPa (j + 3)] at hc'
    have hp2 : ((p : ℤ) * (p : ℤ)) ≠ 0 := by positivity
    have h2 : (p : ℤ) * (p : ℤ) * ((a j : ℤ) * a (j + 1))
        = (p : ℤ) * (p : ℤ) * ((a (j + 3) : ℤ) + 1) := by linear_combination hc'
    exact_mod_cast mul_left_cancel₀ hp2 h2
  obtain ⟨k, hk⟩ := cc_classify a hapos hrel
  exact ⟨k, a, hPa, hk⟩

/-! ## The proposition for a frieze

The three theorems above take `eq:w5cyc` as a hypothesis. `w5cyc_of_frieze` supplies it, so
what follows is the proposition as Proposition `prop:intcount` states it: about the quiddity
cycle of a positive width-5 frieze over `(1/p)ℤ`, with no equation assumed. -/

/-- Column arithmetic in `ℤ/5` matches column arithmetic in `ℤ` modulo `5`. -/
theorem fin5_val_add (j : Fin 5) (k : Fin 5) :
    (((j + k) : Fin 5).val : ℤ) = ((j.val : ℤ) + (k.val : ℤ)) % 5 := by
  rw [Fin.val_add]
  omega

/-- **Proposition `prop:intcount`.** At a prime `p`, the quiddity cycle of a positive width-5
frieze over `(1/p)ℤ` has `3` or `5` integer entries. -/
theorem w5cyc_fin {p : ℕ} (hp : 0 < p) {m : ℕ → ℤ → ℚ} (hm : IsPositiveFrieze 5 m)
    {Q : Fin 5 → ℤ} (hQ : ∀ j : Fin 5, quiddity m (j.val : ℤ) = (Q j : ℚ) / p) :
    ∀ j : Fin 5, Q j * Q (j + 1) = (p : ℤ) * (Q (j + 3) + p) := by
  have hper5 : ∀ k : ℤ, quiddity m (k + 5) = quiddity m k := by
    intro k; have := quiddity_period hm.1 k; simpa using this
  have hmod : ∀ k : ℤ, quiddity m k = quiddity m (k % 5) := periodic_mod hper5
  have hext : ∀ (j : Fin 5) (k : Fin 5),
      quiddity m ((j.val : ℤ) + (k.val : ℤ)) = (Q (j + k) : ℚ) / p := by
    intro j k
    rw [hmod, ← fin5_val_add j k, ← hQ (j + k)]
  intro j
  have h1 : quiddity m ((j.val : ℤ) + 1) = (Q (j + 1) : ℚ) / p := by
    have := hext j 1; simpa using this
  have h3 : quiddity m ((j.val : ℤ) + 3) = (Q (j + 3) : ℚ) / p := by
    have := hext j 3; simpa using this
  have hNQ : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hg := glide_of_frieze hm (j.val : ℤ)
  rw [h3, hQ j, h1] at hg
  have hQ' : ((Q j : ℚ)) * (Q (j + 1)) = (p : ℚ) * ((Q (j + 3)) + p) := by
    field_simp at hg
    refine mul_left_cancel₀ hNQ ?_
    linear_combination -hg
  exact_mod_cast hQ'

/-- The numerators of a positive frieze are positive. -/
theorem Q_pos {p : ℕ} (hp : 0 < p) {m : ℕ → ℤ → ℚ} (hm : IsPositiveFrieze 5 m)
    {Q : Fin 5 → ℤ} (hQ : ∀ j : Fin 5, quiddity m (j.val : ℤ) = (Q j : ℚ) / p) :
    ∀ j : Fin 5, 0 < Q j := by
  intro j
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have h := hm.2 2 (j.val : ℤ) (by omega) (by omega)
  rw [show m 2 (j.val : ℤ) = quiddity m (j.val : ℤ) from rfl, hQ j] at h
  rw [lt_div_iff₀ hpQ, zero_mul] at h
  exact_mod_cast h

/-- **Proposition `prop:intcount`.** At a prime `p`, the quiddity cycle of a positive width-5
frieze over `(1/p)ℤ` has `3` or `5` integer entries. -/
theorem intcount_frieze {p : ℕ} (hp : p.Prime) {m : ℕ → ℤ → ℚ} (hm : IsPositiveFrieze 5 m)
    {Q : Fin 5 → ℤ} (hQ : ∀ j : Fin 5, quiddity m (j.val : ℤ) = (Q j : ℚ) / p) :
    (divSet p Q).card = 3 ∨ (divSet p Q).card = 5 :=
  intcount_card hp (w5cyc_fin hp.pos hm hQ)

/-- **Proposition `prop:intcount`, the case of five, for a frieze.** This is `intcount_five`
with its two hypotheses discharged from the frieze rather than assumed: positivity by
`Q_pos` and `eq:w5cyc` by `w5cyc_fin`. -/
theorem intcount_five_frieze {p : ℕ} (hp : p.Prime) {m : ℕ → ℤ → ℚ}
    (hm : IsPositiveFrieze 5 m) {Q : Fin 5 → ℤ}
    (hQ : ∀ j : Fin 5, quiddity m (j.val : ℤ) = (Q j : ℚ) / p)
    (hc : (divSet p Q).card = 5) :
    ∃ (k : Fin 5) (a : Fin 5 → ℕ), (∀ j, Q j = (p : ℤ) * a j) ∧
      a k = 3 ∧ a (k + 1) = 1 ∧ a (k + 2) = 2 ∧ a (k + 3) = 2 ∧ a (k + 4) = 1 :=
  intcount_five hp (Q_pos hp.pos hm hQ) (w5cyc_fin hp.pos hm hQ) hc

end VicoEnum
