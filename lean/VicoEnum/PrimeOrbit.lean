/-
  VicoEnum/PrimeOrbit.lean

  How many entries of a width-5 quiddity over `(1/p)ℤ` are integers.

  At width 5 the glide gives `a_{j+3} = a_j a_{j+1} - 1` for every `j` modulo 5
  (Remark 2.3), which in numerators is

      p_j p_{j+1} = p (p_{j+3} + p).                                     (rel)

  If `p ∤ p_{j+3}` then the right side has `p`-valuation exactly one, so exactly one of
  `p_j`, `p_{j+1}` is divisible by `p` (`w5_val_step`). Writing
  `I = {j : p ∣ p_j}` for the set of integer entries, that says: for every `m ∉ I`,
  exactly one of `m+2`, `m+3` lies in `I`. Only two cardinalities survive that condition
  on `ℤ/5`, namely 3 and 5 (`zmod5_card`, by exhaustion over the 32 subsets).

  So a width-5 frieze over `(1/p)ℤ` has either exactly three integer entries or five, and
  five happens only for the Conway--Coxeter frieze `(2,2,1,3,1)`. This is the arithmetic
  behind Conjecture `conj:orbit`: since `e_j = p\,p_{j+3}` one has
  `M_j = p\,p_{j+3}/g_j`, and `p ∤ p_{j+3}` forces `M_j = p` (`w5_M_eq_p`), which supplies
  two of the five positions in the generic case. The remaining implication, that
  `p ∣ p_{j+3}` forces `M_j = p^2`, is not proved here.
-/
import VicoEnum.Bounds5

namespace VicoEnum

/-- **The valuation step.** If `xy = p(z+p)` with `p` prime and `p ∤ z`, then exactly one
of `x`, `y` is divisible by `p`. -/
theorem w5_val_step {p x y z : ℤ} (hp : Prime p) (h : x * y = p * (z + p))
    (hz : ¬ (p ∣ z)) : (p ∣ x ∨ p ∣ y) ∧ ¬ (p ∣ x ∧ p ∣ y) := by
  constructor
  · refine hp.2.2 x y ?_
    exact ⟨z + p, h⟩
  · rintro ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩
    apply hz
    have hp0 : p ≠ 0 := hp.ne_zero
    have h1 : p * (p * (x' * y')) = p * (z + p) := by linear_combination h
    have h2 : p * (x' * y') = z + p := mul_left_cancel₀ hp0 h1
    exact ⟨x' * y' - 1, by linarith [h2]⟩

/-- **The combinatorial step.** A subset `I` of `ℤ/5` such that every `m ∉ I` has exactly
one of `m+2`, `m+3` in `I` has cardinality 3 or 5. Checked by exhaustion over the 32
subsets. -/
theorem zmod5_card : ∀ I : Finset (ZMod 5),
    (∀ m : ZMod 5, m ∉ I →
      ((m + 2 ∈ I ∧ m + 3 ∉ I) ∨ (m + 2 ∉ I ∧ m + 3 ∈ I))) →
    I.card = 3 ∨ I.card = 5 := by decide

/-- **The count of integer entries.** For a width-5 quiddity over `(1/p)ℤ`, written in
numerators `q : ℤ/5 → ℤ` and satisfying the glide relation (rel), the number of entries
divisible by `p`, that is the number of integer entries of the frieze, is 3 or 5. -/
theorem w5_integer_count {p : ℤ} (hp : Prime p) (q : ZMod 5 → ℤ)
    [DecidablePred (fun j : ZMod 5 => p ∣ q j)]
    (hrel : ∀ j : ZMod 5, q j * q (j + 1) = p * (q (j + 3) + p)) :
    (Finset.univ.filter (fun j : ZMod 5 => p ∣ q j)).card = 3 ∨
      (Finset.univ.filter (fun j : ZMod 5 => p ∣ q j)).card = 5 := by
  refine zmod5_card _ ?_
  intro m hm
  have hmem : ∀ k : ZMod 5,
      (k ∈ Finset.univ.filter (fun j : ZMod 5 => p ∣ q j)) ↔ p ∣ q k := by
    intro k; simp
  have hmz : ¬ (p ∣ q m) := fun hc => hm ((hmem m).mpr hc)
  have e1 : (m + 2) + 1 = m + 3 := by
    rw [add_assoc, show (2 : ZMod 5) + 1 = 3 by decide]
  have e2 : (m + 2) + 3 = m := by
    rw [add_assoc, show (2 : ZMod 5) + 3 = 0 by decide, add_zero]
  have hrel' := hrel (m + 2)
  rw [e1, e2] at hrel'
  obtain ⟨hor, hnot⟩ := w5_val_step hp hrel' hmz
  rcases hor with hx | hy
  · exact Or.inl ⟨(hmem _).mpr hx, fun hc => hnot ⟨hx, (hmem _).mp hc⟩⟩
  · exact Or.inr ⟨fun hc => hnot ⟨(hmem _).mp hc, hy⟩, (hmem _).mpr hy⟩

/-- **Two of the five positions are forced.** With `e_j = p p_{j+3}` the width-5 parameter
is `M_j = p p_{j+3}/g_j`, so if `p ∤ p_{j+3}` then one of `p_j`, `p_{j+1}` is prime to `p`,
hence so is `g_j = gcd(p_j+p, p_{j+1}+p)`, and `M_j = p`. In the generic case exactly two
indices lie outside `I`, which gives the two positions with `M = p` of Conjecture
`conj:orbit`. The converse implication is not proved here. -/
theorem w5_M_eq_p {p x g : ℤ} (hx : ¬ (p ∣ x)) (hg : g ∣ x + p) : ¬ (p ∣ g) := by
  intro hpg
  obtain ⟨t, ht⟩ := hg
  obtain ⟨s, rfl⟩ := hpg
  exact hx ⟨s * t - 1, by linarith [ht]⟩

/-- **The cancellation.** If `p Y = c X` with `X ∣ Y` and `X ≠ 0`, then `p ∣ c`. -/
theorem w5_dvd_of_rel {p c X Y : ℤ} (hX : X ≠ 0) (hrel : p * Y = c * X) (hXY : X ∣ Y) :
    p ∣ c := by
  obtain ⟨s, rfl⟩ := hXY
  have h : X * (p * s - c) = 0 := by linear_combination hrel
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 hX
  · exact ⟨s, by linarith [h1]⟩

/-- **The last position, and with it Conjecture `conj:orbit`.** At the unique index `i`
with `p ∣ p_i` and `p ∣ p_{i+1}`, write `p_i = pα`, `p_{i+1} = pβ`, so that
`p_{i+3} = p(αβ-1)` and `g_i = p\,G` with `G = gcd(α+1, β+1)`. Relation (rel) at `j = i+2`
gives `p_{i+2}(αβ-1) = p(α+1)` with `p ∤ p_{i+2}`. Then `M_i = p` would mean `g_i = p_{i+3}`,
that is `G = αβ-1`; but `G ∣ α+1`, so `αβ-1` would divide `α+1`, and `w5_dvd_of_rel` would
force `p ∣ p_{i+2}`. Hence `M_i = p^2`.

This closes the last of the five positions, so every rotation orbit other than the rigid
one has exactly two entries with `M = p` and three with `M = p^2`. -/
theorem w5_last_position {p c a b G : ℤ} (hc : ¬ (p ∣ c)) (hX : a * b - 1 ≠ 0)
    (hrel : p * (a + 1) = c * (a * b - 1)) (hG : G ∣ a + 1) : G ≠ a * b - 1 := by
  intro h
  exact hc (w5_dvd_of_rel hX hrel (h ▸ hG))


/-! ## The orbit split, assembled

A positive width-5 frieze over `(1/N)ℤ` is exactly a positive `q : ℤ/5 → ℤ` with
`q j * q (j+1) = N * (q (j+3) + N)` for every `j`: by Remark 2.3 the interior rows are
2 and 3 and the glide exchanges them, so that single cyclic relation is the whole closing
condition. Everything below is stated for such a `q`.

The parameter of Theorem `thm:markov` at position `j` is `M j = p q(j+3) / g j` with
`g j = gcd(q j + p, q (j+1) + p)`, and `M j ∈ {p, p²}` by Proposition `prop:support`. In
divisibility terms that dichotomy reads `g j = q (j+3)` or `p * g j = q (j+3)`, and the
first case is `M j = p`. So the orbit split is a statement about how often
`g j = q (j+3)`.
-/

/-- The 3-element subsets of `ℤ/5` compatible with the integer-entry condition are exactly
the sets `{i, i+1, i+3}`: each has a unique adjacent pair. -/
theorem zmod5_three_structure : ∀ I : Finset (ZMod 5),
    (∀ m : ZMod 5, m ∉ I →
      ((m + 2 ∈ I ∧ m + 3 ∉ I) ∨ (m + 2 ∉ I ∧ m + 3 ∈ I))) →
    I.card = 3 → ∃ i : ZMod 5, I = {i, i + 1, i + 3} := by decide

/-- In `{i, i+1, i+3}` the only element whose successor is also present is `i`. -/
theorem zmod5_adjacent_unique : ∀ i x : ZMod 5,
    x ∈ ({i, i + 1, i + 3} : Finset (ZMod 5)) →
    x + 1 ∈ ({i, i + 1, i + 3} : Finset (ZMod 5)) → x = i := by decide

/-- `i+2` is the gap of `{i, i+1, i+3}`. -/
theorem zmod5_gap : ∀ i : ZMod 5,
    i + 2 ∉ ({i, i + 1, i + 3} : Finset (ZMod 5)) := by decide

/-- If membership of `S` is membership of the complement of `I` shifted by three, then
`|I| = 3` forces `|S| = 2`. -/
theorem zmod5_shift_count : ∀ I S : Finset (ZMod 5),
    (∀ j : ZMod 5, j ∈ S ↔ j + 3 ∉ I) → I.card = 3 → S.card = 2 := by decide

/-- **The orbit split at a prime.** Let `q` be a positive width-5 quiddity over `(1/p)ℤ`
and let `g` divide both `q j + p` and `q (j+1) + p` at each position, subject to the
dichotomy `g j = q (j+3)` or `p * g j = q (j+3)` supplied by Proposition `prop:support`.
If not every entry is an integer, then exactly two of the five positions satisfy
`g j = q (j+3)`, that is exactly two have `M j = p` and three have `M j = p^2`. -/
theorem orbit_split {p : ℤ} (hp : Prime p) (q g : ZMod 5 → ℤ)
    [DecidablePred (fun j : ZMod 5 => p ∣ q j)]
    [DecidablePred (fun j : ZMod 5 => g j = q (j + 3))]
    (hpos : ∀ j, 0 < q j)
    (hrel : ∀ j, q j * q (j + 1) = p * (q (j + 3) + p))
    (hgl : ∀ j, g j ∣ q j + p) (hgr : ∀ j, g j ∣ q (j + 1) + p)
    (hdich : ∀ j, g j = q (j + 3) ∨ p * g j = q (j + 3))
    (hnotall : (Finset.univ.filter (fun j : ZMod 5 => p ∣ q j)).card ≠ 5) :
    (Finset.univ.filter (fun j : ZMod 5 => g j = q (j + 3))).card = 2 := by
  set I := Finset.univ.filter (fun j : ZMod 5 => p ∣ q j) with hIdef
  set S := Finset.univ.filter (fun j : ZMod 5 => g j = q (j + 3)) with hSdef
  have hmemI : ∀ k : ZMod 5, k ∈ I ↔ p ∣ q k := by intro k; simp [hIdef]
  have hmemS : ∀ k : ZMod 5, k ∈ S ↔ g k = q (k + 3) := by intro k; simp [hSdef]
  -- the condition driving both combinatorial lemmas
  have hcond : ∀ m : ZMod 5, m ∉ I →
      ((m + 2 ∈ I ∧ m + 3 ∉ I) ∨ (m + 2 ∉ I ∧ m + 3 ∈ I)) := by
    intro m hm
    have hmz : ¬ (p ∣ q m) := fun hc => hm ((hmemI m).mpr hc)
    have e1 : (m + 2) + 1 = m + 3 := by
      rw [add_assoc, show (2 : ZMod 5) + 1 = 3 by decide]
    have e2 : (m + 2) + 3 = m := by
      rw [add_assoc, show (2 : ZMod 5) + 3 = 0 by decide, add_zero]
    have hrel' := hrel (m + 2)
    rw [e1, e2] at hrel'
    obtain ⟨hor, hnot⟩ := w5_val_step hp hrel' hmz
    rcases hor with hx | hy
    · exact Or.inl ⟨(hmemI _).mpr hx, fun hc => hnot ⟨hx, (hmemI _).mp hc⟩⟩
    · exact Or.inr ⟨fun hc => hnot ⟨(hmemI _).mp hc, hy⟩, (hmemI _).mpr hy⟩
  have hcard : I.card = 3 := by
    rcases zmod5_card I hcond with h | h
    · exact h
    · exact absurd h hnotall
  obtain ⟨i, hI⟩ := zmod5_three_structure I hcond hcard
  -- `p` divides `g j` exactly when it divides both neighbours
  have hgp : ∀ j : ZMod 5, p ∣ g j → (p ∣ q j ∧ p ∣ q (j + 1)) := by
    intro j hj
    constructor
    · exact (dvd_add_left (dvd_refl p)).mp (dvd_trans hj (hgl j))
    · exact (dvd_add_left (dvd_refl p)).mp (dvd_trans hj (hgr j))
  refine zmod5_shift_count I S ?_ hcard
  intro j
  constructor
  · -- g j = q (j+3) forces p not to divide q (j+3)
    intro hjS hj3
    have hgq : g j = q (j + 3) := (hmemS j).mp hjS
    have hpg : p ∣ g j := by rw [hgq]; exact (hmemI _).mp hj3
    obtain ⟨hqj, hqj1⟩ := hgp j hpg
    -- so j and j+1 both lie in I, hence j = i by the structure of I
    have hji : j = i := by
      have h1 : j ∈ I := (hmemI j).mpr hqj
      have h2 : j + 1 ∈ I := (hmemI _).mpr hqj1
      rw [hI] at h1 h2
      exact zmod5_adjacent_unique i j h1 h2
    subst hji
    -- p does not divide q (j+2)
    have hj2 : ¬ (p ∣ q (j + 2)) := by
      intro hc
      have hmem : j + 2 ∈ I := (hmemI _).mpr hc
      rw [hI] at hmem
      exact zmod5_gap j hmem
    -- write q j = p a and q (j+3) = p (a b - 1); apply w5_last_position
    obtain ⟨a, ha⟩ := hqj
    obtain ⟨b, hb⟩ := hqj1
    have habrel : q (j + 3) = p * (a * b - 1) := by
      have h := hrel j
      rw [ha, hb] at h
      have hp0 : p ≠ 0 := hp.ne_zero
      have : p * (p * (a * b)) = p * (q (j + 3) + p) := by linear_combination h
      have h2 : p * (a * b) = q (j + 3) + p := mul_left_cancel₀ hp0 this
      linear_combination -h2
    have hne : a * b - 1 ≠ 0 := by
      intro hz
      have : q (j + 3) = 0 := by rw [habrel, hz, mul_zero]
      exact absurd this (hpos (j + 3)).ne'
    -- relation at j+2 : q(j+2) q(j+3) = p (q j + p)
    have e3 : (j + 2) + 1 = j + 3 := by
      rw [add_assoc, show (2 : ZMod 5) + 1 = 3 by decide]
    have e4 : (j + 2) + 3 = j := by
      rw [add_assoc, show (2 : ZMod 5) + 3 = 0 by decide, add_zero]
    have hr2 := hrel (j + 2)
    rw [e3, e4, habrel, ha] at hr2
    -- hr2 : q (j+2) * (p * (a*b-1)) = p * (p * a + p)
    have hkey : p * (a + 1) = q (j + 2) * (a * b - 1) := by
      have hp0 : p ≠ 0 := hp.ne_zero
      refine mul_left_cancel₀ hp0 ?_
      linear_combination -hr2
    -- g j = p * G with G dividing a + 1
    obtain ⟨G, hG⟩ := hpg
    have hGdvd : G ∣ a + 1 := by
      have h1 : g j ∣ q j + p := hgl j
      rw [hG, ha] at h1
      obtain ⟨t, ht⟩ := h1
      have hp0 : p ≠ 0 := hp.ne_zero
      exact ⟨t, mul_left_cancel₀ hp0 (by linear_combination ht)⟩
    have hGeq : G = a * b - 1 := by
      have h1 : p * G = p * (a * b - 1) := by rw [← hG, hgq]; exact habrel
      exact mul_left_cancel₀ hp.ne_zero h1
    exact w5_last_position hj2 hne hkey hGdvd hGeq
  · -- p does not divide q (j+3): then p does not divide g j, so the dichotomy picks case one
    intro hj3
    have hnq : ¬ (p ∣ q (j + 3)) := fun hc => hj3 ((hmemI _).mpr hc)
    refine (hmemS j).mpr ?_
    rcases hdich j with h | h
    · exact h
    · exact absurd ⟨g j, h.symm⟩ hnq

end VicoEnum
