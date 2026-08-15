/-
  VicoEnum/Free.lean

  Theorem `thm:free`: the rotation action of `ℤ/5` on positive rational width-5 quiddity
  cycles is free.

  The paper's argument is that a cycle fixed by a nontrivial rotation is constant, because
  `5` is prime and a nontrivial rotation generates, and that a constant positive cycle is
  impossible. The second half was already formalised in isolation as `no_pos_rat_root`: for
  a constant quiddity the continuants are `K_0 = 1`, `K_1 = a`, `K_2 = a²-1`, `K_3 = a³-2a`,
  so the closing condition `K_3 = 1` on row `4` reads

      a³ - 2a - 1 = 0,

  which has no positive rational root. What was missing was everything around it: the
  frieze, the action, and the passage from fixed to constant. `IsFrieze` supplies the first,
  and this file supplies the rest.
-/
import VicoEnum.Frieze
import VicoEnum.Orbit

namespace VicoEnum

/-! ## Shifts -/

/-- Rotating a frieze by `k` columns. -/
def rotate (k : ℤ) (m : ℕ → ℤ → ℚ) : ℕ → ℤ → ℚ := fun r j => m r (j + k)

/-- A shift-invariant function is invariant under every integer multiple of the shift. -/
theorem shift_iter {a : ℤ → ℚ} {k : ℤ} (hk : ∀ j, a (j + k) = a j) :
    ∀ (i : ℤ) (j : ℤ), a (j + i * k) = a j := by
  intro i
  induction i using Int.induction_on with
  | hz => intro j; simp
  | hp p ih =>
    intro j
    have e : j + ((p : ℤ) + 1) * k = (j + p * k) + k := by ring
    rw [e, hk, ih]
  | hn p ih =>
    intro j
    have e : j + (-(p : ℤ) - 1) * k = (j + (-(p : ℤ)) * k) - k := by ring
    rw [e]
    have := hk (j + (-(p : ℤ)) * k - k)
    rw [show j + (-(p : ℤ)) * k - k + k = j + (-(p : ℤ)) * k from by ring] at this
    rw [← this]; exact ih j

/-- **Fixed by a rotation coprime to the period forces constancy.** With `uk + 5v = 1` the
shift by `1` factors through the shifts by `k` and by `5`, both of which fix `a`. -/
theorem const_of_shift_invariant {a : ℤ → ℚ} {k u v : ℤ}
    (hper : ∀ j, a (j + 5) = a j) (hk : ∀ j, a (j + k) = a j)
    (huv : u * k + v * 5 = 1) : ∀ j, a j = a 0 := by
  have hone : ∀ j, a (j + 1) = a j := by
    intro j
    have e : j + 1 = (j + u * k) + v * 5 := by rw [← huv]; ring
    rw [e, shift_iter hper v, shift_iter hk u]
  have hall : ∀ (i : ℤ) (j : ℤ), a (j + i) = a j := by
    intro i
    induction i using Int.induction_on with
    | hz => intro j; simp
    | hp p ih =>
      intro j
      have e : j + ((p : ℤ) + 1) = (j + p) + 1 := by ring
      rw [e, hone, ih]
    | hn p ih =>
      intro j
      have e : j + (-(p : ℤ) - 1) = (j + (-(p : ℤ))) - 1 := by ring
      rw [e]
      have := hone (j + (-(p : ℤ)) - 1)
      rw [show j + (-(p : ℤ)) - 1 + 1 = j + (-(p : ℤ)) from by ring] at this
      rw [← this]; exact ih j
  intro j
  have := hall j 0
  simpa using this

/-! ## No constant positive width-5 cycle -/

/-- The continuant of a constant sequence, at length `3`: `K_3 = a³ - 2a`. -/
theorem Kc_const_three {a : ℤ → ℚ} {c : ℚ} (hc : ∀ j, a j = c) (j : ℤ) :
    Kc a j 3 = c ^ 3 - 2 * c := by
  have h2 : Kc a j 2 = c * c - 1 := by
    rw [Kc_succ_succ a j 0]; simp [hc]
  rw [Kc_succ_succ a j 1, h2]
  simp only [Kc_one, hc]
  ring

/-- **No positive width-5 frieze has constant quiddity.** The closing condition on row `4`
forces `a³ - 2a - 1 = 0`, which `no_pos_rat_root` forbids for positive rational `a`. -/
theorem no_constant_quiddity {m : ℕ → ℤ → ℚ} (hm : IsFrieze 5 m)
    (hpos : ∀ r j, 0 < r → r < 5 → 0 < m r j)
    (hconst : ∀ j : ℤ, quiddity m j = quiddity m 0) : False := by
  set c := quiddity m 0 with hcdef
  have hcpos : 0 < c := hpos 2 0 (by omega) (by omega)
  obtain ⟨hone, -⟩ := closing_conditions hm hpos (by omega)
  have h3 : Kc (quiddity m) 0 3 = 1 := by have := hone 0; simpa using this
  rw [Kc_const_three hconst 0] at h3
  exact no_pos_rat_root c hcpos (by linarith [h3])

/-! ## Freeness -/

/-- **Theorem `thm:free`.** The rotation action of `ℤ/5` on positive rational width-5
friezes is free: no nontrivial rotation fixes the quiddity cycle. The hypothesis
`u k + 5 v = 1` says exactly that `k` is prime to `5`, which is what "nontrivial" means for
a rotation of order `5`. The hypothesis is stated on the quiddity, not on the whole array,
because that is what Theorem `thm:free` asserts and it is the weaker assumption: `IsFrieze n`
constrains no row above `n`, so two friezes can share a quiddity and differ as arrays. -/
theorem rotation_free {m : ℕ → ℤ → ℚ} (hm : IsFrieze 5 m)
    (hpos : ∀ r j, 0 < r → r < 5 → 0 < m r j) {k u v : ℤ} (huv : u * k + v * 5 = 1)
    (hfix : ∀ j : ℤ, quiddity m (j + k) = quiddity m j) : False := by
  have hk : ∀ j : ℤ, quiddity m (j + k) = quiddity m j := hfix
  have hper : ∀ j : ℤ, quiddity m (j + 5) = quiddity m j := by
    intro j
    have := hm.periodic 2 j
    simpa [quiddity] using this
  exact no_constant_quiddity hm hpos (const_of_shift_invariant hper hk huv)

/-- The Conway--Coxeter frieze of width `5` witnesses that the hypotheses of
`rotation_free` are not vacuous: it is a positive width-5 frieze, so the theorem says
something about a nonempty class. -/
theorem rotation_free_nonvacuous : IsPositiveFrieze 5 cc5 := cc5_positive

/-! ## The rotation is a free action of order five

`rotate k` carries friezes to friezes, composes additively, and is the identity at `k = n`
by periodicity. At `n = 5` it therefore has order `5`, and `rotation_free` says it has no
fixed point. Feeding those two facts to `five_dvd_card_of_free` divides by five any finite
collection of positive width-5 friezes closed under rotation. -/

theorem rotate_isFrieze {n : ℕ} {m : ℕ → ℤ → ℚ} (hm : IsFrieze n m) (k : ℤ) :
    IsFrieze n (rotate k m) where
  periodic := by
    intro r j
    simp only [rotate]
    rw [show j + (n : ℤ) + k = (j + k) + (n : ℤ) from by ring, hm.periodic]
  row_zero := fun j => hm.row_zero _
  row_one := fun j => hm.row_one _
  row_top_one := fun j => hm.row_top_one _
  row_top_zero := fun j => hm.row_top_zero _
  diamond := by
    intro r j h2 hn
    simp only [rotate, show j + 1 + k = (j + k) + 1 from by ring]
    exact hm.diamond r (j + k) h2 hn

theorem rotate_pos {n : ℕ} {m : ℕ → ℤ → ℚ} (hpos : ∀ r j, 0 < r → r < n → 0 < m r j) (k : ℤ) :
    ∀ r j, 0 < r → r < n → 0 < rotate k m r j := fun r j h1 h2 => hpos r (j + k) h1 h2

theorem rotate_add (a b : ℤ) (m : ℕ → ℤ → ℚ) :
    rotate a (rotate b m) = rotate (a + b) m := by
  funext r j
  simp only [rotate]
  rw [show j + a + b = j + (a + b) from by ring]

/-- At the width, rotation is the identity: that is the periodicity field. -/
theorem rotate_width {n : ℕ} {m : ℕ → ℤ → ℚ} (hm : IsFrieze n m) : rotate (n : ℤ) m = m := by
  funext r j
  exact hm.periodic r j

/-- **Rotation by one has order five at width five.** -/
theorem rotate_one_order_five {m : ℕ → ℤ → ℚ} (hm : IsFrieze 5 m) :
    rotate 1 (rotate 1 (rotate 1 (rotate 1 (rotate 1 m)))) = m := by
  rw [rotate_add, rotate_add, rotate_add, rotate_add]
  have h5 : (1 : ℤ) + 1 + 1 + 1 + 1 = ((5 : ℕ) : ℤ) := by norm_num
  rw [h5]
  exact rotate_width hm

/-- **Five divides any rotation-closed collection of positive width-5 friezes.** This is
Theorem `thm:free` in the form the counting argument consumes. `five_dvd_card_of_free`
wants a map of order five on all of the ambient type, so rotation is extended by the
identity off the frieze locus; that changes nothing on `S`, where every element is a
frieze. -/
theorem five_dvd_card_of_friezes (S : Finset (ℕ → ℤ → ℚ))
    (hS : ∀ m ∈ S, IsFrieze 5 m ∧ ∀ r j, 0 < r → r < 5 → 0 < m r j)
    (hclosed : ∀ m ∈ S, rotate 1 m ∈ S) : 5 ∣ S.card := by
  classical
  set f : (ℕ → ℤ → ℚ) → (ℕ → ℤ → ℚ) :=
    fun m => if IsFrieze 5 m then rotate 1 m else m with hf
  have hstep : ∀ m, IsFrieze 5 m → f m = rotate 1 m := by
    intro m h; simp only [hf]; exact if_pos h
  have hord : ∀ m, f (f (f (f (f m)))) = m := by
    intro m
    by_cases h : IsFrieze 5 m
    · have i1 := rotate_isFrieze h 1
      have i2 := rotate_isFrieze i1 1
      have i3 := rotate_isFrieze i2 1
      have i4 := rotate_isFrieze i3 1
      rw [hstep m h, hstep _ i1, hstep _ i2, hstep _ i3, hstep _ i4]
      exact rotate_one_order_five h
    · have : f m = m := by simp only [hf]; exact if_neg h
      simp only [this]
  have hmap : ∀ m ∈ S, f m ∈ S := by
    intro m hm
    rw [hstep m (hS m hm).1]
    exact hclosed m hm
  have hfree : ∀ m ∈ S, f m ≠ m := by
    intro m hm
    obtain ⟨hfr, hp⟩ := hS m hm
    rw [hstep m hfr]
    intro hcon
    refine rotation_free hfr hp (k := 1) (u := 1) (v := 0) (by norm_num) ?_
    intro j
    have := congrFun (congrFun hcon 2) j
    simpa [rotate, quiddity] using this
  exact five_dvd_card_of_free hord S hmap hfree

end VicoEnum
