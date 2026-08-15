/-
  VicoEnum/Bijection.lean

  The two maps between `W5` pairs and width-5 friezes are mutually inverse.

  `W5_of_frieze` runs frieze to pair; `w5cond_converse` runs pair to frieze. Having both
  does not make the counts equal: that needs the composites to be the identity, which is
  what this file proves.

  One direction is immediate. Building from `(a₀,a₁)` and reading the first two quiddity
  entries returns `(a₀,a₁)`, because `quiddity (friezeOf a) j = a j` definitionally and
  `quid5fn` takes the stated values at columns `0` and `1`.

  The other direction is `frieze_rebuild`. A positive width-5 frieze has quiddity exactly
  `quid5fn` of its first two entries: at columns `0` and `1` by definition, at `2`, `3`, `4`
  by `width5_from_frieze`, and at every other column because both sides have period `5`.
  With `frieze_determined` this returns the frieze itself.

  ONE CAVEAT, and it matters for counting. `IsFrieze n` constrains rows `0` to `n` and says
  nothing above `n`, so two arrays can satisfy it, share every constrained row, and still
  differ. `frieze_rebuild` therefore gives agreement on rows `1` to `5`, which with
  `row_zero` is every row the definition mentions, and not equality of the arrays. The
  paper's Definition `def:frieze` has the bounded domain `0 ≤ i-j ≤ n`, so it is the paper's
  friezes that these pairs biject with, not with arrays satisfying `IsFrieze 5`. Turning this
  into `T5 N = T(N,5)` needs the count taken over rows `≤ 5`; that is done in `Count5.lean`,
  where `Friezes5` is the set of those restrictions and `friezes5_ncard` is the equality.
-/
import VicoEnum.W5Converse
import VicoEnum.Free

namespace VicoEnum

/-! ## Reading the quiddity back -/

@[simp] theorem quiddity_friezeOf (a : ℤ → ℚ) (j : ℤ) :
    quiddity (friezeOf a) j = a j := rfl

/-- **One composite is the identity on pairs.** -/
theorem pair_roundtrip (a0 a1 : ℚ) :
    quiddity (friezeOf (quid5fn a0 a1)) 0 = a0 ∧
    quiddity (friezeOf (quid5fn a0 a1)) 1 = a1 := by
  refine ⟨?_, ?_⟩
  · simpa using q0 a0 a1 0 (by norm_num)
  · simpa using q1 a0 a1 1 (by norm_num)

/-! ## The quiddity of a frieze is `quid5fn` of its first two entries -/

/-- The quiddity of a width-`n` frieze has period `n`. -/
theorem quiddity_period {n : ℕ} {m : ℕ → ℤ → ℚ} (hm : IsFrieze n m) (j : ℤ) :
    quiddity m (j + (n : ℤ)) = quiddity m j := by
  simpa [quiddity] using hm.periodic 2 j

/-- A `5`-periodic function is determined by the column mod `5`. -/
theorem periodic_mod {a : ℤ → ℚ} (hper : ∀ j, a (j + 5) = a j) (j : ℤ) :
    a j = a (j % 5) := by
  have h := shift_iter hper (j / 5) (j % 5)
  have hj : j % 5 + j / 5 * 5 = j := by omega
  rw [hj] at h
  exact h

/-- **The quiddity is `quid5fn` of its first two entries.** -/
theorem quiddity_eq_quid5fn {m : ℕ → ℤ → ℚ} (hm : IsFrieze 5 m)
    (hpos : ∀ r j, 0 < r → r < 5 → 0 < m r j) (j : ℤ) :
    quiddity m j = quid5fn (quiddity m 0) (quiddity m 1) j := by
  obtain ⟨e3, e2, e4⟩ := width5_from_frieze hm hpos
  have hper : ∀ k : ℤ, quiddity m (k + 5) = quiddity m k := by
    intro k
    have := quiddity_period hm k
    simpa using this
  have hD : quiddity m 0 * quiddity m 1 - 1 = quiddity m 3 := by linarith [e3]
  have hDne : quiddity m 0 * quiddity m 1 - 1 ≠ 0 := by
    rw [hD]; exact (hpos 2 3 (by omega) (by omega)).ne'
  rw [periodic_mod hper j]
  rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4)
    with h | h | h | h | h
  · rw [h, q0 _ _ j h]
  · rw [h, q1 _ _ j h]
  · rw [h, q2 _ _ j h]
    field_simp
    linarith [e2]
  · rw [h, q3 _ _ j h]; linarith [e3]
  · rw [h, q4 _ _ j h]
    field_simp
    linarith [e4]

/-- **The other composite is the identity on friezes.** Building from a frieze's first two
quiddity entries returns the frieze, on rows `1` to `5`. Row `0` vanishes on both sides;
`rebuild_agree` in `Count5.lean` is the version covering every row Definition `def:frieze`
constrains. -/
theorem frieze_rebuild {m : ℕ → ℤ → ℚ} (hm : IsFrieze 5 m)
    (hpos : ∀ r j, 0 < r → r < 5 → 0 < m r j) :
    ∀ r j, 1 ≤ r → r ≤ 5 →
      friezeOf (quid5fn (quiddity m 0) (quiddity m 1)) r j = m r j := by
  have hD : quiddity m 0 * quiddity m 1 - 1 = quiddity m 3 := by
    obtain ⟨e3, -, -⟩ := width5_from_frieze hm hpos; linarith [e3]
  have hDne : quiddity m 0 * quiddity m 1 - 1 ≠ 0 := by
    rw [hD]; exact (hpos 2 3 (by omega) (by omega)).ne'
  have hbuild : IsFrieze 5 (friezeOf (quid5fn (quiddity m 0) (quiddity m 1))) :=
    width5_build hDne
  have hbpos : ∀ r j, 0 < r → r < 5 →
      0 < friezeOf (quid5fn (quiddity m 0) (quiddity m 1)) r j := by
    refine width5_build_pos (hpos 2 0 (by omega) (by omega))
      (hpos 2 1 (by omega) (by omega)) ?_
    rw [hD]; exact hpos 2 3 (by omega) (by omega)
  intro r j h1 h5
  refine frieze_determined hbuild hm hbpos hpos ?_ r j h1 h5
  intro k
  rw [quiddity_friezeOf]
  exact (quiddity_eq_quid5fn hm hpos k).symm

end VicoEnum
