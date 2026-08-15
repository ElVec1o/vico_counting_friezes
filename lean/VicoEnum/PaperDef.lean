/-
  VicoEnum/PaperDef.lean

  Definition `def:frieze` transcribed literally, and the identification with `Friezes5`.

  `IsFrieze n` carries a `periodic` field. Definition `def:frieze` does not: it states the
  boundary rows, the diamond rule on the strip `0 ≤ i-j ≤ n`, and positivity, and nothing
  else. Every count in this paper is over the paper's definition, so the two must be shown
  to agree rather than assumed to; that gap is where five earlier versions of this file went
  wrong, each proving something about a neighbouring object.

  `PaperFrieze5` below assumes NO periodicity. The main point is `pf_period`: at width `5`
  periodicity is a consequence, not an axiom. Clearing the diamond gives the quiddity
  recursion `a_{j+2}(a_j a_{j+1} - 1) = a_j + 1` (`pf_rec`), whose iterate has order `5`, so
  the paper's conditions already force `a_{j+5} = a_j`. With that, `pf_quid` identifies the
  quiddity as `quid5fn` of its first two entries and the two inclusions go through.

  The conclusion is `paper_count`: the set Definition `def:count` counts has exactly `T5 N`
  elements, with `T(1,5) = 5 = C_3` as `eq:catalan` requires.
-/
import VicoEnum.Count5

namespace VicoEnum

/-- Definition `def:frieze` at width `5`, over `(1/N)ℤ`, written literally: a map on the
strip `0 ≤ i-j ≤ 5` in the coordinates `(r,j) = (i-j, j)`, boundary rows `0,5` zero and
`1,4` one, the paper's diamond `m_{i,j}m_{i+1,j+1} - m_{i,j+1}m_{i+1,j} = 1` at every
`(i,j)` for which all four entries are in the strip, positivity of the interior, lattice.
NO periodicity is assumed -- the paper's definition does not state it. -/
structure PaperFrieze5 (N : ℕ) (F : Fin 6 → ℤ → ℚ) : Prop where
  z0 : ∀ j, F 0 j = 0
  o1 : ∀ j, F 1 j = 1
  o4 : ∀ j, F 4 j = 1
  z5 : ∀ j, F 5 j = 0
  d1 : ∀ j, F 1 j * F 1 (j + 1) - F 0 (j + 1) * F 2 j = 1
  d2 : ∀ j, F 2 j * F 2 (j + 1) - F 1 (j + 1) * F 3 j = 1
  d3 : ∀ j, F 3 j * F 3 (j + 1) - F 2 (j + 1) * F 4 j = 1
  d4 : ∀ j, F 4 j * F 4 (j + 1) - F 3 (j + 1) * F 5 j = 1
  p2 : ∀ j, 0 < F 2 j
  p3 : ∀ j, 0 < F 3 j
  lat : ∀ r j, InLattice N (F r j)

variable {N : ℕ} {F : Fin 6 → ℤ → ℚ}

/-- Row `3` is the cleared diamond: `b_j = a_j a_{j+1} - 1`. -/
theorem pf_row3 (h : PaperFrieze5 N F) (j : ℤ) : F 3 j = F 2 j * F 2 (j + 1) - 1 := by
  have := h.d2 j; rw [h.o1 (j + 1)] at this; linarith

/-- `D_j = a_j a_{j+1} - 1 > 0`. -/
theorem pf_D (h : PaperFrieze5 N F) (j : ℤ) : 0 < F 2 j * F 2 (j + 1) - 1 := by
  rw [← pf_row3 h j]; exact h.p3 j

/-- **The quiddity recursion**, in cleared form: `a_{j+2}(a_j a_{j+1} - 1) = a_j + 1`.
This is Proposition `prop:param` at `n = 5`, derived from the paper's conditions alone. -/
theorem pf_rec (h : PaperFrieze5 N F) (j : ℤ) :
    F 2 (j + 2) * (F 2 j * F 2 (j + 1) - 1) = F 2 j + 1 := by
  have h3 := h.d3 j
  rw [h.o4 j, pf_row3 h j, pf_row3 h (j + 1), mul_one] at h3
  have hj : j + 1 + 1 = j + 2 := by ring
  rw [hj] at h3
  have hy : 0 < F 2 (j + 1) := h.p2 (j + 1)
  refine mul_left_cancel₀ hy.ne' ?_
  linear_combination h3

/-- Row `3` is the shift of row `2` by three columns: `a_{j+3} = a_j a_{j+1} - 1`.
This is the glide symmetry of Remark `rem:glide`, again from the paper's conditions. -/
theorem pf_shift3 (h : PaperFrieze5 N F) (j : ℤ) :
    F 2 (j + 3) = F 2 j * F 2 (j + 1) - 1 := by
  have hz := pf_rec h j
  have hw := pf_rec h (j + 1)
  have e1 : j + 1 + 1 = j + 2 := by ring
  have e2 : j + 1 + 2 = j + 3 := by ring
  rw [e1, e2] at hw
  have hyz : 0 < F 2 (j + 1) * F 2 (j + 2) - 1 := by
    have := pf_D h (j + 1); rwa [e1] at this
  refine mul_left_cancel₀ hyz.ne' ?_
  linear_combination hw - F 2 (j + 1) * hz

/-- **The quiddity is `5`-periodic.**  Not assumed: derived from Definition `def:frieze`.
So the `periodic` field of `IsFrieze` is not an extra restriction at width `5`. -/
theorem pf_period (h : PaperFrieze5 N F) (j : ℤ) : F 2 (j + 5) = F 2 j := by
  have hx : 0 < F 2 j := h.p2 j
  have hy : 0 < F 2 (j + 1) := h.p2 (j + 1)
  have hz := pf_rec h j
  have hw3 := pf_shift3 h j
  have hu := pf_rec h (j + 2)
  have e1 : j + 2 + 1 = j + 3 := by ring
  have e2 : j + 2 + 2 = j + 4 := by ring
  rw [e1, e2, hw3] at hu
  have hzw : F 2 (j + 2) * (F 2 j * F 2 (j + 1) - 1) - 1 = F 2 j := by linarith [hz]
  rw [hzw] at hu
  have hv := pf_rec h (j + 3)
  have e3 : j + 3 + 1 = j + 4 := by ring
  have e4 : j + 3 + 2 = j + 5 := by ring
  rw [e3, e4, hw3] at hv
  have hwu : (F 2 j * F 2 (j + 1) - 1) * F 2 (j + 4) - 1 = F 2 (j + 1) := by
    refine mul_left_cancel₀ hx.ne' ?_
    linear_combination (F 2 j * F 2 (j + 1) - 1) * hu + hz
  rw [hwu] at hv
  refine mul_left_cancel₀ hy.ne' ?_
  linear_combination hv

/-- The quiddity is `quid5fn` of its first two entries. -/
theorem pf_quid (h : PaperFrieze5 N F) (j : ℤ) :
    F 2 j = quid5fn (F 2 0) (F 2 1) j := by
  have hD0 : (0 : ℚ) < F 2 0 * F 2 1 - 1 := by
    have := pf_D h 0; norm_num at this ⊢; linarith
  have hDne : (F 2 0 * F 2 1 - 1) ≠ 0 := hD0.ne'
  have hx : (0 : ℚ) < F 2 0 := h.p2 0
  have hper : ∀ k : ℤ, F 2 (k + 5) = F 2 k := pf_period h
  have ha3 : F 2 3 = F 2 0 * F 2 1 - 1 := by
    have := pf_shift3 h 0; norm_num at this ⊢; linarith
  have hzw : F 2 2 * (F 2 0 * F 2 1 - 1) = F 2 0 + 1 := by
    have := pf_rec h 0; norm_num at this ⊢; linarith
  have ha2 : F 2 2 = (F 2 0 + 1) / (F 2 0 * F 2 1 - 1) := by
    rw [eq_div_iff hDne]; exact hzw
  have ha4 : F 2 4 = (F 2 1 + 1) / (F 2 0 * F 2 1 - 1) := by
    have hu := pf_rec h 2
    norm_num at hu
    rw [ha3] at hu
    have h1 : F 2 4 * F 2 0 = F 2 2 + 1 := by linear_combination hu - F 2 4 * hzw
    have h2 : F 2 4 * (F 2 0 * F 2 1 - 1) * F 2 0 = (F 2 1 + 1) * F 2 0 := by
      linear_combination (F 2 0 * F 2 1 - 1) * h1 + hzw
    rw [eq_div_iff hDne]
    exact mul_right_cancel₀ hx.ne' h2
  rw [(periodic_mod hper j : F 2 j = F 2 (j % 5))]
  rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4)
    with hj | hj | hj | hj | hj
  · rw [hj, q0 _ _ j hj]
  · rw [hj, q1 _ _ j hj]
  · rw [hj, q2 _ _ j hj, ha2]
  · rw [hj, q3 _ _ j hj, ha3]
  · rw [hj, q4 _ _ j hj, ha4]

/-- **Every paper frieze is in `Friezes5 N`.**  No periodicity assumed. -/
theorem paperFrieze5_mem (hN : 0 < N) (h : PaperFrieze5 N F) : F ∈ Friezes5 N := by
  have hx : (0 : ℚ) < F 2 0 := h.p2 0
  have hy : (0 : ℚ) < F 2 1 := h.p2 1
  have hD0 : (0 : ℚ) < F 2 0 * F 2 1 - 1 := by
    have := pf_D h 0; norm_num at this ⊢; linarith
  have hlatq : ∀ j : ℤ, InLattice N (quid5fn (F 2 0) (F 2 1) j) := by
    intro j; rw [← pf_quid h j]; exact h.lat 2 j
  refine ⟨friezeOf (quid5fn (F 2 0) (F 2 1)),
    width5_build_positive hx hy hD0,
    width5_build_lattice hN hD0.ne' hlatq, ?_⟩
  funext r j
  obtain ⟨v, hv⟩ := r
  show F ⟨v, hv⟩ j = friezeOf (quid5fn (F 2 0) (F 2 1)) v j
  interval_cases v
  · exact h.z0 j
  · exact h.o1 j
  · exact pf_quid h j
  · show F 3 j = Kc (quid5fn (F 2 0) (F 2 1)) j 2
    rw [Kc_two, pf_row3 h j, ← pf_quid h j, ← pf_quid h (j + 1)]; ring
  · show F 4 j = Kc (quid5fn (F 2 0) (F 2 1)) j 3
    rw [quid5fn_three hD0.ne' j]; exact h.o4 j
  · show F 5 j = Kc (quid5fn (F 2 0) (F 2 1)) j 4
    rw [quid5fn_four hD0.ne' j]; exact h.z5 j

/-- The other inclusion: every member of `Friezes5 N` satisfies Definition `def:frieze`. -/
theorem mem_paperFrieze5 (hF : F ∈ Friezes5 N) : PaperFrieze5 N F := by
  obtain ⟨m, hm, hlat, rfl⟩ := hF
  have d : ∀ r j, 2 ≤ r → r ≤ 5 →
      m (r - 2) (j + 1) * m r j = m (r - 1) j * m (r - 1) (j + 1) - 1 :=
    fun r j h2 h5 => hm.1.diamond r j h2 h5
  refine ⟨fun j => hm.1.row_zero j, fun j => hm.1.row_one j, fun j => hm.1.row_top_one j,
    fun j => hm.1.row_top_zero j, ?_, ?_, ?_, ?_,
    fun j => hm.2 2 j (by omega) (by omega), fun j => hm.2 3 j (by omega) (by omega),
    fun r j => hlat (r : ℕ) j (by omega)⟩
  · intro j; have h := d 2 j (by omega) (by omega); norm_num at h
    show m 1 j * m 1 (j + 1) - m 0 (j + 1) * m 2 j = (1 : ℚ); linarith
  · intro j; have h := d 3 j (by omega) (by omega); norm_num at h
    show m 2 j * m 2 (j + 1) - m 1 (j + 1) * m 3 j = (1 : ℚ); linarith
  · intro j; have h := d 4 j (by omega) (by omega); norm_num at h
    show m 3 j * m 3 (j + 1) - m 2 (j + 1) * m 4 j = (1 : ℚ); linarith
  · intro j; have h := d 5 j (by omega) (by omega); norm_num at h
    show m 4 j * m 4 (j + 1) - m 3 (j + 1) * m 5 j = (1 : ℚ); linarith

/-- **`Friezes5 N` is exactly the set Definition `def:count` counts.** -/
theorem friezes5_eq_paper (hN : 0 < N) :
    Friezes5 N = {F : Fin 6 → ℤ → ℚ | PaperFrieze5 N F} :=
  Set.eq_of_subset_of_subset (fun _ hF => mem_paperFrieze5 hF)
    (fun _ hF => paperFrieze5_mem hN hF)

/-- Hence the headline theorem, stated on the paper's own definition. -/
theorem paper_count (hN : 0 < N) :
    {F : Fin 6 → ℤ → ℚ | PaperFrieze5 N F}.ncard = T5 N := by
  rw [← friezes5_eq_paper hN]; exact friezes5_ncard hN

theorem paper_count_one : {F : Fin 6 → ℤ → ℚ | PaperFrieze5 1 F}.ncard = 5 := by
  rw [paper_count (by norm_num), T5_one]

end VicoEnum
