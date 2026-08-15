/-
  VicoEnum/Width7Model.lean

  A model of `IsFrieze 7`.

  Width 5 has `cc5_positive` and width 6 has `cc6_isFrieze`; width 7 had no witness at all.
  What this file does NOT do is rescue `width7_bound_p3` from vacuity: that theorem never
  mentions `IsFrieze`, its six hypotheses are on free integers and are satisfiable outright,
  and nothing in the tree connects them to a width-7 frieze. `width7_bound_p3_nonvacuous`
  below instantiates it at this model's own numbers; the genuine remaining gap is deriving
  those relations from `IsFrieze 7`, which the paper still carries as PROVED.

  The Conway--Coxeter frieze with quiddity `(1,2,3,2,1,3,3)` supplies one. Its entries sum to
  `15 = 3n - 6` at `n = 7`, it has minimal period `7` (so the six closing identities are
  tested on seven distinct columns rather than a proper divisor), and its interior is
  strictly positive.
-/
import VicoEnum.Width6Model
import VicoEnum.Palindromic

namespace VicoEnum

/-- The quiddity `(1,2,3,2,1,3,3)`, extended `7`-periodically. -/
noncomputable def quid7 : ℤ → ℚ := fun j =>
  if j % 7 = 0 then 1
  else if j % 7 = 1 then 2
  else if j % 7 = 2 then 3
  else if j % 7 = 3 then 2
  else if j % 7 = 4 then 1
  else if j % 7 = 5 then 3
  else 3

theorem quid7_periodic (j : ℤ) : quid7 (j + 7) = quid7 j := by
  simp only [quid7, show (j + 7) % 7 = j % 7 from by omega]

theorem r0 (j : ℤ) (h : j % 7 = 0) : quid7 j = 1 := by simp [quid7, h]
theorem r1 (j : ℤ) (h : j % 7 = 1) : quid7 j = 2 := by simp [quid7, h]
theorem r2 (j : ℤ) (h : j % 7 = 2) : quid7 j = 3 := by simp [quid7, h]
theorem r3 (j : ℤ) (h : j % 7 = 3) : quid7 j = 2 := by simp [quid7, h]
theorem r4 (j : ℤ) (h : j % 7 = 4) : quid7 j = 1 := by simp [quid7, h]
theorem r5 (j : ℤ) (h : j % 7 = 5) : quid7 j = 3 := by simp [quid7, h]
theorem r6 (j : ℤ) (h : j % 7 = 6) : quid7 j = 3 := by simp [quid7, h]

/-- The length-six continuant. -/
theorem Kc_six (a : ℤ → ℚ) (j : ℤ) :
    Kc a j 6 = a (j + 5) * Kc a j 5 - Kc a j 4 := by
  have hi : j + ((4 : ℕ) : ℤ) + 1 = j + 5 := by push_cast; ring
  rw [Kc_succ_succ a j 4, hi]

/-- **`K₅ = 1` at every column.** -/
theorem quid7_five (j : ℤ) : Kc quid7 j 5 = 1 := by
  rw [Kc_five]
  rcases (by omega : j % 7 = 0 ∨ j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨ j % 7 = 4 ∨ j % 7 = 5 ∨
    j % 7 = 6) with h | h | h | h | h | h | h
  · rw [r0 j h, r1 (j+1) (by omega), r2 (j+2) (by omega), r3 (j+3) (by omega), r4 (j+4) (by omega)]; norm_num
  · rw [r1 j h, r2 (j+1) (by omega), r3 (j+2) (by omega), r4 (j+3) (by omega), r5 (j+4) (by omega)]; norm_num
  · rw [r2 j h, r3 (j+1) (by omega), r4 (j+2) (by omega), r5 (j+3) (by omega), r6 (j+4) (by omega)]; norm_num
  · rw [r3 j h, r4 (j+1) (by omega), r5 (j+2) (by omega), r6 (j+3) (by omega), r0 (j+4) (by omega)]; norm_num
  · rw [r4 j h, r5 (j+1) (by omega), r6 (j+2) (by omega), r0 (j+3) (by omega), r1 (j+4) (by omega)]; norm_num
  · rw [r5 j h, r6 (j+1) (by omega), r0 (j+2) (by omega), r1 (j+3) (by omega), r2 (j+4) (by omega)]; norm_num
  · rw [r6 j h, r0 (j+1) (by omega), r1 (j+2) (by omega), r2 (j+3) (by omega), r3 (j+4) (by omega)]; norm_num

/-- **`K₆ = 0` at every column.** -/
theorem quid7_six (j : ℤ) : Kc quid7 j 6 = 0 := by
  rw [Kc_six, quid7_five, Kc_four]
  rcases (by omega : j % 7 = 0 ∨ j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨ j % 7 = 4 ∨ j % 7 = 5 ∨
    j % 7 = 6) with h | h | h | h | h | h | h
  · rw [r0 j h, r1 (j+1) (by omega), r2 (j+2) (by omega), r3 (j+3) (by omega), r5 (j+5) (by omega)]; norm_num
  · rw [r1 j h, r2 (j+1) (by omega), r3 (j+2) (by omega), r4 (j+3) (by omega), r6 (j+5) (by omega)]; norm_num
  · rw [r2 j h, r3 (j+1) (by omega), r4 (j+2) (by omega), r5 (j+3) (by omega), r0 (j+5) (by omega)]; norm_num
  · rw [r3 j h, r4 (j+1) (by omega), r5 (j+2) (by omega), r6 (j+3) (by omega), r1 (j+5) (by omega)]; norm_num
  · rw [r4 j h, r5 (j+1) (by omega), r6 (j+2) (by omega), r0 (j+3) (by omega), r2 (j+5) (by omega)]; norm_num
  · rw [r5 j h, r6 (j+1) (by omega), r0 (j+2) (by omega), r1 (j+3) (by omega), r3 (j+5) (by omega)]; norm_num
  · rw [r6 j h, r0 (j+1) (by omega), r1 (j+2) (by omega), r2 (j+3) (by omega), r4 (j+5) (by omega)]; norm_num

/-- **The model.** -/
noncomputable def cc7 : ℕ → ℤ → ℚ := friezeOf quid7

theorem cc7_isFrieze : IsFrieze 7 cc7 := by
  refine friezeOf_isFrieze (by omega) ?_ (fun j => quid7_five j) (fun j => quid7_six j)
  intro j
  have h7 : ((7 : ℕ) : ℤ) = 7 := by norm_num
  rw [h7]
  exact quid7_periodic j

/-- **The interior is positive**, so `IsFrieze 7` together with the positivity hypothesis is
inhabited. -/
theorem cc7_positive : ∀ r j, 0 < r → r < 7 → 0 < cc7 r j := by
  intro r j h0 h7
  rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_pos
  · show 0 < quid7 j
    rcases (by omega : j % 7 = 0 ∨ j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨ j % 7 = 4 ∨
      j % 7 = 5 ∨ j % 7 = 6) with h | h | h | h | h | h | h
    · rw [r0 j h]; norm_num
    · rw [r1 j h]; norm_num
    · rw [r2 j h]; norm_num
    · rw [r3 j h]; norm_num
    · rw [r4 j h]; norm_num
    · rw [r5 j h]; norm_num
    · rw [r6 j h]; norm_num
  · show 0 < Kc quid7 j 2
    rw [Kc_two]
    rcases (by omega : j % 7 = 0 ∨ j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨ j % 7 = 4 ∨
      j % 7 = 5 ∨ j % 7 = 6) with h | h | h | h | h | h | h
    · rw [r0 j h, r1 (j+1) (by omega)]; norm_num
    · rw [r1 j h, r2 (j+1) (by omega)]; norm_num
    · rw [r2 j h, r3 (j+1) (by omega)]; norm_num
    · rw [r3 j h, r4 (j+1) (by omega)]; norm_num
    · rw [r4 j h, r5 (j+1) (by omega)]; norm_num
    · rw [r5 j h, r6 (j+1) (by omega)]; norm_num
    · rw [r6 j h, r0 (j+1) (by omega)]; norm_num
  · show 0 < Kc quid7 j 3
    rw [Kc_three]
    rcases (by omega : j % 7 = 0 ∨ j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨ j % 7 = 4 ∨
      j % 7 = 5 ∨ j % 7 = 6) with h | h | h | h | h | h | h
    · rw [r0 j h, r1 (j+1) (by omega), r2 (j+2) (by omega)]; norm_num
    · rw [r1 j h, r2 (j+1) (by omega), r3 (j+2) (by omega)]; norm_num
    · rw [r2 j h, r3 (j+1) (by omega), r4 (j+2) (by omega)]; norm_num
    · rw [r3 j h, r4 (j+1) (by omega), r5 (j+2) (by omega)]; norm_num
    · rw [r4 j h, r5 (j+1) (by omega), r6 (j+2) (by omega)]; norm_num
    · rw [r5 j h, r6 (j+1) (by omega), r0 (j+2) (by omega)]; norm_num
    · rw [r6 j h, r0 (j+1) (by omega), r1 (j+2) (by omega)]; norm_num
  · show 0 < Kc quid7 j 4
    rw [Kc_four]
    rcases (by omega : j % 7 = 0 ∨ j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨ j % 7 = 4 ∨
      j % 7 = 5 ∨ j % 7 = 6) with h | h | h | h | h | h | h
    · rw [r0 j h, r1 (j+1) (by omega), r2 (j+2) (by omega), r3 (j+3) (by omega)]; norm_num
    · rw [r1 j h, r2 (j+1) (by omega), r3 (j+2) (by omega), r4 (j+3) (by omega)]; norm_num
    · rw [r2 j h, r3 (j+1) (by omega), r4 (j+2) (by omega), r5 (j+3) (by omega)]; norm_num
    · rw [r3 j h, r4 (j+1) (by omega), r5 (j+2) (by omega), r6 (j+3) (by omega)]; norm_num
    · rw [r4 j h, r5 (j+1) (by omega), r6 (j+2) (by omega), r0 (j+3) (by omega)]; norm_num
    · rw [r5 j h, r6 (j+1) (by omega), r0 (j+2) (by omega), r1 (j+3) (by omega)]; norm_num
    · rw [r6 j h, r0 (j+1) (by omega), r1 (j+2) (by omega), r2 (j+3) (by omega)]; norm_num
  · show 0 < Kc quid7 j 5
    rw [quid7_five j]; norm_num

/-! ## `width7_bound_p3` at this model

`width7_bound_p3` takes six hypotheses on free integers and never mentions `IsFrieze`, so it
was never vacuous. What was missing is that its hypotheses hold at numbers coming from an
actual width-7 frieze rather than arbitrary ones. At `N = 1` the quiddity `(1,2,3,2,…)` gives
`u = p₀p₁ - N² = 1`, `G = p₂u - p₀N² = 2` and `E = p₃G - N²u = 3 = eN³`, so `e = 3`. Those are
`cc7`'s own row entries: `Kc quid7 0 2 = 1`, `Kc quid7 0 3 = 2`, `Kc quid7 0 4 = 3`.

This is an instantiation, not the bridge. Deriving the two relations from `IsFrieze 7` in
general is the gap the paper still carries as PROVED. -/

theorem cc7_entries : Kc quid7 0 2 = 1 ∧ Kc quid7 0 3 = 2 ∧ Kc quid7 0 4 = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Kc_two, r0 0 (by norm_num), r1 (0+1) (by norm_num)]; norm_num
  · rw [Kc_three, r0 0 (by norm_num), r1 (0+1) (by norm_num), r2 (0+2) (by norm_num)]; norm_num
  · rw [Kc_four, r0 0 (by norm_num), r1 (0+1) (by norm_num), r2 (0+2) (by norm_num),
      r3 (0+3) (by norm_num)]; norm_num

/-- **`width7_bound_p3` is not vacuous**, at the numbers `cc7` supplies. -/
theorem width7_bound_p3_nonvacuous : (2 : ℤ) ≤ 1 ^ 2 * (1 ^ 3 + 1 + 1) :=
  width7_bound_p3 (N := 1) (p3 := 2) (u := 1) (G := 2) (e := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end VicoEnum
