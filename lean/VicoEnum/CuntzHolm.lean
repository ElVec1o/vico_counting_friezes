/-
  VicoEnum/CuntzHolm.lean

  The descent mechanism behind the uniform bound.

  Cuntz and Holm (J. Comb. Algebra 3 (2019), Theorem 3.6) prove that for any
  `R ⊆ ℂ` with `M := inf{|x| : x ∈ R \ {0}} > 0`, every quiddity entry of a frieze
  over `R \ {0}` of height `h` has absolute value at most `((h-1) + 2M)/M²`. Over
  `(1/N)ℤ` one has `M = 1/N`, and their height `h` is our width `n` minus three, so
  the bound reads `(n-4)N² + 2N`.

  Their proof runs a descent along two consecutive rows: the diamond rule turns a
  large entry into a lower bound on the next entry, and iterating `h` times exceeds
  what the row can hold. The step that drives that descent is isolated here.

  SUPERSEDED. Everything below is an abandoned scaffold. `CuntzHolmFull.lean` proves the
  bound directly by telescoping (`chS_step`, `chS_telescope`, `cuntz_holm_bound`) and uses
  none of these declarations; a scan of the tree found all ten unreferenced and uncited. They
  are left in place because they are correct and were the route by which the direct proof was
  found, but nothing depends on them and the paper cites none of them. The genuine remaining
  gap for Theorem `thm:uniform` is the instantiation of `cuntz_holm_bound` at a frieze, with
  `M = 1/N` and their height `h` matched to our width, which the paper carries as PROVED.
-/
import VicoEnum.Basic

namespace VicoEnum

/-- **The Cuntz--Holm descent step.** If two consecutive rows of a frieze satisfy the
diamond relation `x₁y₁ - x₂ = 1`, and every nonzero entry of the ambient set has
absolute value at least `M`, then a large `x₁` forces `x₂` to be large as well:
`M·|x₁| ≤ 1 + |x₂|`. -/
theorem ch_step {M x₁ x₂ y₁ : ℚ} (hM : 0 < M) (hy : M ≤ |y₁|)
    (h : x₁ * y₁ - x₂ = 1) : M * |x₁| ≤ 1 + |x₂| := by
  have hx : (0 : ℚ) ≤ |x₁| := abs_nonneg _
  have h1 : |x₁| * M ≤ |x₁| * |y₁| := mul_le_mul_of_nonneg_left hy hx
  have h2 : |x₁| * |y₁| = |x₁ * y₁| := (abs_mul _ _).symm
  have h3 : x₁ * y₁ = 1 + x₂ := by linarith
  have h4 : |1 + x₂| ≤ 1 + |x₂| := by
    calc |1 + x₂| ≤ |(1 : ℚ)| + |x₂| := abs_add _ _
      _ = 1 + |x₂| := by norm_num
  calc M * |x₁| = |x₁| * M := by ring
    _ ≤ |x₁| * |y₁| := h1
    _ = |x₁ * y₁| := h2
    _ = |1 + x₂| := by rw [h3]
    _ ≤ 1 + |x₂| := h4

/-- Contrapositive form: over `(1/N)ℤ` every nonzero entry has absolute value at
least `1/N`, so a quiddity entry exceeding `B` forces the next entry to exceed
`B/N - 1`. This is the inequality iterated in the Cuntz--Holm proof. -/
theorem ch_step_lattice {N : ℕ} (hN : 0 < N) {B x₁ x₂ y₁ : ℚ}
    (hy : (1 : ℚ) / N ≤ |y₁|) (h : x₁ * y₁ - x₂ = 1) (hB : B < |x₁|) :
    B / N - 1 < |x₂| := by
  have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hM : (0 : ℚ) < 1 / N := by positivity
  have key := ch_step hM hy h
  have : (1 / (N : ℚ)) * B ≤ (1 / (N : ℚ)) * |x₁| :=
    mul_le_mul_of_nonneg_left hB.le hM.le
  have hlt : (1 / (N : ℚ)) * B < (1 / (N : ℚ)) * |x₁| :=
    (mul_lt_mul_left hM).mpr hB
  have : B / N < 1 + |x₂| := by
    have : B / (N : ℚ) = (1 / (N : ℚ)) * B := by ring
    linarith [this ▸ hlt, key]
  linarith

/-! ## Why the constant is what it is

The descent of Theorem 3.6 produces, after `i` steps, a lower bound
`|x_{i+2}| > (M(MB-1) - i)/M`, and correspondingly an upper bound on `|y_{i+1}|`.
The argument closes because at the last step the remaining room is exactly `1 + M`,
which drives the final bound on `|y_n|` down to `M` itself, contradicting the
definition of `M` as an infimum over nonzero entries. Both facts are pure algebra in
`B`, and are checked here.
-/

/-- With `B = ((n-1) + 2M)/M²` one has `M(MB - 1) = (n-1) + M`. This is the identity
that makes the descent terminate after exactly the available number of rows. -/
theorem ch_key (M : ℚ) (hM : 0 < M) (n : ℚ) :
    M * (M * (((n - 1) + 2 * M) / M ^ 2) - 1) = (n - 1) + M := by
  have : M ≠ 0 := hM.ne'
  field_simp
  ring

/-- At the last step the room remaining is `1 + M`, and the resulting bound on the
final entry of the second row is exactly `M`. Since every nonzero entry has absolute
value at least `M`, that is the contradiction. -/
theorem ch_final (M : ℚ) (hM : 0 < M) (n : ℚ) :
    M / (((n - 1) + M) - (n - 2)) * (1 + M) = M := by
  have h : ((n - 1) + M) - (n - 2) = 1 + M := by ring
  rw [h]
  have : (1 : ℚ) + M ≠ 0 := by positivity
  field_simp

/-- **The descent step in full.** The diamond relation `x_i y_i = 1 + x_{i+1} y_{i-1}`,
together with a lower bound `M` on the current second-row entry and an upper bound `U`
on the previous one, converts a lower bound on `|x_i|` into a lower bound on
`|x_{i+1}|`. This is the inequality iterated in the proof of Theorem 3.6; the upper
bounds `U` are themselves produced by the same relation one row earlier, which is what
makes the induction a coupled one. -/
theorem ch_descent {M U xi xi1 yi yim1 : ℚ} (hM : 0 < M) (hU : 0 < U)
    (hyi : M ≤ |yi|) (hyU : |yim1| ≤ U)
    (h : xi * yi = 1 + xi1 * yim1) :
    M * |xi| - 1 ≤ |xi1| * U := by
  have hx : (0 : ℚ) ≤ |xi| := abs_nonneg _
  have h1 : |xi| * M ≤ |xi| * |yi| := mul_le_mul_of_nonneg_left hyi hx
  have h2 : |xi| * |yi| = |xi * yi| := (abs_mul _ _).symm
  have h3 : |xi * yi| = |1 + xi1 * yim1| := by rw [h]
  have h4 : |1 + xi1 * yim1| ≤ 1 + |xi1| * |yim1| := by
    calc |1 + xi1 * yim1| ≤ |(1 : ℚ)| + |xi1 * yim1| := abs_add _ _
      _ = 1 + |xi1| * |yim1| := by rw [abs_mul]; norm_num
  have h5 : |xi1| * |yim1| ≤ |xi1| * U := mul_le_mul_of_nonneg_left hyU (abs_nonneg _)
  have : M * |xi| ≤ 1 + |xi1| * U := by
    calc M * |xi| = |xi| * M := by ring
      _ ≤ |xi| * |yi| := h1
      _ = |1 + xi1 * yim1| := by rw [h2, h3]
      _ ≤ 1 + |xi1| * |yim1| := h4
      _ ≤ 1 + |xi1| * U := by linarith
  linarith

/-- The second-row entries are themselves bounded by the same relation, which supplies
the `U` consumed by `ch_descent` at the next step. -/
theorem ch_row_bound {xi xi1 yi yim1 : ℚ} (hxi : 0 < |xi|)
    (h : xi * yi = 1 + xi1 * yim1) :
    |yi| ≤ (1 + |xi1| * |yim1|) / |xi| := by
  rw [le_div_iff hxi]
  have : |yi| * |xi| = |xi * yi| := by rw [abs_mul]; ring
  rw [this, h]
  calc |1 + xi1 * yim1| ≤ |(1 : ℚ)| + |xi1 * yim1| := abs_add _ _
    _ = 1 + |xi1| * |yim1| := by rw [abs_mul]; norm_num

/-! ## The descent constants

The descent produces a chain of lower bounds `|x_{i+1}| > c i`. Unwinding the
recursion in the proof of Theorem 3.6, these constants form an arithmetic progression
of common difference `-1/M`, starting at `MB - 1`. The choice of `B` is exactly what
makes the chain arrive at the value `1` after `n` steps, and a frieze of height `n`
has `x_{n+1} = 1`, so the strict inequality `|x_{n+1}| > 1` is the contradiction.
-/

/-- The descent constants `c i = MB - 1 - (i-1)/M`. -/
def chC (M B : ℚ) (i : ℕ) : ℚ := M * B - 1 - ((i : ℚ) - 1) / M

/-- Each descent step costs exactly `1/M`. -/
theorem chC_step (M B : ℚ) (hM : M ≠ 0) (i : ℕ) :
    chC M B (i + 1) = chC M B i - 1 / M := by
  unfold chC
  push_cast
  field_simp
  ring

/-- **The choice of `B` is forced.** With `B = ((n-1) + 2M)/M²` the descent constants
arrive at exactly `1` after `n` steps. Since a frieze of height `n` has `x_{n+1} = 1`,
the descent yields `1 = |x_{n+1}| > 1`, which is absurd. Any smaller `B` would not
reach `1`, and any larger one would overshoot: the bound is the exact threshold. -/
theorem chC_terminal (M : ℚ) (hM : 0 < M) (n : ℚ) :
    M * (((n - 1) + 2 * M) / M ^ 2) - 1 - (n - 1) / M = 1 := by
  have : M ≠ 0 := hM.ne'
  field_simp
  ring

/-- The bound of Cuntz--Holm Theorem 3.6 specialised to `(1/N)ℤ`, where `M = 1/N`
and a frieze of width `n` has height `n - 3`. -/
def chBound (n N : ℕ) : ℚ := ((n : ℚ) - 4) * (N : ℚ) ^ 2 + 2 * (N : ℚ)

/-- The specialisation is arithmetically what the general formula gives. -/
theorem chBound_eq (n N : ℕ) (hN : 0 < N) :
    chBound n N = (((n : ℚ) - 3 - 1) + 2 * (1 / N)) / (1 / (N : ℚ)) ^ 2 := by
  have hNpos : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  unfold chBound
  field_simp
  ring

end VicoEnum
