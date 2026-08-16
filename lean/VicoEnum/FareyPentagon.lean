/-
  VicoEnum/FareyPentagon.lean

  The explicit map from a frieze to a path in a Farey graph.

  In the classification cited in the paper, `F_R` is the directed graph whose vertices
  are integer pairs `(a,b)` with `gcd(a,b)` a factor of `R`, with a directed edge from
  `(a,b)` to `(c,d)` when `ad - bc = R`, and the frieze attached to a path is given by
  `m_{ij} = (1/R)(a_j b_i - b_j a_i)`.

  Everything the correspondence needs about the path is proved here directly, as an
  explicit construction rather than as a count.

  * `fpath` builds the vertex sequence from the quiddity by `v_{i+1} = c_i v_i - v_{i-1}`.
  * `fpath_det` shows every edge of that sequence has the *same* determinant as the first.
    So a single edge check puts the whole path in one graph `F_R`; this is the structural
    reason the construction lands in `F_R` at all.
  * `pentagon_closes` shows the width-five path closes antipodally after five steps,
    `v₅ = -v₀` and `v₆ = -v₁`, which is the monodromy `-I` of `frieze5_monodromy` read on
    vertices, and is the antipodal identification used to view `F_R` in the plane.

  Composing with `cubic_to_W5` sends a solution of Ford's cubic to an explicit closed
  five-vertex path with all five edge determinants equal. No cardinality argument is used
  anywhere in this file.
-/
import VicoEnum.Param

namespace VicoEnum

/-- The determinant pairing on vertices, the quantity that decides Farey adjacency:
`(a,b)` has a directed edge to `(c,d)` in `F_R` exactly when `fdet (a,b) (c,d) = R`. -/
def fdet (u w : ℤ × ℤ) : ℤ := u.1 * w.2 - u.2 * w.1

/-- One step of the path recurrence leaves the determinant unchanged. This single ring
identity is what forces the whole path into a single Farey graph. -/
theorem fdet_step (c : ℤ) (u w : ℤ × ℤ) :
    fdet w (c * w.1 - u.1, c * w.2 - u.2) = fdet u w := by
  simp only [fdet]; ring

/-- The vertex sequence of a quiddity: `v_{i+2} = c_i v_{i+1} - v_i`. -/
def fpath (v₀ v₁ : ℤ × ℤ) (c : ℕ → ℤ) : ℕ → ℤ × ℤ
  | 0 => v₀
  | 1 => v₁
  | (n + 2) =>
      (c n * (fpath v₀ v₁ c (n + 1)).1 - (fpath v₀ v₁ c n).1,
       c n * (fpath v₀ v₁ c (n + 1)).2 - (fpath v₀ v₁ c n).2)

/-- **Every edge of the path has the same determinant.** Consequently, if the first edge
is an edge of `F_R`, then so is every later edge: the construction lands in one Farey
graph, and which graph is decided by the single number `fdet v₀ v₁`. -/
theorem fpath_det (v₀ v₁ : ℤ × ℤ) (c : ℕ → ℤ) :
    ∀ i, fdet (fpath v₀ v₁ c i) (fpath v₀ v₁ c (i + 1)) = fdet v₀ v₁ := by
  intro i
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [show fpath v₀ v₁ c (n + 1 + 1) =
        (c n * (fpath v₀ v₁ c (n + 1)).1 - (fpath v₀ v₁ c n).1,
         c n * (fpath v₀ v₁ c (n + 1)).2 - (fpath v₀ v₁ c n).2) from rfl]
      rw [fdet_step]
      exact ih

/-- **The width-five path closes antipodally.** Running the recurrence with the width-five
quiddity `(a₀, a₁, (a₀+1)/D, D, (a₁+1)/D)`, `D = a₀a₁ - 1`, returns to the negative of the
starting pair after five steps. This is the monodromy `-I` of `frieze5_monodromy` read on
vertices; it is what makes the five vertices a *closed* pentagon in the antipodal quotient
of `F_R`.

The statement is for a single coordinate; the recurrence acts on the two coordinates of a
vertex independently, so this gives `v₅ = -v₀` and `v₆ = -v₁`. -/
theorem pentagon_closes {K : Type*} [Field K] (a₀ a₁ x₀ x₁ : K) (hD : a₀ * a₁ - 1 ≠ 0) :
    let x₂ := (a₀ + 1) / (a₀ * a₁ - 1) * x₁ - x₀
    let x₃ := (a₀ * a₁ - 1) * x₂ - x₁
    let x₄ := (a₁ + 1) / (a₀ * a₁ - 1) * x₃ - x₂
    let x₅ := a₀ * x₄ - x₃
    let x₆ := a₁ * x₅ - x₄
    x₅ = -x₀ ∧ x₆ = -x₁ := by
  intro x₂ x₃ x₄ x₅ x₆
  have h₂ : x₂ = (a₀ + 1) / (a₀ * a₁ - 1) * x₁ - x₀ := rfl
  have h₃ : x₃ = (a₀ * a₁ - 1) * x₂ - x₁ := rfl
  have h₄ : x₄ = (a₁ + 1) / (a₀ * a₁ - 1) * x₃ - x₂ := rfl
  have h₅ : x₅ = a₀ * x₄ - x₃ := rfl
  have h₆ : x₆ = a₁ * x₅ - x₄ := rfl
  constructor
  · rw [h₅, h₄, h₃, h₂]; field_simp; ring
  · rw [h₆, h₅, h₄, h₃, h₂]; field_simp; ring

/-- The two intermediate vertices of the pentagon carry no denominators: `x₃` and `x₄` are
polynomial in `a₀`, `a₁` and the starting pair. -/
theorem pentagon_mid (a₀ a₁ x₀ x₁ : ℚ) (hD : a₀ * a₁ - 1 ≠ 0) :
    (a₀ * a₁ - 1) * ((a₀ + 1) / (a₀ * a₁ - 1) * x₁ - x₀) - x₁
        = a₀ * x₁ - (a₀ * a₁ - 1) * x₀ ∧
      (a₁ + 1) / (a₀ * a₁ - 1)
          * ((a₀ * a₁ - 1) * ((a₀ + 1) / (a₀ * a₁ - 1) * x₁ - x₀) - x₁)
        - ((a₀ + 1) / (a₀ * a₁ - 1) * x₁ - x₀) = x₁ - a₁ * x₀ := by
  constructor <;> field_simp <;> ring

end VicoEnum
