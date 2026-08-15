/-
  VicoEnum/Rigidity.lean

  Rigidity at a minimal quiddity entry.

  In the vector model of a positive frieze over `(1/N)ℤ`, a quiddity entry is
  `a_j = det(u_{j-1}, u_{j+1})/R`. If the frieze is primitive, so `R = N`, and
  `a_j = 1/N` takes the least value an entry can take, then
  `det(u_{j-1}, u_{j+1}) = 1`: the two neighbours form a unimodular pair. The two
  remaining conditions `det(u_{j-1}, u_j) = det(u_j, u_{j+1}) = N` then pin `u_j`
  down completely, with no freedom left at all.

  The proof is a telescoping pair of determinant identities: multiplying the two
  conditions by the coordinates of the neighbours and adding collapses everything
  onto `c·det(b,d) = c`.
-/
import VicoEnum.Basic

namespace VicoEnum

/-- Determinant of a pair of integer vectors. -/
def dt (b c : ℤ × ℤ) : ℤ := b.1 * c.2 - b.2 * c.1

@[simp] theorem dt_self (b : ℤ × ℤ) : dt b b = 0 := by unfold dt; ring

theorem dt_antisymm (b c : ℤ × ℤ) : dt b c = - dt c b := by unfold dt; ring

/-- **Rigidity at a minimal entry.** Let `b` and `d` be the neighbours of a vertex
`c`, with `det(b,d) = 1`, which is exactly what `a_j = 1/N` says for a primitive
frieze, and `det(b,c) = det(c,d) = N`. Then `c = N·b + N·d`: in the basis `(b,d)`
the middle vector is `(N,N)`, with no remaining freedom. -/
theorem rigidity {b c d : ℤ × ℤ} {N : ℤ}
    (hbd : dt b d = 1) (hbc : dt b c = N) (hcd : dt c d = N) :
    c = (N * b.1 + N * d.1, N * b.2 + N * d.2) := by
  have hbd' : b.1 * d.2 - b.2 * d.1 = 1 := hbd
  have hbc' : b.1 * c.2 - b.2 * c.1 = N := hbc
  have hcd' : c.1 * d.2 - c.2 * d.1 = N := hcd
  have c1 : c.1 = N * b.1 + N * d.1 := by
    linear_combination d.1 * hbc' + b.1 * hcd' - c.1 * hbd'
  have c2 : c.2 = N * b.2 + N * d.2 := by
    linear_combination d.2 * hbc' + b.2 * hcd' - c.2 * hbd'
  exact Prod.ext c1 c2

/-- Consequence: the middle vector is determined by its neighbours, so two vertices
with the same unimodular neighbour pair and the same `N` coincide. -/
theorem rigidity_unique {b c c' d : ℤ × ℤ} {N : ℤ}
    (hbd : dt b d = 1)
    (hbc : dt b c = N) (hcd : dt c d = N)
    (hbc' : dt b c' = N) (hcd' : dt c' d = N) :
    c = c' := by
  rw [rigidity hbd hbc hcd, rigidity hbd hbc' hcd']

end VicoEnum
