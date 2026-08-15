/-
  VicoEnum/CwBridge.lean

  `Cw` is the numerator continuant of a frieze.

  `GeneralWidth.lean` opens by saying `K_k(a_i,…) = Cw N p i k / N^k`, and until now that was
  a comment. `Cw_desnanot` and `dj_windows` speak about the `Cw` recursion with no stated
  relation to a frieze; this file states the relation. Note that `general_reduction` and
  `general_hrel` do NOT mention `Cw` at all, so this file does nothing for them: they quantify
  over free integers, and `general_reduction_Cw` is what ties them to the windows.

  The identification is a two-step induction: both sides satisfy the same three-term
  recursion, and the `N^2` in `Cw` is exactly what clearing one denominator from each of the
  two previous terms produces. `Glide.lean` carries the same identity for its own copy `Kr` of
  the continuant, as `Kr_homog`; that copy is ℕ-indexed and is not the one `IsFrieze` uses.
-/
import VicoEnum.Frieze

namespace VicoEnum

/-- **The numerator continuant.** If `p i = N a_i` then `Cw N p i k = N^k K_k(a_i, …)`. -/
theorem Cw_eq_pow_mul_Kc {N : ℤ} {a : ℤ → ℚ} {p : ℕ → ℤ}
    (hp : ∀ i : ℕ, (p i : ℚ) = (N : ℚ) * a i) (i : ℕ) :
    ∀ k, ((Cw N p i k : ℤ) : ℚ) = (N : ℚ) ^ k * Kc a (i : ℤ) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [Cw, Kc]
    | 1 => simpa [Cw, Kc] using hp i
    | (m + 2) =>
      have h1 := ih (m + 1) (by omega)
      have h2 := ih m (by omega)
      show ((p (i + m + 1) * Cw N p i (m + 1) - N ^ 2 * Cw N p i m : ℤ) : ℚ) = _
      push_cast
      rw [h1, h2, hp (i + m + 1), Kc_succ_succ]
      have hidx : ((i + m + 1 : ℕ) : ℤ) = (i : ℤ) + m + 1 := by push_cast; ring
      rw [hidx]
      ring

/-- **Every frieze entry, in numerator form.** For `1 ≤ r ≤ n` the entry `m r j` at a column
`j ≥ 0` satisfies `Cw N p j (r-1) = N^{r-1} m r j`, so the `Cw` recursion of `GeneralWidth`
is the recursion the frieze entries actually satisfy. -/
theorem Cw_eq_entry {N : ℤ} {n : ℕ} {m : ℕ → ℤ → ℚ} (hm : IsFrieze n m)
    (hpos : ∀ r j, 0 < r → r < n → 0 < m r j) {p : ℕ → ℤ}
    (hp : ∀ i : ℕ, (p i : ℚ) = (N : ℚ) * quiddity m i) (r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n)
    (j : ℕ) :
    ((Cw N p j (r - 1) : ℤ) : ℚ) = (N : ℚ) ^ (r - 1) * m r (j : ℤ) := by
  rw [Cw_eq_pow_mul_Kc hp j (r - 1), entry_eq_continuant hm hpos r hr1 hrn (j : ℤ)]

end VicoEnum
