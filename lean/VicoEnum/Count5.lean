/-
  VicoEnum/Count5.lean

  `T5 N` counts what Definition `def:count` counts.

  `def:count` counts positive rational friezes of width `n` with entries in `(1/N)ℤ`. It
  counts arrays, not quiddity cycles; the sentence "as sequences, not up to rotation" fixes
  that no quotient by rotation is taken, and says nothing about which object is counted.

  The caveat recorded in `Bijection.lean` is that `IsFrieze n` constrains rows `0` to `n` and
  leaves everything above free, so arrays satisfying it are a proper class of representatives
  rather than the friezes themselves. Definition `def:frieze` has the bounded domain
  `0 ≤ i-j ≤ n`, so the paper's width-5 frieze *is* its rows `0` to `5`. That is `rows5`
  below, and `Friezes5 N` is the set of those.

  The count then goes

      Friezes5 N  ←→  Pairs5 N  ←→  {W5 pairs},

  the left bijection by `frieze_rebuild` (a frieze is rebuilt from its first two quiddity
  entries) with injectivity from reading row `2` at columns `0` and `1`, the right one by
  `w5cond_converse` and `W5_of_frieze`. Hence `(Friezes5 N).ncard = T5 N`, and the two
  divisibility theorems are statements about `T(N,5)` itself.
-/
import VicoEnum.Bijection
import VicoEnum.Assemble
import VicoEnum.TenPrime

namespace VicoEnum

open Finset

/-- The rows that Definition `def:frieze` mentions at width `5`. Two arrays agreeing here
are the same frieze of the paper. -/
def rows5 (m : ℕ → ℤ → ℚ) : Fin 6 → ℤ → ℚ := fun r j => m r.val j

/-- The generating pairs: a width-5 quiddity cycle recorded by its first two entries. -/
def Pairs5 (N : ℕ) : Set (ℚ × ℚ) :=
  {x | IsPositiveFrieze 5 (friezeOf (quid5fn x.1 x.2)) ∧
    ∀ r j, r ≤ 5 → InLattice N (friezeOf (quid5fn x.1 x.2) r j)}

/-- **The friezes of Definition `def:frieze`** at width `5` over `(1/N)ℤ`. -/
def Friezes5 (N : ℕ) : Set (Fin 6 → ℤ → ℚ) :=
  {F | ∃ m, IsPositiveFrieze 5 m ∧ (∀ r j, r ≤ 5 → InLattice N (m r j)) ∧ F = rows5 m}

/-- A positive lattice element has a positive integer numerator. -/
theorem num_of_lattice {N : ℕ} (hN : 0 < N) {x : ℚ} (hx : 0 < x) (h : InLattice N x) :
    ∃ p : ℕ, 0 < p ∧ x = (p : ℚ) / N := by
  obtain ⟨k, hk⟩ := h
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hkpos : 0 < k := by
    rw [hk, lt_div_iff hNQ, zero_mul] at hx
    exact_mod_cast hx
  exact ⟨k.toNat, by omega, by rw [hk]; congr 1; exact_mod_cast (Int.toNat_of_nonneg hkpos.le).symm⟩

/-! ## Friezes and pairs -/

/-- **A frieze is its own rebuild, on every row Definition `def:frieze` mentions.** This is
`frieze_rebuild` with row `0` added, where both sides vanish. -/
theorem rebuild_agree {m : ℕ → ℤ → ℚ} (hm : IsPositiveFrieze 5 m) :
    ∀ r j, r ≤ 5 → friezeOf (quid5fn (quiddity m 0) (quiddity m 1)) r j = m r j := by
  intro r j hr
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · rw [friezeOf_zero, hm.1.row_zero]
  · exact frieze_rebuild hm.1 hm.2 r j hr1 hr

/-- **The friezes are the image of the pairs.** -/
theorem friezes5_eq_image {N : ℕ} :
    Friezes5 N = (fun x : ℚ × ℚ => rows5 (friezeOf (quid5fn x.1 x.2))) '' Pairs5 N := by
  ext F
  constructor
  · rintro ⟨m, hm, hlat, rfl⟩
    have hag := rebuild_agree hm
    refine ⟨(quiddity m 0, quiddity m 1), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · -- the rebuilt array is a frieze
      have hD : quiddity m 0 * quiddity m 1 - 1 = quiddity m 3 := by
        obtain ⟨e3, -, -⟩ := width5_from_frieze hm.1 hm.2; linarith [e3]
      have hDne : quiddity m 0 * quiddity m 1 - 1 ≠ 0 := by
        rw [hD]; exact (hm.2 2 3 (by omega) (by omega)).ne'
      exact width5_build hDne
    · intro r j h0 h5; rw [hag r j (by omega)]; exact hm.2 r j h0 h5
    · intro r j hr; rw [hag r j hr]; exact hlat r j hr
    · funext r j
      show friezeOf (quid5fn (quiddity m 0) (quiddity m 1)) r.val j = m r.val j
      exact hag r.val j (by omega)
  · rintro ⟨x, ⟨hfr, hlat⟩, rfl⟩
    exact ⟨friezeOf (quid5fn x.1 x.2), hfr, hlat, rfl⟩

/-- **The map to friezes is injective on pairs.** Row `2` at columns `0` and `1` returns the
pair. -/
theorem rows5_injOn {N : ℕ} :
    Set.InjOn (fun x : ℚ × ℚ => rows5 (friezeOf (quid5fn x.1 x.2))) (Pairs5 N) := by
  intro a _ b _ hab
  have h0 : quid5fn a.1 a.2 0 = quid5fn b.1 b.2 0 := congrFun (congrFun hab 2) 0
  have h1 : quid5fn a.1 a.2 1 = quid5fn b.1 b.2 1 := congrFun (congrFun hab 2) 1
  rw [q0 _ _ 0 (by norm_num), q0 _ _ 0 (by norm_num)] at h0
  rw [q1 _ _ 1 (by norm_num), q1 _ _ 1 (by norm_num)] at h1
  exact Prod.ext h0 h1

/-! ## Pairs and `W5` -/

/-- **The image characterisation.** `Pairs5` is the image of the counted `Finset` under
`(p,q) ↦ (p/N, q/N)`. -/
theorem pairs5_eq_image {N : ℕ} (hN : 0 < N) :
    Pairs5 N = (fun x : ℕ × ℕ => ((x.1 : ℚ) / N, (x.2 : ℚ) / N)) ''
      ↑((box5 N).filter (fun x => W5 N x.1 x.2)) := by
  ext x
  constructor
  · rintro ⟨⟨hfr, hpos⟩, hlat⟩
    have hl : ∀ j : ℤ, InLattice N (quid5fn x.1 x.2 j) := by
      intro j; have := hlat 2 j (by omega); simpa using this
    have hpospos : ∀ j : ℤ, 0 < quid5fn x.1 x.2 j := by
      intro j; have := hpos 2 j (by omega) (by omega); simpa using this
    obtain ⟨p, hp, hpe⟩ := num_of_lattice hN (hpospos 0) (hl 0)
    obtain ⟨q, hq, hqe⟩ := num_of_lattice hN (hpospos 1) (hl 1)
    obtain ⟨c2, -, hc2⟩ := num_of_lattice hN (hpospos 2) (hl 2)
    obtain ⟨d, -, hd⟩ := num_of_lattice hN (hpospos 3) (hl 3)
    obtain ⟨c4, -, hc4⟩ := num_of_lattice hN (hpospos 4) (hl 4)
    have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hW : W5 N p q := by
      refine W5_of_frieze hN hfr hpos (p := p) (q := q) (c₂ := c2) (d := d) (c₄ := c4)
        ?_ ?_ ?_ ?_ ?_ <;>
      · simp only [quiddity_friezeOf]
        first
          | (rw [hpe]; field_simp)
          | (rw [hqe]; field_simp)
          | (rw [hc2]; field_simp)
          | (rw [hd]; field_simp)
          | (rw [hc4]; field_simp)
    refine ⟨(p, q), ?_, ?_⟩
    · simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨mem_box5_of_W5 hN hW, hW⟩
    · have h0 : quid5fn x.1 x.2 0 = x.1 := q0 x.1 x.2 0 (by norm_num)
      have h1 : quid5fn x.1 x.2 1 = x.2 := q1 x.1 x.2 1 (by norm_num)
      rw [h0] at hpe; rw [h1] at hqe
      exact Prod.ext hpe.symm hqe.symm
  · rintro ⟨⟨p, q⟩, hmem, rfl⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hmem
    obtain ⟨-, hW⟩ := hmem
    obtain ⟨h1, h2, -, -⟩ := w5cond_converse hN hW
    exact ⟨h1, h2⟩

/-- The pairs are counted by `T5`. -/
theorem pairs5_ncard {N : ℕ} (hN : 0 < N) : (Pairs5 N).ncard = T5 N := by
  classical
  have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [pairs5_eq_image hN]
  rw [Set.ncard_image_of_injOn]
  · rw [Set.ncard_coe_Finset]; rfl
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    have hcan : ∀ x y : ℚ, x / (N : ℚ) = y / (N : ℚ) → x = y := by
      intro x y hxy
      have := congrArg (fun z : ℚ => z * (N : ℚ)) hxy
      simpa [div_mul_cancel₀, hNQ] using this
    exact Prod.ext (by exact_mod_cast hcan _ _ hab.1) (by exact_mod_cast hcan _ _ hab.2)

/-! ## The count -/

/-- **`T(N,5) = T5 N`.** The friezes of Definition `def:frieze` are counted by the `W5`
enumeration. -/
theorem friezes5_ncard {N : ℕ} (hN : 0 < N) : (Friezes5 N).ncard = T5 N := by
  rw [friezes5_eq_image, Set.ncard_image_of_injOn rows5_injOn, pairs5_ncard hN]

/-- **`5 ∣ T(N,5)`** for the count Definition `def:count` defines. -/
theorem five_dvd_friezes5 {N : ℕ} (hN : 0 < N) : 5 ∣ (Friezes5 N).ncard := by
  rw [friezes5_ncard hN]; exact five_dvd_T5 hN

/-- **`10 ∣ T(p,5)`** at a prime, for the same count. -/
theorem ten_dvd_friezes5_prime {p : ℕ} (hp : p.Prime) : 10 ∣ (Friezes5 p).ncard := by
  rw [friezes5_ncard hp.pos]; exact ten_dvd_T5_prime hp

end VicoEnum
