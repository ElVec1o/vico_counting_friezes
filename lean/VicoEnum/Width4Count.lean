/-
  VicoEnum/Width4Count.lean

  Theorem `thm:w4` for the friezes themselves.

  `Width4.lean` proves `width4_card` by an independent matrix route, counting the set of
  admissible FIRST ENTRIES
  `{a : 0 < a, a and 2/a in (1/N)Z}`. That is a set of rationals, not a set of friezes, and
  the paper's table recorded the gap. This file closes it, counting the arrays that
  Definition `def:frieze` defines, by the route `Count5.lean` uses at width 5.

  Width four is rigid. Row `3` is the top row and is constant `1`, and by `eq:rec` it is
  `a_j a_{j+1} - 1`, so `a_j a_{j+1} = 2` at every column. That forces period `2`: from
  `a_j a_{j+1} = 2 = a_{j+1} a_{j+2}` and `a_{j+1} ≠ 0` we get `a_j = a_{j+2}`. So the whole
  quiddity is `(a, 2/a, a, 2/a)` and the frieze has one parameter, recovered from row `2` at
  column `0`. Over `(1/N)Z` with `a = p/N` the lattice condition is `p | 2N^2`, so the count
  is `d(2N^2)`.
-/
import VicoEnum.Count5

namespace VicoEnum

open Finset

/-! ## The one-parameter quiddity -/

/-- The width-4 quiddity `(a, 2/a, a, 2/a)`, which has period `2`. -/
noncomputable def quid4fn (a0 : ℚ) : ℤ → ℚ := fun j => if j % 2 = 0 then a0 else 2 / a0

theorem quid4fn_periodic (a0 : ℚ) (j : ℤ) : quid4fn a0 (j + 4) = quid4fn a0 j := by
  simp only [quid4fn, show (j + 4) % 2 = j % 2 from by omega]

theorem quid4fn_two_periodic (a0 : ℚ) (j : ℤ) : quid4fn a0 (j + 2) = quid4fn a0 j := by
  simp only [quid4fn, show (j + 2) % 2 = j % 2 from by omega]

theorem q4even (a0 : ℚ) (j : ℤ) (h : j % 2 = 0) : quid4fn a0 j = a0 := by simp [quid4fn, h]
theorem q4odd (a0 : ℚ) (j : ℤ) (h : j % 2 = 1) : quid4fn a0 j = 2 / a0 := by
  simp only [quid4fn, h]; norm_num

/-- **The product of consecutive entries is `2`.** -/
theorem quid4fn_prod {a0 : ℚ} (ha : a0 ≠ 0) (j : ℤ) :
    quid4fn a0 (j + 1) * quid4fn a0 j = 2 := by
  rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with h | h
  · rw [q4even a0 j h, q4odd a0 (j + 1) (by omega)]; field_simp
  · rw [q4odd a0 j h, q4even a0 (j + 1) (by omega)]; field_simp

/-- **`K₂ = 1`**, the closing condition at width `4`. -/
theorem quid4fn_K2 {a0 : ℚ} (ha : a0 ≠ 0) (j : ℤ) : Kc (quid4fn a0) j 2 = 1 := by
  rw [Kc_two, quid4fn_prod ha j]; norm_num

/-- **`K₃ = 0`**, the other closing condition. -/
theorem quid4fn_K3 {a0 : ℚ} (ha : a0 ≠ 0) (j : ℤ) : Kc (quid4fn a0) j 3 = 0 := by
  rw [Kc_three, quid4fn_prod ha j, quid4fn_two_periodic]
  ring

/-- **The construction.** -/
theorem width4_build {a0 : ℚ} (ha : a0 ≠ 0) : IsFrieze 4 (friezeOf (quid4fn a0)) := by
  refine friezeOf_isFrieze (by omega) ?_ (fun j => quid4fn_K2 ha j) (fun j => quid4fn_K3 ha j)
  intro j
  have h4 : ((4 : ℕ) : ℤ) = 4 := by norm_num
  rw [h4]
  exact quid4fn_periodic a0 j

theorem quid4fn_pos {a0 : ℚ} (ha : 0 < a0) (j : ℤ) : 0 < quid4fn a0 j := by
  rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with h | h
  · rw [q4even a0 j h]; exact ha
  · rw [q4odd a0 j h]; positivity

theorem width4_build_positive {a0 : ℚ} (ha : 0 < a0) :
    IsPositiveFrieze 4 (friezeOf (quid4fn a0)) := by
  refine ⟨width4_build ha.ne', ?_⟩
  intro r j h0 h4
  rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl
  · exact one_pos
  · exact quid4fn_pos ha j
  · show 0 < Kc (quid4fn a0) j 2
    rw [quid4fn_K2 ha.ne' j]; norm_num

/-! ## The converse: a width-4 frieze has this quiddity -/

/-- **From `IsFrieze`.** A positive width-4 frieze satisfies `a_j a_{j+1} = 2`. The
corresponding statement from Definition `def:frieze` directly, with no periodicity assumed,
is `pf4_prod` below. -/
theorem width4_prod {m : ℕ → ℤ → ℚ} (hm : IsPositiveFrieze 4 m) (j : ℤ) :
    quiddity m (j + 1) * quiddity m j = 2 := by
  have h3 : m 3 j = 1 := hm.1.row_top_one j
  have he := entry_eq_continuant hm.1 hm.2 3 (by omega) (by omega) j
  rw [he, Kc_two] at h3
  linarith [h3]

/-- The quiddity has period `2`. -/
theorem width4_period {m : ℕ → ℤ → ℚ} (hm : IsPositiveFrieze 4 m) (j : ℤ) :
    quiddity m (j + 2) = quiddity m j := by
  have h1 := width4_prod hm j
  have h2 := width4_prod hm (j + 1)
  have hne : quiddity m (j + 1) ≠ 0 := (hm.2 2 (j + 1) (by omega) (by omega)).ne'
  have : quiddity m (j + 1 + 1) * quiddity m (j + 1) = quiddity m (j + 1) * quiddity m j := by
    rw [h2, h1]
  have h3 : j + 1 + 1 = j + 2 := by ring
  rw [h3] at this
  exact mul_right_cancel₀ hne (by linarith [this])

/-- **The quiddity is `quid4fn` of its first entry.** -/
theorem width4_quid {m : ℕ → ℤ → ℚ} (hm : IsPositiveFrieze 4 m) (j : ℤ) :
    quiddity m j = quid4fn (quiddity m 0) j := by
  have hne : quiddity m 0 ≠ 0 := (hm.2 2 0 (by omega) (by omega)).ne'
  have hper : ∀ k : ℤ, quiddity m (k + 2) = quiddity m k := width4_period hm
  have h1 : quiddity m 1 = 2 / quiddity m 0 := by
    have h0 := width4_prod hm 0
    norm_num at h0
    field_simp
    linarith [h0]
  have hmod : quiddity m j = quiddity m (j % 2) := by
    have hit : ∀ (i : ℤ) (k : ℤ), quiddity m (k + i * 2) = quiddity m k := by
      intro i
      induction i using Int.induction_on with
      | hz => intro k; simp
      | hp n ih =>
        intro k
        have e : k + ((n : ℤ) + 1) * 2 = (k + n * 2) + 2 := by ring
        rw [e, hper, ih]
      | hn n ih =>
        intro k
        have e : k + (-(n : ℤ) - 1) * 2 = (k + (-(n : ℤ)) * 2) - 2 := by ring
        rw [e]
        have := hper (k + (-(n : ℤ)) * 2 - 2)
        rw [show k + (-(n : ℤ)) * 2 - 2 + 2 = k + (-(n : ℤ)) * 2 from by ring] at this
        rw [← this]; exact ih k
    have h := hit (j / 2) (j % 2)
    rw [show j % 2 + j / 2 * 2 = j from by omega] at h
    exact h
  rw [hmod]
  rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with h | h
  · rw [h, q4even _ j h]
  · rw [h, q4odd _ j h, h1]

/-! ## The lattice condition -/

/-- **The lattice condition.** With `a₀ = p/N`, every quiddity entry lies in `(1/N)ℤ` exactly
when `p ∣ 2N²`. The even columns are `p/N` and give nothing; the odd ones are `2N/p`. -/
theorem quid4fn_lattice {N p : ℕ} (hN : 0 < N) (hp : 0 < p) :
    (∀ j : ℤ, InLattice N (quid4fn ((p : ℚ) / N) j)) ↔ p ∣ 2 * N ^ 2 := by
  have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpQ : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h 1
    rw [q4odd _ 1 (by norm_num)] at hk
    have : (2 : ℚ) * N ^ 2 = (k : ℚ) * p := by
      field_simp at hk
      linarith [hk]
    have hZ : (2 : ℤ) * (N : ℤ) ^ 2 = (k : ℤ) * p := by exact_mod_cast this
    have hdZ : ((p : ℤ)) ∣ ((2 * N ^ 2 : ℕ) : ℤ) := by
      refine ⟨k, ?_⟩; push_cast; linarith [hZ]
    exact_mod_cast hdZ
  · rintro ⟨c, hc⟩ j
    rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with h | h
    · rw [q4even _ j h]; exact ⟨p, by push_cast; ring⟩
    · rw [q4odd _ j h]
      refine ⟨c, ?_⟩
      have hcQ : (2 : ℚ) * (N : ℚ) ^ 2 = (p : ℚ) * c := by exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hc
      field_simp
      linarith [hcQ]

/-! ## The count -/

/-- The rows Definition `def:frieze` mentions at width `4`. -/
def rows4 (m : ℕ → ℤ → ℚ) : Fin 5 → ℤ → ℚ := fun r j => m r.val j

/-- **The friezes of Definition `def:frieze`** at width `4` over `(1/N)ℤ`. -/
def Friezes4 (N : ℕ) : Set (Fin 5 → ℤ → ℚ) :=
  {F | ∃ m, IsPositiveFrieze 4 m ∧ (∀ r j, r ≤ 4 → InLattice N (m r j)) ∧ F = rows4 m}

/-- A width-4 frieze is its own rebuild, on every row `def:frieze` mentions. -/
theorem rebuild4 {m : ℕ → ℤ → ℚ} (hm : IsPositiveFrieze 4 m) :
    ∀ r j, r ≤ 4 → friezeOf (quid4fn (quiddity m 0)) r j = m r j := by
  have hne : quiddity m 0 ≠ 0 := (hm.2 2 0 (by omega) (by omega)).ne'
  have hpos0 : 0 < quiddity m 0 := hm.2 2 0 (by omega) (by omega)
  intro r j hr
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · rw [friezeOf_zero, hm.1.row_zero]
  · refine frieze_determined (width4_build hne) hm.1 (width4_build_positive hpos0).2 hm.2
      ?_ r j hr1 hr
    intro k
    show quid4fn (quiddity m 0) k = quiddity m k
    exact (width4_quid hm k).symm

/-- **The friezes are the image of the divisors of `2N²`.** -/
theorem friezes4_eq_image {N : ℕ} (hN : 0 < N) :
    Friezes4 N = (fun p : ℕ => rows4 (friezeOf (quid4fn ((p : ℚ) / N)))) ''
      ↑(2 * N ^ 2).divisors := by
  have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  ext F
  constructor
  · rintro ⟨m, hm, hlat, rfl⟩
    have hpos0 : 0 < quiddity m 0 := hm.2 2 0 (by omega) (by omega)
    obtain ⟨p, hp, hpe⟩ := num_of_lattice hN hpos0 (hlat 2 0 (by omega))
    have hq : ∀ j : ℤ, InLattice N (quid4fn ((p : ℚ) / N) j) := by
      intro j
      rw [← hpe, ← width4_quid hm j]
      exact hlat 2 j (by omega)
    refine ⟨p, ?_, ?_⟩
    · simp only [Finset.coe_sort_coe, Finset.mem_coe, Nat.mem_divisors]
      exact ⟨(quid4fn_lattice hN hp).mp hq, by positivity⟩
    · funext r j
      show friezeOf (quid4fn ((p : ℚ) / N)) r.val j = m r.val j
      rw [← hpe]
      exact rebuild4 hm r.val j (by omega)
  · rintro ⟨p, hmem, rfl⟩
    simp only [Finset.mem_coe, Nat.mem_divisors] at hmem
    have hp : 0 < p := Nat.pos_of_dvd_of_pos hmem.1 (by positivity)
    have hpQ : (0 : ℚ) < (p : ℚ) / N := by
      have : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
      positivity
    refine ⟨friezeOf (quid4fn ((p : ℚ) / N)), width4_build_positive hpQ, ?_, rfl⟩
    intro r j hr
    have hq := (quid4fn_lattice hN hp).mpr hmem.1
    have hone : InLattice N (1 : ℚ) := ⟨(N : ℤ), by push_cast; field_simp⟩
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact hone
    · exact hq j
    · show InLattice N (Kc (quid4fn ((p : ℚ) / N)) j 2)
      rw [quid4fn_K2 hpQ.ne' j]; exact hone
    · show InLattice N (Kc (quid4fn ((p : ℚ) / N)) j 3)
      rw [quid4fn_K3 hpQ.ne' j]; exact ⟨0, by simp⟩

/-- The map is injective: `p` is read off row `2` at column `0`. -/
theorem rows4_injOn {N : ℕ} (hN : 0 < N) :
    Set.InjOn (fun p : ℕ => rows4 (friezeOf (quid4fn ((p : ℚ) / N)))) ↑(2 * N ^ 2).divisors := by
  have hNQ : ((N : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  intro a _ b _ hab
  have h0 : quid4fn ((a : ℚ) / N) 0 = quid4fn ((b : ℚ) / N) 0 := congrFun (congrFun hab 2) 0
  rw [q4even _ 0 (by norm_num), q4even _ 0 (by norm_num)] at h0
  field_simp at h0
  exact_mod_cast h0

/-- **Theorem `thm:w4`.** `T(N,4) = d(2N²)`. -/
theorem friezes4_ncard {N : ℕ} (hN : 0 < N) :
    (Friezes4 N).ncard = (2 * N ^ 2).divisors.card := by
  rw [friezes4_eq_image hN, Set.ncard_image_of_injOn (rows4_injOn hN), Set.ncard_coe_Finset]

/-! ## Definition `def:frieze` at width four

`IsFrieze` carries a `periodic` field; Definition `def:frieze` does not. At width 5 that gap
is closed by `PaperDef.lean`, where `pf_period` shows periodicity is a consequence. The same
must be done here, or `Friezes4` is a subset of what `def:count` counts and `friezes4_ncard`
gives only one inequality.

At width four it is shorter. The diamond at `r = 2` with rows `1` and `3` constant reads
`a_j a_{j+1} = 2` directly, and period `2` follows by cancelling `a_{j+1}`. -/

/-- Definition `def:frieze` at width `4`, over `(1/N)ℤ`, written literally: rows `0` and `4`
zero, rows `1` and `3` one, the paper's diamond at every `(i,j)` whose four entries lie in
the strip `0 ≤ i-j ≤ 4`, positivity of the interior, lattice. NO periodicity is assumed. -/
structure PaperFrieze4 (N : ℕ) (F : Fin 5 → ℤ → ℚ) : Prop where
  z0 : ∀ j, F 0 j = 0
  o1 : ∀ j, F 1 j = 1
  o3 : ∀ j, F 3 j = 1
  z4 : ∀ j, F 4 j = 0
  d1 : ∀ j, F 1 j * F 1 (j + 1) - F 0 (j + 1) * F 2 j = 1
  d2 : ∀ j, F 2 j * F 2 (j + 1) - F 1 (j + 1) * F 3 j = 1
  d3 : ∀ j, F 3 j * F 3 (j + 1) - F 2 (j + 1) * F 4 j = 1
  p2 : ∀ j, 0 < F 2 j
  lat : ∀ r j, InLattice N (F r j)

variable {N : ℕ} {F : Fin 5 → ℤ → ℚ}

/-- **The product of consecutive quiddity entries is `2`**, from the paper's conditions
alone. -/
theorem pf4_prod (h : PaperFrieze4 N F) (j : ℤ) : F 2 j * F 2 (j + 1) = 2 := by
  have := h.d2 j; rw [h.o1 (j + 1), h.o3 j] at this; linarith

/-- **The quiddity is `2`-periodic.** Not assumed: derived from Definition `def:frieze`. So
the `periodic` field of `IsFrieze` is not an extra restriction at width `4`. -/
theorem pf4_period (h : PaperFrieze4 N F) (j : ℤ) : F 2 (j + 2) = F 2 j := by
  have h1 := pf4_prod h j
  have h2 := pf4_prod h (j + 1)
  have hne : F 2 (j + 1) ≠ 0 := (h.p2 (j + 1)).ne'
  have e : j + 1 + 1 = j + 2 := by ring
  rw [e] at h2
  exact mul_left_cancel₀ hne (by linarith [h1, h2])

/-- The quiddity is `quid4fn` of its first entry. -/
theorem pf4_quid (h : PaperFrieze4 N F) (j : ℤ) : F 2 j = quid4fn (F 2 0) j := by
  have hne : F 2 0 ≠ 0 := (h.p2 0).ne'
  have hper : ∀ k : ℤ, F 2 (k + 2) = F 2 k := pf4_period h
  have h1 : F 2 1 = 2 / F 2 0 := by
    have h0 := pf4_prod h 0
    norm_num at h0
    field_simp
    linarith [h0]
  have hmod : F 2 j = F 2 (j % 2) := by
    have hit : ∀ (i : ℤ) (k : ℤ), F 2 (k + i * 2) = F 2 k := by
      intro i
      induction i using Int.induction_on with
      | hz => intro k; simp
      | hp n ih =>
        intro k
        have e : k + ((n : ℤ) + 1) * 2 = (k + n * 2) + 2 := by ring
        rw [e, hper, ih]
      | hn n ih =>
        intro k
        have e : k + (-(n : ℤ) - 1) * 2 = (k + (-(n : ℤ)) * 2) - 2 := by ring
        rw [e]
        have := hper (k + (-(n : ℤ)) * 2 - 2)
        rw [show k + (-(n : ℤ)) * 2 - 2 + 2 = k + (-(n : ℤ)) * 2 from by ring] at this
        rw [← this]; exact ih k
    have hh := hit (j / 2) (j % 2)
    rw [show j % 2 + j / 2 * 2 = j from by omega] at hh
    exact hh
  rw [hmod]
  rcases (by omega : j % 2 = 0 ∨ j % 2 = 1) with hj | hj
  · rw [hj, q4even _ j hj]
  · rw [hj, q4odd _ j hj, h1]

/-- **Every paper frieze is in `Friezes4 N`.** No periodicity assumed. -/
theorem paperFrieze4_mem (h : PaperFrieze4 N F) : F ∈ Friezes4 N := by
  have hpos : (0 : ℚ) < F 2 0 := h.p2 0
  have hlatq : ∀ j : ℤ, InLattice N (quid4fn (F 2 0) j) := by
    intro j; rw [← pf4_quid h j]; exact h.lat 2 j
  refine ⟨friezeOf (quid4fn (F 2 0)), width4_build_positive hpos, ?_, ?_⟩
  · intro r j hr
    have hone : InLattice N (1 : ℚ) := by
      have := h.lat 1 j; rwa [h.o1 j] at this
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact hone
    · exact hlatq j
    · show InLattice N (Kc (quid4fn (F 2 0)) j 2)
      rw [quid4fn_K2 hpos.ne' j]; exact hone
    · show InLattice N (Kc (quid4fn (F 2 0)) j 3)
      rw [quid4fn_K3 hpos.ne' j]; exact ⟨0, by simp⟩
  · funext r j
    obtain ⟨v, hv⟩ := r
    show F ⟨v, hv⟩ j = friezeOf (quid4fn (F 2 0)) v j
    interval_cases v
    · exact h.z0 j
    · exact h.o1 j
    · exact pf4_quid h j
    · show F 3 j = Kc (quid4fn (F 2 0)) j 2
      rw [quid4fn_K2 hpos.ne' j]; exact h.o3 j
    · show F 4 j = Kc (quid4fn (F 2 0)) j 3
      rw [quid4fn_K3 hpos.ne' j]; exact h.z4 j

/-- The other inclusion. -/
theorem mem_paperFrieze4 (hF : F ∈ Friezes4 N) : PaperFrieze4 N F := by
  obtain ⟨m, hm, hlat, rfl⟩ := hF
  have d : ∀ r j, 2 ≤ r → r ≤ 4 →
      m (r - 2) (j + 1) * m r j = m (r - 1) j * m (r - 1) (j + 1) - 1 :=
    fun r j h2 h4 => hm.1.diamond r j h2 h4
  refine ⟨fun j => hm.1.row_zero j, fun j => hm.1.row_one j, fun j => hm.1.row_top_one j,
    fun j => hm.1.row_top_zero j, ?_, ?_, ?_,
    fun j => hm.2 2 j (by omega) (by omega), fun r j => hlat (r : ℕ) j (by omega)⟩
  · intro j; have hh := d 2 j (by omega) (by omega); norm_num at hh
    show m 1 j * m 1 (j + 1) - m 0 (j + 1) * m 2 j = (1 : ℚ); linarith
  · intro j; have hh := d 3 j (by omega) (by omega); norm_num at hh
    show m 2 j * m 2 (j + 1) - m 1 (j + 1) * m 3 j = (1 : ℚ); linarith
  · intro j; have hh := d 4 j (by omega) (by omega); norm_num at hh
    show m 3 j * m 3 (j + 1) - m 2 (j + 1) * m 4 j = (1 : ℚ); linarith

/-- **`Friezes4 N` is exactly the set Definition `def:count` counts at width `4`.** -/
theorem friezes4_eq_paper :
    Friezes4 N = {F : Fin 5 → ℤ → ℚ | PaperFrieze4 N F} :=
  Set.eq_of_subset_of_subset (fun _ hF => mem_paperFrieze4 hF)
    (fun _ hF => paperFrieze4_mem hF)

/-- **Theorem `thm:w4` on the paper's own definition.** `T(N,4) = d(2N²)`. -/
theorem paper_count4 {N : ℕ} (hN : 0 < N) :
    {F : Fin 5 → ℤ → ℚ | PaperFrieze4 N F}.ncard = (2 * N ^ 2).divisors.card := by
  rw [← friezes4_eq_paper]; exact friezes4_ncard hN

end VicoEnum
