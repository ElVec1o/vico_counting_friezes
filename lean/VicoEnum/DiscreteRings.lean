/-
  VicoEnum/DiscreteRings.lean

  Why the setting is a lattice and not a subring.

  Cuntz and Holm prove finiteness for friezes over any discrete subset of the complex
  numbers, which raises the question of counting friezes over discrete subrings other than
  the integers. Over the reals there are none.

  `discrete_subring_real`: a subring of R whose nonzero elements are bounded away from 0 is
  exactly Z. The fractional part of any element lies in the subring and is below 1, so its
  powers tend to 0 while remaining nonzero, contradicting discreteness unless it vanishes.

  So positive friezes over a discrete subring of R are Conway-Coxeter friezes over Z, and
  there is no further ring to generalise to. The generalisation that does exist is to
  lattices: `lattice_mul_closed_iff` records that (1/N)Z is closed under multiplication only
  for N = 1, so it is a Z-module and not a ring, which is exactly the setting of this
  project.

  Over C discrete subrings do exist, the imaginary quadratic orders among them, but positivity
  is not defined there, so the question changes rather than generalises. Real quadratic rings
  such as Z[sqrt 2] are dense in R, so they are not discrete and the finiteness of Cuntz and
  Holm does not apply to them.
-/
import VicoEnum.Monodromy
namespace VicoEnum

/-- **The only discrete subring of `ℝ` is `ℤ`.** If a subring of the reals has its nonzero
elements bounded away from `0`, it is exactly the integers. -/
theorem discrete_subring_real (S : Subring ℝ) {ε : ℝ} (hε : 0 < ε)
    (hdisc : ∀ x ∈ S, x ≠ 0 → ε ≤ |x|) :
    (S : Set ℝ) = Set.range ((↑) : ℤ → ℝ) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_range]
  constructor
  · intro hx
    -- the fractional part lies in S and is < 1, so it must vanish
    have hfl : ((⌊x⌋ : ℤ) : ℝ) ∈ S := coe_int_mem S _
    have hy : x - ((⌊x⌋ : ℤ) : ℝ) ∈ S := S.sub_mem hx hfl
    set y := x - ((⌊x⌋ : ℤ) : ℝ) with hydef
    have h0 : 0 ≤ y := by rw [hydef]; linarith [Int.floor_le x]
    have h1 : y < 1 := by rw [hydef]; linarith [Int.lt_floor_add_one x]
    rcases eq_or_lt_of_le h0 with h | hpos
    · exact ⟨⌊x⌋, by rw [hydef] at h; linarith⟩
    · exfalso
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
      have hyn : y ^ n ∈ S := S.pow_mem hy n
      have hne : y ^ n ≠ 0 := (pow_pos hpos n).ne'
      have := hdisc _ hyn hne
      rw [abs_of_pos (pow_pos hpos n)] at this
      linarith
  · rintro ⟨k, rfl⟩
    exact coe_int_mem S k

/-- **The lattice `(1/N)ℤ` is a ring only for `N = 1`.** It is closed under multiplication
exactly when `N = 1`, which is why the setting of the paper is a lattice and not a subring:
by `discrete_subring_real` there is no other discrete subring of `ℝ` to pass to. -/
theorem lattice_mul_closed_iff {N : ℕ} (hN : 0 < N) :
    (∀ x y : ℝ, (∃ a : ℤ, x = a / N) → (∃ b : ℤ, y = b / N) → ∃ c : ℤ, x * y = c / N)
      ↔ N = 1 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h ((1 : ℤ) / N) ((1 : ℤ) / N) ⟨1, by norm_num⟩ ⟨1, by norm_num⟩
    have : (1 : ℝ) / (N : ℝ) = c := by
      field_simp at hc ⊢
      nlinarith [hc, sq_nonneg ((N : ℝ))]
    have hle : (1 : ℝ) / N ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast hN
    have hpos : (0 : ℝ) < 1 / N := by positivity
    have hc1 : (c : ℝ) = 1 / N := this.symm
    have : c = 1 := by
      have h1 : (0 : ℝ) < c := by rw [hc1]; exact hpos
      have h2 : (c : ℝ) ≤ 1 := by rw [hc1]; exact hle
      have : (0 : ℤ) < c := by exact_mod_cast h1
      have : c ≤ 1 := by exact_mod_cast h2
      omega
    rw [this] at hc1
    field_simp at hc1
    exact_mod_cast hc1
  · rintro rfl
    intro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by rw [ha, hb]; push_cast; ring⟩

end VicoEnum
