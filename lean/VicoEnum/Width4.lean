/-
  VicoEnum/Width4.lean

  D1:  T(N,4) = d(2N²).

  The width-4 closing condition `M(a)M(b)M(c)M(d) = -I` is reduced to
  `c = a`, `d = b`, `ab = 2` (Lemma `isFrieze4_iff`), so a width-4 frieze is
  determined by its first entry. Membership of the cycle in `(1/N)ℤ` then says
  exactly that the numerator of that entry divides `2N²`.
-/
import VicoEnum.Basic

namespace VicoEnum

open Matrix

/-- The frieze matrix `M(a) = !![a, -1; 1, 0]`. -/
def M (a : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![a, -1; 1, 0]

/-- A positive width-4 quiddity cycle: four positive rationals whose monodromy
is `-I`. -/
def IsFrieze4 (a b c d : ℚ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ M a * M b * M c * M d = -1

/-- **The width-4 reduction.** The monodromy condition forces the cycle to be
`(a, 2/a, a, 2/a)`. -/
lemma isFrieze4_iff (a b c d : ℚ) :
    IsFrieze4 a b c d ↔ 0 < a ∧ a * b = 2 ∧ c = a ∧ d = b := by
  constructor
  · rintro ⟨ha, hb, hc, hd, hM⟩
    -- read off the four entries of the monodromy
    rw [show (-1 : Matrix (Fin 2) (Fin 2) ℚ) = !![-1, 0; 0, -1] by
      ext i j; fin_cases i <;> fin_cases j <;> simp] at hM
    simp only [M, Matrix.mul_fin_two] at hM
    have e00 := congrFun (congrFun hM 0) 0
    have e01 := congrFun (congrFun hM 0) 1
    have e10 := congrFun (congrFun hM 1) 0
    have e11 := congrFun (congrFun hM 1) 1
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e00 e01 e10 e11
    -- (1,1) gives bc = 2; (0,1) gives c = a; then ab = 2 and (1,0) gives d = b
    have hbc : b * c = 2 := by linarith [e11]
    have hca : c = a := by nlinarith [e01, hbc, ha, hc]
    have hab : a * b = 2 := by rw [← hca]; linarith [hbc, mul_comm b c]
    have hdb : d = b := by nlinarith [e10, hbc, hca, hb, hd]
    exact ⟨ha, hab, hca, hdb⟩
  · rintro ⟨ha, hab, hca, hdb⟩
    have hb : 0 < b := by nlinarith [hab, ha]
    refine ⟨ha, hb, by rw [hca]; exact ha, by rw [hdb]; exact hb, ?_⟩
    rw [hca, hdb]
    rw [show (-1 : Matrix (Fin 2) (Fin 2) ℚ) = !![-1, 0; 0, -1] by
      ext i j; fin_cases i <;> fin_cases j <;> simp]
    simp only [M, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> nlinarith [hab]

/-! ## The lattice condition -/

/-- A positive width-4 frieze lies in `(1/N)ℤ` exactly when the numerator of its
first entry is a divisor of `2N²`. -/
theorem width4_set (N : ℕ) (hN : 0 < N) :
    {a : ℚ | 0 < a ∧ InLattice N a ∧ InLattice N (2 / a)}
      = (fun p : ℕ => (p : ℚ) / (N : ℚ)) '' ((2 * N ^ 2).divisors : Set ℕ) := by
  have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hNZ : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Nat.mem_divisors]
  constructor
  · rintro ⟨hapos, ⟨k, rfl⟩, hlat2⟩
    have hk : 0 < k := by
      by_contra hk
      push_neg at hk
      have : ((k : ℚ)) / (N : ℚ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (by exact_mod_cast hk) (by positivity)
      linarith
    refine ⟨k.toNat, ⟨?_, by positivity⟩, ?_⟩
    swap
    · congr 1
      exact_mod_cast Int.toNat_of_nonneg hk.le
    -- `2 / a = 2N/k` lies in `(1/N)ℤ` iff `k ∣ 2N²`
    obtain ⟨m, hm⟩ := hlat2
    have hkQ : ((k : ℚ)) ≠ 0 := by exact_mod_cast hk.ne'
    have : (2 : ℚ) * (N : ℚ) ^ 2 = (m : ℚ) * (k : ℚ) := by
      field_simp at hm
      linarith [hm]
    have hZ : (2 : ℤ) * (N : ℤ) ^ 2 = m * k := by exact_mod_cast this
    have : (k : ℤ) ∣ 2 * (N : ℤ) ^ 2 := ⟨m, by linarith [hZ]⟩
    have := Int.natCast_dvd_natCast.mp (by
      simpa [Int.toNat_of_nonneg hk.le] using this : ((k.toNat : ℕ) : ℤ) ∣ ((2 * N ^ 2 : ℕ) : ℤ))
    exact this
  · rintro ⟨p, ⟨hpdvd, hne⟩, rfl⟩
    have hp : 0 < p := Nat.pos_of_dvd_of_pos hpdvd (by positivity)
    have hpQ : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
    refine ⟨by positivity, ⟨p, by push_cast; ring⟩, ?_⟩
    obtain ⟨m, hm⟩ := hpdvd
    refine ⟨2 * (N : ℤ) ^ 2 / p, ?_⟩
    have : (2 * N ^ 2 : ℤ) / (p : ℤ) = (m : ℤ) := by
      rw [show (2 * (N : ℤ) ^ 2) = (p : ℤ) * (m : ℤ) by exact_mod_cast hm]
      exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne')
    rw [this]
    have : (2 : ℚ) * (N : ℚ) ^ 2 = (p : ℚ) * (m : ℚ) := by exact_mod_cast hm
    field_simp
    linarith [this]

/-- **D1.** `T(N,4) = d(2N²)`. -/
theorem width4_card (N : ℕ) (hN : 0 < N) :
    Set.ncard {a : ℚ | 0 < a ∧ InLattice N a ∧ InLattice N (2 / a)}
      = (2 * N ^ 2).divisors.card := by
  have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [width4_set N hN]
  rw [Set.ncard_image_of_injOn]
  · simp [Set.ncard_coe_Finset]
  · intro x _ y _ hxy
    field_simp at hxy
    exact_mod_cast hxy

end VicoEnum
