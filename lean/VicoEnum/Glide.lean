/-
  VicoEnum/Glide.lean

  The glide symmetry, and the lattice criterion at every width.

  Rows `r` and `n-r` of a frieze carry the same entries: `m_{r,j} = m_{n-r,j+r}`. This is
  classical, and it follows from the monodromy alone. Splitting
  `M(a_j)⋯M(a_{j+n-1}) = -I` as `P Q = -I`, where `P` is the first `r-1` factors, the
  determinant identity `det P = 1` forces `Q 1 1 = -(P 0 0)`; and those two matrix entries
  are exactly the two continuants in question (`glide_core`, `glide`).

  Consequently the conditions defining a frieze over `(1/N)ℤ` come from rows
  `2 ≤ r ≤ ⌊n/2⌋` only. Writing `a_j = p_j/N`, row `r` has entries
  `K_{r-1}(a_j,…) = C_{r-1}(p_j,…)/N^{r-1}` by `Kr_homog`, so by `row_lattice_iff` the
  row lies in `(1/N)ℤ` exactly when `N^{r-2} ∣ C_{r-1}(p_j,…)`, and it is positive exactly
  when `C_{r-1}(p_j,…) > 0`.

  At `n = 5` the range `2 ≤ r ≤ 2` contains only the quiddity, which is Remark 2.3. At
  `n = 6` it adds `r = 3`, which is `N ∣ p_j p_{j+1}`, and that is Theorem `thm:w6count`.
  The cutoff is sharp in both directions: dropping row `⌊n/2⌋` overcounts at widths 7, 8
  and 9, and adding row `⌊n/2⌋+1` changes nothing (`code/glide_criterion.py`).
-/
import VicoEnum.Width6
import VicoEnum.Param

namespace VicoEnum

open Matrix

/-! ## Continuants as matrix products -/

/-- The frieze continuant of the window `a i, …, a (i+k-1)`. -/
def Kr (a : ℕ → ℚ) (i : ℕ) : ℕ → ℚ
  | 0 => 1
  | 1 => a i
  | (k + 2) => a (i + k + 1) * Kr a i (k + 1) - Kr a i k

@[simp] theorem Kr_zero (a : ℕ → ℚ) (i : ℕ) : Kr a i 0 = 1 := rfl
@[simp] theorem Kr_one (a : ℕ → ℚ) (i : ℕ) : Kr a i 1 = a i := rfl

theorem Kr_succ_succ (a : ℕ → ℚ) (i k : ℕ) :
    Kr a i (k + 2) = a (i + k + 1) * Kr a i (k + 1) - Kr a i k := rfl

/-- The product `M(a i) ⋯ M(a (i+k-1))` of frieze matrices. -/
def Mprod (a : ℕ → ℚ) (i : ℕ) : ℕ → Matrix (Fin 2) (Fin 2) ℚ
  | 0 => 1
  | (k + 1) => Mprod a i k * M (a (i + k))

theorem det_M (x : ℚ) : (M x).det = 1 := by
  simp [M, Matrix.det_fin_two_of]

theorem det_Mprod (a : ℕ → ℚ) (i k : ℕ) : (Mprod a i k).det = 1 := by
  induction k with
  | zero => simp [Mprod]
  | succ m ih => simp [Mprod, Matrix.det_mul, ih, det_M]

/-- Products split: the first `k` factors times the next `l`. -/
theorem Mprod_add (a : ℕ → ℚ) (i k l : ℕ) :
    Mprod a i (k + l) = Mprod a i k * Mprod a (i + k) l := by
  induction l with
  | zero => simp [Mprod]
  | succ m ih =>
    have hk : k + (m + 1) = (k + m) + 1 := by omega
    have hi : i + (k + m) = (i + k) + m := by omega
    rw [hk]
    show Mprod a i (k + m) * M (a (i + (k + m))) = _
    rw [ih, hi, Mprod, ← mul_assoc]

/-- **The four entries of a product are continuants.** This is the standard
continuant-matrix identity, in the form needed below. -/
theorem Mprod_entries (a : ℕ → ℚ) (i k : ℕ) :
    Mprod a i (k + 2)
      = !![Kr a i (k + 2), -(Kr a i (k + 1)); Kr a (i + 1) (k + 1), -(Kr a (i + 1) k)] := by
  induction k with
  | zero =>
    show Mprod a i 1 * M (a (i + 1)) = _
    show (Mprod a i 0 * M (a (i + 0))) * M (a (i + 1)) = _
    simp only [Mprod, one_mul, Nat.add_zero]
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [M, Kr, Matrix.mul_fin_two, Matrix.one_fin_two] <;> ring
  | succ m ih =>
    show Mprod a i (m + 2) * M (a (i + (m + 2))) = _
    rw [ih]
    have h1 : i + (m + 2) = i + m + 1 + 1 := by omega
    have h2 : i + 1 + m + 1 = i + m + 1 + 1 := by omega
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [M, Kr_succ_succ, Matrix.mul_fin_two, h1, h2] <;> ring

theorem Mprod_00 (a : ℕ → ℚ) (i k : ℕ) : (Mprod a i (k + 1)) 0 0 = Kr a i (k + 1) := by
  cases k with
  | zero =>
    show (Mprod a i 0 * M (a (i + 0))) 0 0 = _
    simp [Mprod, M, Matrix.one_fin_two, Matrix.mul_fin_two]
  | succ m => rw [Mprod_entries]; simp

theorem Mprod_11 (a : ℕ → ℚ) (i k : ℕ) :
    (Mprod a i (k + 2)) 1 1 = -(Kr a (i + 1) k) := by
  rw [Mprod_entries]; simp

/-! ## The glide -/

/-- **The determinant step.** If `P Q = -I` and `det P = 1`, then `Q 1 1 = -(P 0 0)`.
Everything about the glide is in this line: the bottom-right entry of the complementary
product is minus the top-left entry of the leading one. -/
theorem glide_core {P Q : Matrix (Fin 2) (Fin 2) ℚ} (hd : P.det = 1) (h : P * Q = -1) :
    Q 1 1 = -(P 0 0) := by
  have hneg : (-1 : Matrix (Fin 2) (Fin 2) ℚ) = !![-1, 0; 0, -1] := by
    ext r c; fin_cases r <;> fin_cases c <;> simp
  rw [hneg] at h
  have e2 : P 0 0 * Q 0 1 + P 0 1 * Q 1 1 = 0 := by
    have := congrFun (congrFun h 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e4 : P 1 0 * Q 0 1 + P 1 1 * Q 1 1 = -1 := by
    have := congrFun (congrFun h 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hdet : P 0 0 * P 1 1 - P 0 1 * P 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hd; linarith [hd]
  linear_combination P 0 0 * e4 - P 1 0 * e2 - Q 1 1 * hdet

/-- **The glide symmetry.** For a quiddity cycle of length `n = s+t+3` with monodromy
`-I`, the continuant of the window of length `s+1` starting at `j` equals the continuant of
the complementary window of length `t` starting at `j+s+2`. In frieze terms, with
`r = s+2`, this says `m_{r,j} = m_{n-r,j+r}`: row `r` and row `n-r` carry the same entries.

Rows `r` and `n-r` therefore impose the same conditions, so the interior range
`2 ≤ r ≤ n-2` reduces to `2 ≤ r ≤ ⌊n/2⌋`. -/
theorem glide {a : ℕ → ℚ} {j s t : ℕ} (h : Mprod a j (s + t + 3) = -1) :
    Kr a (j + s + 2) t = Kr a j (s + 1) := by
  have hsplit : Mprod a j (s + t + 3) = Mprod a j (s + 1) * Mprod a (j + (s + 1)) (t + 2) := by
    have : s + t + 3 = (s + 1) + (t + 2) := by omega
    rw [this, Mprod_add]
  rw [hsplit] at h
  have key := glide_core (det_Mprod a j (s + 1)) h
  rw [Mprod_11, Mprod_00] at key
  have hidx : j + (s + 1) + 1 = j + s + 2 := by omega
  rw [hidx] at key
  linarith [key]

/-! ## The lattice criterion -/

/-- **Homogenisation.** Substituting `a_j = p_j/N` into the frieze continuant and clearing
denominators produces the integer continuant `Cw` of `GeneralWidth.lean`:
`K_k(p_i/N, …) = C_k(p_i, …)/N^k`. -/
theorem Kr_homog {N : ℤ} (hN : (N : ℚ) ≠ 0) (p : ℕ → ℤ) (i : ℕ) :
    ∀ k, Kr (fun j => (p j : ℚ) / (N : ℚ)) i k = ((Cw N p i k : ℤ) : ℚ) / (N : ℚ) ^ k := by
  have main : ∀ k,
      (Kr (fun j => (p j : ℚ) / (N : ℚ)) i k = ((Cw N p i k : ℤ) : ℚ) / (N : ℚ) ^ k) ∧
      (Kr (fun j => (p j : ℚ) / (N : ℚ)) i (k + 1)
        = ((Cw N p i (k + 1) : ℤ) : ℚ) / (N : ℚ) ^ (k + 1)) := by
    intro k
    induction k with
    | zero => exact ⟨by simp [Kr, Cw], by simp [Kr, Cw]⟩
    | succ m ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1, ?_⟩
      rw [Kr_succ_succ, h1, h0, Cw_succ_succ]
      push_cast
      field_simp
      ring
  exact fun k => (main k).1

/-- **The row criterion.** An entry of row `r = k+2`, which equals `C/N^{k+1}` with `C` an
integer continuant, lies in `(1/N)ℤ` if and only if `N^k` divides `C`. -/
theorem row_lattice_iff {N : ℕ} (hN : 0 < N) (C : ℤ) (k : ℕ) :
    InLattice N ((C : ℚ) / (N : ℚ) ^ (k + 1)) ↔ (N : ℤ) ^ k ∣ C := by
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpk : ((N : ℚ)) ^ k ≠ 0 := pow_ne_zero k hN'
  have hstep : (N : ℚ) * ((C : ℚ) / (N : ℚ) ^ (k + 1)) = (C : ℚ) / (N : ℚ) ^ k := by
    field_simp
    ring
  rw [inLattice_iff hN]
  constructor
  · rintro ⟨m, hm⟩
    rw [hstep, div_eq_iff hpk] at hm
    refine ⟨m, ?_⟩
    have hc : ((C : ℤ) : ℚ) = (((N : ℤ) ^ k * m : ℤ) : ℚ) := by
      push_cast; linear_combination hm
    exact_mod_cast hc
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hstep, div_eq_iff hpk]
    have hc : ((C : ℤ) : ℚ) = (((N : ℤ) ^ k * m : ℤ) : ℚ) := by exact_mod_cast hm
    push_cast at hc
    linear_combination hc

/-- The positivity half: an entry of row `r = k+2` is positive exactly when its integer
continuant is. -/
theorem row_pos_iff {N : ℕ} (hN : 0 < N) (C : ℤ) (k : ℕ) :
    0 < ((C : ℚ) / (N : ℚ) ^ (k + 1)) ↔ 0 < C := by
  have hN' : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  have hpow : (0 : ℚ) < (N : ℚ) ^ (k + 1) := by positivity
  rw [div_pos_iff]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · exact_mod_cast h1
    · linarith [hpow, h2]
  · intro h
    exact Or.inl ⟨by exact_mod_cast h, hpow⟩

/-! ## The monodromy at every column

Lemma `lem:glide` assumes `M(a_0)···M(a_{n-1}) = -I` and concludes for every `j` modulo `n`.
`glide` above takes the monodromy AT column `j` as its hypothesis, so what is missing is that
the monodromy at `0` gives the monodromy at `j`. Splitting the cycle at `j` writes the first
product as `PQ` and the one at `j` as `QP`, and `PQ = -I` forces `QP = -I`: multiply by `-1`
to get `P(-Q) = 1`, commute, and multiply back. Only periodicity of the quiddity and
invertibility of `P` are used, and the latter is `det_Mprod`. -/

/-- `Mprod` inherits the period of the quiddity. -/
theorem Mprod_periodic {a : ℕ → ℚ} {n : ℕ} (hper : ∀ i, a (i + n) = a i) (j k : ℕ) :
    Mprod a (j + n) k = Mprod a j k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    show Mprod a (j + n) m * M (a (j + n + m)) = Mprod a j m * M (a (j + m))
    rw [ih]
    congr 2
    rw [show j + n + m = (j + m) + n from by omega, hper]

/-- **The monodromy at column `j`.** For an `n`-periodic quiddity, the monodromy being `-I`
at column `0` makes it `-I` at every column. -/
theorem Mprod_monodromy_shift {a : ℕ → ℚ} {n : ℕ} (hper : ∀ i, a (i + n) = a i)
    (h0 : Mprod a 0 n = -1) {j : ℕ} (hj : j ≤ n) : Mprod a j n = -1 := by
  have hjn : j + (n - j) = n := by omega
  set P := Mprod a 0 j with hP
  set Q := Mprod a j (n - j) with hQ
  have hPQ : P * Q = -1 := by
    have hadd := Mprod_add a 0 j (n - j)
    rw [zero_add, hjn] at hadd
    rw [hP, hQ, ← hadd]; exact h0
  have hQP : Q * P = -1 := by
    have h1 : P * (-Q) = 1 := by rw [mul_neg, hPQ]; simp
    have h2 : (-Q) * P = 1 := (Matrix.mul_eq_one_comm).mp h1
    have : -(Q * P) = 1 := by rw [← h2]; simp
    have := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℚ => -X) this
    simpa using this
  have hsplit : Mprod a j n = Q * P := by
    have h1 : Mprod a j ((n - j) + j) = Mprod a j (n - j) * Mprod a (j + (n - j)) j :=
      Mprod_add a j (n - j) j
    rw [show (n - j) + j = n from by omega, hjn] at h1
    have h2 : Mprod a n j = P := by
      have := Mprod_periodic hper 0 j
      rw [zero_add] at this
      rw [hP]; exact this
    rw [h1, h2, hQ]
  rw [hsplit]; exact hQP

/-- **Lemma `lem:glide` as stated in the paper.** The monodromy is assumed once, at column
`0`, and the glide identity holds at every column modulo `n`. -/
theorem glide_of_monodromy {a : ℕ → ℚ} {n j s t : ℕ} (hper : ∀ i, a (i + n) = a i)
    (hn : n = s + t + 3) (h0 : Mprod a 0 n = -1) (hj : j ≤ n) :
    Kr a (j + s + 2) t = Kr a j (s + 1) := by
  refine glide ?_
  rw [← hn]
  exact Mprod_monodromy_shift hper h0 hj

end VicoEnum
