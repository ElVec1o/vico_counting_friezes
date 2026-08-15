/-
  VicoEnum/MarkovCount.lean

  Theorem `thm:markov`: the Markov-type reduction of `T(N,5)`.

  `Markov.lean` has the three algebraic facts. This file assembles them into the count.

  Writing `p + N = gu`, `q + N = gv` with `g = gcd(p+N, q+N)` and `M = guv - N(u+v)`, the
  quantity `e = pq - N^2` is `gM` (`markov_factor`), so `pq = N^2 + gM` with no subtraction.
  Going from a quadruple to a pair, the two divisibilities of `W5` follow from `M ∣ N^2`
  directly. Coming back is the substantial direction: with `e = Nf` the divisibilities read
  `f ∣ Ngu` and `f ∣ Ngv`, hence `f ∣ N g gcd(u,v) = Ng`, and `markov_dvd_iff` turns that
  into `M ∣ N^2`.

  The map runs from quadruples to pairs, `(g,u,v,M) ↦ (gu - N, gv - N)`, the inverse of the
  paper's map, so no gcd appears in the map itself. `markov_gcd` is used in INJECTIVITY, where
  `g` is recovered from the pair as `gcd(gu, gv) = g gcd(u,v) = g`. Surjectivity needs the
  same cancellation but inlines it, since there the coprimality is a hypothesis in hand.
-/
import VicoEnum.Markov
import VicoEnum.PaperDef

namespace VicoEnum

/-- The `W5` pairs, as a set. -/
def W5Set (N : ℕ) : Set (ℕ × ℕ) := {x | W5 N x.1 x.2}

/-- The quadruples of Theorem `thm:markov`. -/
def MarkovSet (N : ℕ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {z | z.1 * z.2.1 * z.2.2.1 = N * (z.2.1 + z.2.2.1) + z.2.2.2 ∧
    z.2.2.2 ∣ N ^ 2 ∧ N ∣ z.1 * z.2.2.2 ∧ Nat.gcd z.2.1 z.2.2.1 = 1 ∧
    N < z.1 * z.2.1 ∧ N < z.1 * z.2.2.1}

/-- The map of Theorem `thm:markov`, from quadruples to numerator pairs. -/
def mkv (N : ℕ) : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ :=
  fun z => (z.1 * z.2.1 - N, z.1 * z.2.2.1 - N)

/-! ## The product identity -/

/-- **`pq = N² + gM`**, division-free. This is `markov_factor` transported to `ℕ`, and it is
proved from it rather than re-derived. -/
theorem mkv_prod {N g u v M : ℕ} (hM : g * u * v = N * (u + v) + M)
    (hu : N < g * u) (hv : N < g * v) :
    (g * u - N) * (g * v - N) = N ^ 2 + g * M := by
  have hMZ : (g : ℤ) * u * v = (N : ℤ) * (u + v) + M := by exact_mod_cast hM
  zify [hu.le, hv.le]
  linear_combination markov_factor N g u v + (g : ℤ) * hMZ

/-! ## Quadruples to pairs -/

/-- **Quadruple to pair.** All six clauses of `W5`; the two divisibilities come from
`M ∣ N²` directly. -/
theorem mkv_mapsTo {N : ℕ} (hN : 0 < N) : Set.MapsTo (mkv N) (MarkovSet N) (W5Set N) := by
  rintro ⟨g, u, v, M⟩ ⟨hrel, hMN, hNgM, hcop, hu, hv⟩
  dsimp only at hrel hMN hNgM hcop hu hv
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · simp at hu
    · exact h
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with rfl | h
    · exact absurd (Nat.eq_zero_of_zero_dvd hMN) (by positivity)
    · exact h
  show W5 N (g * u - N) (g * v - N)
  have hprod : (g * u - N) * (g * v - N) = N ^ 2 + g * M := mkv_prod hrel hu hv
  have hgM : 0 < g * M := Nat.mul_pos hg hMpos
  have he : (g * u - N) * (g * v - N) - N ^ 2 = g * M := by rw [hprod]; omega
  refine ⟨by omega, by omega, by rw [hprod]; omega, ?_, ?_, ?_⟩
  · rw [hprod]
    exact Nat.dvd_add ⟨N, by ring⟩ hNgM
  · rw [he, show (g * u - N) + N = g * u from by omega,
      show N ^ 2 * (g * u) = g * (N ^ 2 * u) from by ring]
    exact mul_dvd_mul_left g (hMN.mul_right u)
  · rw [he, show (g * v - N) + N = g * v from by omega,
      show N ^ 2 * (g * v) = g * (N ^ 2 * v) from by ring]
    exact mul_dvd_mul_left g (hMN.mul_right v)

/-! ## Injectivity

`g` is recovered from the pair as `gcd(p+N, q+N)`, which is `g gcd(u,v) = g` by
`markov_gcd`; then `u`, `v` cancel and `M` is determined by the relation. -/

theorem mkv_injOn {N : ℕ} : Set.InjOn (mkv N) (MarkovSet N) := by
  rintro ⟨g, u, v, M⟩ ⟨hrel, -, -, hcop, hu, hv⟩ ⟨g', u', v', M'⟩ ⟨hrel', -, -, hcop', hu', hv'⟩ hEq
  dsimp only at hrel hcop hu hv hrel' hcop' hu' hv'
  simp only [mkv, Prod.mk.injEq] at hEq
  have e1 : g * u = g' * u' := by omega
  have e2 : g * v = g' * v' := by omega
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · simp at hu
    · exact h
  have hgg : g = g' := by
    have h1 := markov_gcd g u v hcop
    have h2 := markov_gcd g' u' v' hcop'
    rw [← h1, ← h2, e1, e2]
  subst hgg
  have hue : u = u' := Nat.eq_of_mul_eq_mul_left hg e1
  have hve : v = v' := Nat.eq_of_mul_eq_mul_left hg e2
  subst hue; subst hve
  have : M = M' := by omega
  subst this
  rfl

/-! ## Surjectivity

Given a `W5` pair, set `g = gcd(p+N, q+N)`. The relation and the two positivity conditions
are immediate; the content is `M ∣ N^2`, which comes from `markov_dvd_iff` once the two
divisibilities of `W5` have been combined into `f ∣ Ng`. -/

theorem mkv_surjOn {N : ℕ} (hN : 0 < N) : Set.SurjOn (mkv N) (MarkovSet N) (W5Set N) := by
  rintro ⟨p, q⟩ ⟨hp, hq, hlt, hNpq, hd1, hd2⟩
  dsimp only at hp hq hlt hNpq hd1 hd2
  obtain ⟨e, he⟩ : ∃ e, p * q = N ^ 2 + e := ⟨p * q - N ^ 2, by omega⟩
  have hepos : 0 < e := by omega
  have hesub : p * q - N ^ 2 = e := by omega
  rw [hesub] at hd1 hd2
  set g := Nat.gcd (p + N) (q + N) with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  set u := (p + N) / g with hudef
  set v := (q + N) / g with hvdef
  have hgu : g * u = p + N := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hgv : g * v = q + N := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hcop : Nat.gcd u v = 1 := Nat.coprime_div_gcd_div_gcd hg
  -- `g (guv) = g (N(u+v)) + e`, so `g ∣ e` and `M` exists
  have hge : g * (g * u * v) = g * (N * (u + v)) + e := by
    have h1 : g * (g * u * v) = (g * u) * (g * v) := by ring
    have h2 : g * (N * (u + v)) = N * (g * u) + N * (g * v) := by ring
    rw [h1, h2, hgu, hgv]
    nlinarith [he]
  have hMge : N * (u + v) ≤ g * u * v := by
    have h : g * (N * (u + v)) < g * (g * u * v) := by omega
    exact (Nat.lt_of_mul_lt_mul_left h).le
  obtain ⟨M, hrel⟩ : ∃ M, g * u * v = N * (u + v) + M := ⟨g * u * v - N * (u + v), by omega⟩
  have hexp : g * (g * u * v) = g * (N * (u + v)) + g * M := by rw [hrel, Nat.mul_add]
  have hgM : g * M = e := by omega
  -- `N ∣ e`, giving `f`
  have hNe : N ∣ e := by
    have : N ∣ N ^ 2 + e := by rw [← he]; exact hNpq
    exact (Nat.dvd_add_right ⟨N, by ring⟩).mp this
  obtain ⟨f, hf⟩ := hNe
  -- `f ∣ Ng` from the two divisibilities and `gcd(u,v) = 1`
  have hfu : f ∣ N * g * u := by
    have h1 : e ∣ N ^ 2 * (p + N) := hd1
    rw [hf, ← hgu] at h1
    have h2 : N * f ∣ N * (N * g * u) := by
      refine dvd_trans h1 (dvd_of_eq ?_); ring
    exact (mul_dvd_mul_iff_left (by omega : N ≠ 0)).mp h2
  have hfv : f ∣ N * g * v := by
    have h1 : e ∣ N ^ 2 * (q + N) := hd2
    rw [hf, ← hgv] at h1
    have h2 : N * f ∣ N * (N * g * v) := by
      refine dvd_trans h1 (dvd_of_eq ?_); ring
    exact (mul_dvd_mul_iff_left (by omega : N ≠ 0)).mp h2
  have hfg : f ∣ N * g := by
    have := Nat.dvd_gcd hfu hfv
    rwa [Nat.gcd_mul_left, hcop, Nat.mul_one] at this
  -- `M ∣ N²` by `markov_dvd_iff`
  have hMN : M ∣ N ^ 2 := by
    have hNf : (N : ℤ) * f = (g : ℤ) * M := by
      have : (N : ℤ) * f = (e : ℤ) := by exact_mod_cast hf.symm
      rw [this]; exact_mod_cast hgM.symm
    have hfgZ : (f : ℤ) ∣ (N : ℤ) * g := by exact_mod_cast hfg
    have := (markov_dvd_iff (by exact_mod_cast hN.ne' : (N:ℤ) ≠ 0)
      (by exact_mod_cast hg.ne' : (g:ℤ) ≠ 0) hNf).mp hfgZ
    exact_mod_cast this
  refine ⟨(g, u, v, M), ⟨hrel, hMN, ?_, hcop, by rw [hgu]; omega, by rw [hgv]; omega⟩, ?_⟩
  · rw [hgM, hf]; exact Dvd.intro f rfl
  · show ((g * u - N : ℕ), (g * v - N : ℕ)) = (p, q)
    rw [hgu, hgv]; simp

/-! ## The count -/

/-- **The bijection of Theorem `thm:markov`**, in the direction quadruples to pairs. -/
theorem mkv_bijOn {N : ℕ} (hN : 0 < N) : Set.BijOn (mkv N) (MarkovSet N) (W5Set N) :=
  ⟨mkv_mapsTo hN, mkv_injOn, mkv_surjOn hN⟩

/-- The `W5` pairs are counted by `T5`. `W5Set N` is definitionally the set `W5_ncard`
already speaks about, so this is that theorem and not a second proof of it. -/
theorem w5Set_ncard {N : ℕ} (hN : 0 < N) : (W5Set N).ncard = T5 N := W5_ncard N hN

/-- The Markov quadruples are counted by `T5`. -/
theorem markov_ncard {N : ℕ} (hN : 0 < N) : (MarkovSet N).ncard = T5 N := by
  have h1 : mkv N '' MarkovSet N = W5Set N := (mkv_bijOn hN).image_eq
  have h2 : (mkv N '' MarkovSet N).ncard = (MarkovSet N).ncard :=
    Set.ncard_image_of_injOn mkv_injOn
  rw [← h2, h1, w5Set_ncard hN]

/-- **Theorem `thm:markov`.** `T(N,5)` is the number of Markov quadruples. The right side is
stated on Definition `def:frieze` itself, through `paper_count`. -/
theorem markov_count {N : ℕ} (hN : 0 < N) :
    (MarkovSet N).ncard = {F : Fin 6 → ℤ → ℚ | PaperFrieze5 N F}.ncard := by
  exact (markov_ncard hN).trans (paper_count hN).symm

end VicoEnum