/-
  VicoEnum/TenPrime.lean

  Proposition `prop:tenprime`: `10 ∣ T(p,5)` at a prime.

  `five_dvd_T5` supplies the factor `5`. The factor `2` comes from an involution, and the
  cheap one is the swap `(p,q) ↦ (q,p)`: `W5` is symmetric, so the swap acts on the counted
  set, and `card_add_fixed_even` makes `T5 N` congruent mod `2` to the number of its fixed
  points, which are the diagonal pairs.

  At a prime the diagonal has exactly two points. `W5 p x x` needs `p ∣ x²`, hence `p ∣ x`,
  and `(x-p)(x+p) ∣ p²(x+p)`, hence `x - p ∣ p²`, so `x ∈ {p+1, 2p, p²+p}`; the first fails
  `p ∣ x`. So `T5 p` is even, and with the factor five, divisible by ten.

  Note `10 ∣ T(N,5)` is false for general `N`: `T(8,5) = 145` and `T(16,5) = 255`. At
  `N = 16` the diagonal has seven points, an odd number.
-/
import VicoEnum.Assemble

namespace VicoEnum

open Finset

/-- **The diagonal at a prime.** -/
theorem W5_diag_prime {p x : ℕ} (hp : p.Prime) : W5 p x x ↔ x = 2 * p ∨ x = p ^ 2 + p := by
  have hp2 := hp.two_le
  constructor
  · rintro ⟨hx, -, hlt, hd, hdp, -⟩
    have hpx : p ∣ x := ((Nat.Prime.dvd_mul hp).mp hd).elim id id
    have hgt : p < x := by nlinarith [hlt, hp.pos]
    obtain ⟨d, rfl⟩ : ∃ d, x = p + d := ⟨x - p, by omega⟩
    have hd0 : 0 < d := by omega
    have hsub : (p + d) * (p + d) - p ^ 2 = d * (2 * p + d) := by
      have h1 : (p + d) * (p + d) = p ^ 2 + d * (2 * p + d) := by ring
      omega
    rw [hsub] at hdp
    have hne : 0 < 2 * p + d := by omega
    have hdvd : d ∣ p ^ 2 := by
      obtain ⟨c, hc⟩ := hdp
      refine ⟨c, ?_⟩
      have hh : p ^ 2 * (2 * p + d) = (d * c) * (2 * p + d) := by
        calc p ^ 2 * (2 * p + d) = p ^ 2 * (p + d + p) := by ring
          _ = d * (2 * p + d) * c := hc
          _ = (d * c) * (2 * p + d) := by ring
      exact Nat.eq_of_mul_eq_mul_right hne hh
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    interval_cases i
    · exfalso
      simp only [pow_zero] at hpx
      have hd1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp hpx
      have := Nat.le_of_dvd one_pos hd1
      omega
    · exact Or.inl (by simp only [pow_one]; ring)
    · exact Or.inr (by ring)
  · rintro (rfl | rfl)
    · have hpsq : 0 < p ^ 2 := by positivity
      have hsub : 2 * p * (2 * p) - p ^ 2 = 3 * p ^ 2 := by
        have : 2 * p * (2 * p) = p ^ 2 + 3 * p ^ 2 := by ring
        omega
      have hlt : p ^ 2 < 2 * p * (2 * p) := by
        have : 2 * p * (2 * p) = p ^ 2 + 3 * p ^ 2 := by ring
        omega
      exact ⟨by omega, by omega, hlt, ⟨4 * p, by ring⟩,
        by rw [hsub]; exact ⟨p, by ring⟩, by rw [hsub]; exact ⟨p, by ring⟩⟩
    · have hsub : (p ^ 2 + p) * (p ^ 2 + p) - p ^ 2 = p ^ 3 * (p + 2) := by
        have h1 : (p ^ 2 + p) * (p ^ 2 + p) = p ^ 2 + p ^ 3 * (p + 2) := by ring
        omega
      have hlt : p ^ 2 < (p ^ 2 + p) * (p ^ 2 + p) := by
        have h1 : (p ^ 2 + p) * (p ^ 2 + p) = p ^ 2 + p ^ 3 * (p + 2) := by ring
        have h2 : 0 < p ^ 3 * (p + 2) := by positivity
        omega
      have hdv : ((p ^ 2 + p) * (p ^ 2 + p) - p ^ 2) ∣ p ^ 2 * (p ^ 2 + p + p) := by
        rw [hsub]
        exact ⟨1, by ring⟩
      exact ⟨by positivity, by positivity, hlt, ⟨p ^ 3 + 2 * p ^ 2 + p, by ring⟩, hdv, hdv⟩

/-- The diagonal of the counted set, at a prime, is `{(2p,2p), (p²+p, p²+p)}`. -/
theorem diag_card_prime {p : ℕ} (hp : p.Prime) :
    (((box5 p).filter (fun x => W5 p x.1 x.2)).filter (fun x => Prod.swap x = x)).card = 2 := by
  classical
  have hpos : 0 < p := hp.pos
  have hset : ((box5 p).filter (fun x => W5 p x.1 x.2)).filter (fun x => Prod.swap x = x)
      = {(2 * p, 2 * p), (p ^ 2 + p, p ^ 2 + p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff,
      Prod.swap_prod_mk]
    constructor
    · rintro ⟨⟨-, hw⟩, hs⟩
      have hxy : x.1 = x.2 := hs.2
      rw [← hxy] at hw
      rcases (W5_diag_prime hp).mp hw with h | h
      · exact Or.inl ⟨h, by rw [← hxy]; exact h⟩
      · exact Or.inr ⟨h, by rw [← hxy]; exact h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      · have hw : W5 p x.1 x.2 := by
          rw [h1, h2]
          exact (W5_diag_prime hp).mpr (by first | exact Or.inl rfl | exact Or.inr rfl)
        exact ⟨⟨by simpa using mem_box5_of_W5 hpos hw, hw⟩, by simp [h1, h2]⟩
  rw [hset]
  rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
  simp only [Finset.mem_singleton, Prod.ext_iff, not_and]
  intro h
  exfalso
  have h2 := hp.two_le
  nlinarith [h]

/-- **Proposition `prop:tenprime`, for the `W5`-pair count**; `friezes5_ncard` in
`Count5.lean` transfers this to `T(p,5)`. -/
theorem ten_dvd_T5_prime {p : ℕ} (hp : p.Prime) : 10 ∣ T5 p := by
  classical
  have hpos : 0 < p := hp.pos
  have h5 : 5 ∣ T5 p := five_dvd_T5 hpos
  have hswap : ∀ x : ℕ × ℕ, Prod.swap (Prod.swap x) = x := fun x => rfl
  have hmap : ∀ x ∈ (box5 p).filter (fun x => W5 p x.1 x.2),
      Prod.swap x ∈ (box5 p).filter (fun x => W5 p x.1 x.2) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    obtain ⟨-, hw⟩ := hx
    have hw' : W5 p (Prod.swap x).1 (Prod.swap x).2 := W5_symm hw
    exact ⟨by simpa using mem_box5_of_W5 hpos hw', hw'⟩
  have heven := card_add_fixed_even hswap _ hmap
  rw [diag_card_prime hp] at heven
  have h2 : 2 ∣ T5 p := by
    simp only [T5]
    omega
  omega

end VicoEnum
