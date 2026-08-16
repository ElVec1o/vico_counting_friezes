/-
  VicoEnum/FordParity.lean

  `T(N,5)` modulo ten.

  `card_swap_parity`: a finite set of pairs closed under `(a,b) -> (b,a)` has the parity of
  its diagonal. Applied to the `W5` pairs, whose reflection is that swap, this says `T5 N`
  has the parity of the number of diagonal pairs.

  `support_card_eq_diag`: `M -> (M+N, M+N)` counts the diagonal pairs by the index set
  `{M : M | N^2, N | M^2}` of `T5_sum_ford`.

  `support_card_eq_Qp`: the divisor complement `M -> N^2/M` carries that index set onto the
  square divisors of `N^3`, since `(N^2/M)^2 | N^3` is `N | M^2`. So the index set has
  `Qp N` elements.

  `T5_mod_ten`: combining the three with `five_dvd_T5`, `T5 N = 5 Qp N mod 10`.

  `ten_dvd_T5_iff`: hence `10 | T(N,5)` exactly when `Qp N` is even, which is exactly when
  some exponent in the factorisation of `N` is 1 or 2 mod 4. At a prime this recovers
  `ten_dvd_T5_prime`.
-/
import VicoEnum.FareyPaths
import VicoEnum.Counting
namespace VicoEnum
open Finset

/-- **Parity under the swap involution.** A finite set of pairs closed under `(a,b) ↦ (b,a)`
has the parity of its diagonal. -/
theorem card_swap_parity {s : Finset (ℕ × ℕ)} (hs : ∀ x ∈ s, Prod.swap x ∈ s) :
    s.card % 2 = (s.filter (fun x => x.1 = x.2)).card % 2 := by
  classical
  have hsplit : s.card =
      (s.filter (fun x => x.1 < x.2)).card + (s.filter (fun x => x.1 = x.2)).card
        + (s.filter (fun x => x.2 < x.1)).card := by
    have h1 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := s) (p := fun x : ℕ × ℕ => x.1 < x.2)
    have h2 := Finset.filter_card_add_filter_neg_card_eq_card
      (s := s.filter (fun x : ℕ × ℕ => ¬ x.1 < x.2)) (p := fun x : ℕ × ℕ => x.1 = x.2)
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    have e1 : s.filter (fun x : ℕ × ℕ => ¬ x.1 < x.2 ∧ x.1 = x.2)
        = s.filter (fun x : ℕ × ℕ => x.1 = x.2) := by
      apply Finset.filter_congr; intro x _; constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨by omega, h⟩
    have e2 : s.filter (fun x : ℕ × ℕ => ¬ x.1 < x.2 ∧ ¬ x.1 = x.2)
        = s.filter (fun x : ℕ × ℕ => x.2 < x.1) := by
      apply Finset.filter_congr; intro x _; constructor
      · rintro ⟨h1, h2⟩; omega
      · intro h; exact ⟨by omega, by omega⟩
    rw [e1, e2] at h2
    omega
  have hbij : (s.filter (fun x => x.1 < x.2)).card = (s.filter (fun x => x.2 < x.1)).card := by
    apply Finset.card_nbij' (fun x => Prod.swap x) (fun x => Prod.swap x)
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hs x hx.1, hx.2⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hs x hx.1, hx.2⟩
    · intro x _; exact Prod.swap_swap x
    · intro x _; exact Prod.swap_swap x
  omega

/-- **The index set has `Qp N` elements.** The divisor complement `M ↦ N^2/M` carries
`{M : M ∣ N^2, N ∣ M^2}` onto the square divisors of `N^3`, because `(N^2/M)^2 ∣ N^3` is
`N ∣ M^2`. -/
theorem support_card_eq_Qp {N : ℕ} (hN : 0 < N) :
    ((N ^ 2).divisors.filter (fun M => N ∣ M ^ 2)).card = Qp N := by
  classical
  rw [Qp_eq_card hN.ne']
  have hN2 : (0:ℕ) < N ^ 2 := by positivity
  have hN3 : (0:ℕ) < N ^ 3 := by positivity
  apply Finset.card_nbij' (fun M => N ^ 2 / M) (fun k => N ^ 2 / k)
  · intro M hM
    obtain ⟨hMd, hMsq⟩ := Finset.mem_filter.mp hM
    obtain ⟨hMN, -⟩ := Nat.mem_divisors.mp hMd
    have hM0 : 0 < M := Nat.pos_of_mem_divisors hMd
    have hmul : M * (N ^ 2 / M) = N ^ 2 := Nat.mul_div_cancel' hMN
    have hkN2 : (N ^ 2 / M) ∣ N ^ 2 := Dvd.intro_left M hmul
    have hsq : M ^ 2 * (N ^ 2 / M) ^ 2 = N ^ 2 * N ^ 2 := by
      rw [show M ^ 2 * (N ^ 2 / M) ^ 2 = (M * (N ^ 2 / M)) ^ 2 from by ring, hmul]; ring
    obtain ⟨c, hc⟩ := hMsq
    have hck : c * (N ^ 2 / M) ^ 2 = N ^ 3 := by
      have h1 : N * (c * (N ^ 2 / M) ^ 2) = N * N ^ 3 := by
        rw [show N * (c * (N ^ 2 / M) ^ 2) = (N * c) * (N ^ 2 / M) ^ 2 from by ring, ← hc, hsq]
        ring
      exact Nat.eq_of_mul_eq_mul_left hN h1
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hkN2.trans ⟨N, by ring⟩, hN3.ne'⟩, ⟨c, by rw [← hck]; ring⟩⟩
  · intro k hk
    obtain ⟨hkd, hksq⟩ := Finset.mem_filter.mp hk
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hkd
    have hkN2 : k ∣ N ^ 2 := dvd_sq_of_sq_dvd_cube hk0 hN hksq
    have hmul : k * (N ^ 2 / k) = N ^ 2 := Nat.mul_div_cancel' hkN2
    have hsq : k ^ 2 * (N ^ 2 / k) ^ 2 = N ^ 2 * N ^ 2 := by
      rw [show k ^ 2 * (N ^ 2 / k) ^ 2 = (k * (N ^ 2 / k)) ^ 2 from by ring, hmul]; ring
    obtain ⟨c, hc⟩ := hksq
    have hcan : k ^ 2 * (N ^ 2 / k) ^ 2 = k ^ 2 * (N * c) := by
      rw [hsq, show N ^ 2 * N ^ 2 = N * N ^ 3 from by ring, hc]; ring
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨Dvd.intro_left k hmul, hN2.ne'⟩,
       ⟨c, Nat.eq_of_mul_eq_mul_left (by positivity) hcan⟩⟩
  · intro M hM
    obtain ⟨hMd, -⟩ := Finset.mem_filter.mp hM
    exact Nat.div_div_self (Nat.mem_divisors.mp hMd).1 hN2.ne'
  · intro k hk
    obtain ⟨hkd, hksq⟩ := Finset.mem_filter.mp hk
    exact Nat.div_div_self
      (dvd_sq_of_sq_dvd_cube (Nat.pos_of_mem_divisors hkd) hN hksq) hN2.ne'

/-- The diagonal `W5` pairs are counted by the index set, via `M ↦ (M+N, M+N)`. -/
theorem support_card_eq_diag {N : ℕ} (hN : 0 < N) :
    ((N ^ 2).divisors.filter (fun M => N ∣ M ^ 2)).card
      = ((W5box N).filter (fun x => x.1 = x.2)).card := by
  classical
  apply Finset.card_nbij' (fun M => ((M + N, M + N) : ℕ × ℕ)) (fun x => x.1 - N)
  · intro M hM
    obtain ⟨hMd, hMsq⟩ := Finset.mem_filter.mp hM
    have hM0 : 0 < M := Nat.pos_of_mem_divisors hMd
    have hw : W5 N (M + N) (M + N) :=
      (W5_diag_shift hN hM0).mpr ⟨(Nat.mem_divisors.mp hMd).1, hMsq⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨mem_box5_of_W5 hN hw, hw⟩, rfl⟩
  · intro x hx
    obtain ⟨hxb, hxe⟩ := Finset.mem_filter.mp hx
    have hw : W5 N x.1 x.1 := hxe ▸ (Finset.mem_filter.mp hxb).2
    obtain ⟨hlt, hsq, hsub⟩ := (W5_diag_iff hN).mp hw
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hsub, by positivity⟩, ?_⟩
    have hk : x.1 - N + N = x.1 := by omega
    have : N ∣ (x.1 - N + N) ^ 2 := by rw [hk]; exact hsq
    have hexp : (x.1 - N + N) ^ 2 = (x.1 - N) ^ 2 + N * (2 * (x.1 - N) + N) := by ring
    rw [hexp] at this
    exact (Nat.dvd_add_right ⟨2 * (x.1 - N) + N, rfl⟩).mp (by rwa [Nat.add_comm] at this)
  · intro M hM; simp
  · intro x hx
    obtain ⟨hxb, hxe⟩ := Finset.mem_filter.mp hx
    have hw : W5 N x.1 x.1 := hxe ▸ (Finset.mem_filter.mp hxb).2
    obtain ⟨hlt, -, -⟩ := (W5_diag_iff hN).mp hw
    exact Prod.ext (by omega) (by omega)

/-- **`T(N,5)` modulo ten.** The reflection is an involution on the `W5` pairs whose fixed
points are the diagonal ones, so `T5 N` has the parity of `Qp N`; with `5 ∣ T5 N` this
pins `T5 N` modulo ten. -/
theorem T5_mod_ten {N : ℕ} (hN : 0 < N) : T5 N % 10 = (5 * Qp N) % 10 := by
  classical
  have hswap : ∀ x ∈ W5box N, Prod.swap x ∈ W5box N := by
    intro x hx
    obtain ⟨-, hw⟩ := Finset.mem_filter.mp hx
    have hw' : W5 N (Prod.swap x).1 (Prod.swap x).2 := W5_symm hw
    exact Finset.mem_filter.mpr ⟨mem_box5_of_W5 hN hw', hw'⟩
  have hpar := card_swap_parity hswap
  rw [W5box_card] at hpar
  have hdiag : ((W5box N).filter (fun x => x.1 = x.2)).card = Qp N := by
    rw [← support_card_eq_diag hN, support_card_eq_Qp hN]
  rw [hdiag] at hpar
  obtain ⟨t, ht⟩ := five_dvd_T5 hN
  omega

/-- **When ten divides the count.** `10 ∣ T(N,5)` exactly when `Qp N` is even. -/
theorem ten_dvd_T5_iff {N : ℕ} (hN : 0 < N) : 10 ∣ T5 N ↔ Even (Qp N) := by
  have h := T5_mod_ten hN
  constructor
  · intro hdvd
    obtain ⟨t, ht⟩ := hdvd
    rcases Nat.even_or_odd (Qp N) with he | ho
    · exact he
    · exfalso; obtain ⟨j, hj⟩ := ho; omega
  · rintro ⟨j, hj⟩
    omega

end VicoEnum