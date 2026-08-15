/-
  VicoEnum/ACountFull.lean

  Lemma `lem:acount`: `A(p) = 5 + 2C(p)` for a prime `p ≥ 5`.

  `ACount.lean` proves the arithmetic of the correspondence and says outright that the count
  itself is not proved there. This file supplies it, and with `thm:orbit` it is what carries
  the paper's identification `T(p,5) = 5 + 5C(p)`.

  The argument has three parts. The condition `uv ∣ p(u+v+1)` is symmetric in `u` and `v`, and
  `gcd(u,v) = 1` means `p` divides at most one of them, so the pairs split into three disjoint
  classes: `p ∤ uv`, `p ∣ u`, and `p ∣ v`. The first class is the five pairs of
  `prop:rigid5`. The second is in bijection with the cubic through `u = ps`, `v = st-1`. The
  third has the same size as the second, by exchanging the coordinates.

  Everything is placed inside the box `[1,(p+2)^2]^2`, which contains every solution: the five
  rigid pairs have entries at most `3`, and in the other two classes `u = ps` and `v = st-1`
  with `s,t ≤ p+2` by `cubic_box_complete`.
-/
import VicoEnum.OrderConjecture
import VicoEnum.Bounds5
import VicoEnum.ACount

namespace VicoEnum

open Finset

/-- The pairs counted by `A(p)`. -/
def ASet (p : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 ((p + 2) ^ 2)) ×ˢ (Finset.Icc 1 ((p + 2) ^ 2))).filter
    (fun x => Nat.gcd x.1 x.2 = 1 ∧ x.1 * x.2 ∣ p * (x.1 + x.2 + 1))

theorem mem_ASet {p : ℕ} {x : ℕ × ℕ} :
    x ∈ ASet p ↔ (1 ≤ x.1 ∧ x.1 ≤ (p + 2) ^ 2) ∧ (1 ≤ x.2 ∧ x.2 ≤ (p + 2) ^ 2) ∧
      Nat.gcd x.1 x.2 = 1 ∧ x.1 * x.2 ∣ p * (x.1 + x.2 + 1) := by
  simp only [ASet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-! ## The box is complete

`ASet` is defined inside `[1,(p+2)^2]^2`. That box contains every solution, so the count is
`A(p)` and not a truncation of it. The three classes each give the bound: the coprime class is
the five rigid pairs, and in the other two `u = ps` and `v = st-1` with `s,t <= p+2` by
`cubic_box_complete`. -/

/-- **Every solution lies in the box.** -/
theorem ASet_bound {p u v : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hg : Nat.gcd u v = 1) (hd : u * v ∣ p * (u + v + 1)) :
    u ≤ (p + 2) ^ 2 ∧ v ≤ (p + 2) ^ 2 := by
  -- the half that does the work, stated for `p ∣ u` and applied twice
  have key : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Nat.gcd a b = 1 → a * b ∣ p * (a + b + 1) →
      p ∣ a → a ≤ p * (p + 2) ∧ b ≤ (p + 2) ^ 2 := by
    intro a b ha hb hgab hdab hpa
    obtain ⟨s, rfl⟩ := hpa
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with rfl | h
      · simp at ha
      · exact h
    -- `s ∣ b+1`
    have hsb : s ∣ b + 1 := by
      have h1 : p * s ∣ p * (p * s + b + 1) :=
        dvd_trans (dvd_mul_right (p * s) b) hdab
      have h2 : s ∣ p * s + b + 1 := by
        have := (mul_dvd_mul_iff_left hp.pos.ne').mp h1
        exact this
      have h3 : s ∣ p * s := Dvd.dvd.mul_left dvd_rfl p
      have h4 := Nat.dvd_sub' h2 h3
      rwa [show p * s + b + 1 - p * s = b + 1 from by omega] at h4
    obtain ⟨t, ht⟩ := hsb
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · omega
      · exact h
    -- `(st-1) ∣ (p+t)`
    have hb : s * t - 1 = b := by omega
    have hdt : (s * t - 1) ∣ p + t := by
      have e2 : p * (p * s + b + 1) = p * s * (p + t) := by
        have hh : p * s + b + 1 = p * s + s * t := by omega
        rw [hh]; ring
      have h5' : p * s * (s * t - 1) ∣ p * s * (p + t) := by
        rw [hb, ← e2]; exact hdab
      exact (mul_dvd_mul_iff_left (by positivity : p * s ≠ 0)).mp h5'
    obtain ⟨m, hm⟩ := hdt
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · omega
      · exact h
    have hrel : s * t * m = p + t + m := acount_backward (by omega) hm.symm
    have hbox := cubic_box_complete (by omega : 0 < s) (by omega : 0 < t) (by omega : 0 < m) hrel
    exact ⟨by nlinarith [hbox.1], by nlinarith [hbox.2.1, hbox.1, h5]⟩
  by_cases hpu : p ∣ u
  · obtain ⟨h1, h2⟩ := key u v hu hv hg hd hpu
    exact ⟨by nlinarith [h1], h2⟩
  by_cases hpv : p ∣ v
  · have hd' : v * u ∣ p * (v + u + 1) := by
      rw [Nat.mul_comm, show v + u + 1 = u + v + 1 from by omega]; exact hd
    obtain ⟨h1, h2⟩ := key v u hv hu (by rwa [Nat.gcd_comm]) hd' hpv
    exact ⟨h2, by nlinarith [h1]⟩
  · -- neither: the five rigid pairs
    have hcop : Nat.Coprime (u * v) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (fun h => (hp.dvd_mul.mp h).elim hpu hpv)).symm
    have hbig : (3 : ℕ) ≤ (p + 2) ^ 2 := by nlinarith [h5]
    rcases t5_prime_rigid hu hv hcop hd with h | h | h | h | h <;>
      exact ⟨by omega, by omega⟩

/-! ## The three classes -/

/-- The pairs with `p` dividing neither coordinate. -/
def Acop (p : ℕ) : Finset (ℕ × ℕ) := (ASet p).filter (fun x => ¬ (p ∣ x.1 * x.2))

/-- The pairs with `p ∣ u`. -/
def Aleft (p : ℕ) : Finset (ℕ × ℕ) := (ASet p).filter (fun x => p ∣ x.1)

/-- The pairs with `p ∣ v`. -/
def Aright (p : ℕ) : Finset (ℕ × ℕ) := (ASet p).filter (fun x => p ∣ x.2)

/-- **The three classes are disjoint and cover `ASet`.** `gcd(u,v) = 1` is what forbids `p`
from dividing both. -/
theorem ASet_split {p : ℕ} (hp : p.Prime) :
    (Acop p).card + (Aleft p).card + (Aright p).card = (ASet p).card := by
  classical
  have hdisj1 : Disjoint (Acop p) (Aleft p) := by
    refine Finset.disjoint_left.mpr ?_
    rintro x hx hx'
    simp only [Acop, Aleft, Finset.mem_filter] at hx hx'
    exact hx.2 (Dvd.dvd.mul_right hx'.2 x.2)
  have hdisj2 : Disjoint (Acop p) (Aright p) := by
    refine Finset.disjoint_left.mpr ?_
    rintro x hx hx'
    simp only [Acop, Aright, Finset.mem_filter] at hx hx'
    exact hx.2 (Dvd.dvd.mul_left hx'.2 x.1)
  have hdisj3 : Disjoint (Aleft p) (Aright p) := by
    refine Finset.disjoint_left.mpr ?_
    rintro x hx hx'
    simp only [Aleft, Aright, Finset.mem_filter] at hx hx'
    obtain ⟨-, -, hg, -⟩ := (mem_ASet).mp hx.1
    have hd : p ∣ Nat.gcd x.1 x.2 := Nat.dvd_gcd hx.2 hx'.2
    rw [hg] at hd
    exact absurd (Nat.dvd_one.mp hd) hp.one_lt.ne'
  have hcover : Acop p ∪ Aleft p ∪ Aright p = ASet p := by
    ext x
    simp only [Finset.mem_union, Acop, Aleft, Aright, Finset.mem_filter]
    constructor
    · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h
    · intro hx
      by_cases hc : p ∣ x.1 * x.2
      · rcases (Nat.Prime.dvd_mul hp).mp hc with h | h
        · exact Or.inl (Or.inr ⟨hx, h⟩)
        · exact Or.inr ⟨hx, h⟩
      · exact Or.inl (Or.inl ⟨hx, hc⟩)
  rw [← hcover, Finset.card_union_of_disjoint (by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hx'
      rcases Finset.mem_union.mp hx with h | h
      · exact (Finset.disjoint_left.mp hdisj2) h hx'
      · exact (Finset.disjoint_left.mp hdisj3) h hx'),
    Finset.card_union_of_disjoint hdisj1]

/-! ## The class coprime to `p` is the five rigid pairs -/

/-- **`Acop` is exactly the five pairs of Proposition `prop:rigid5`.** -/
theorem Acop_eq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    Acop p = {(1, 1), (1, 2), (2, 1), (2, 3), (3, 2)} := by
  have hbox : (3 : ℕ) ≤ (p + 2) ^ 2 := by nlinarith [h5]
  have hp2 : ¬ (p ∣ 2) := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hp6 : ¬ (p ∣ 6) := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases p
    · exact absurd h (by norm_num)
    · exact absurd hp (by norm_num)
  ext x
  simp only [Acop, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hnd⟩
    obtain ⟨⟨hu1, -⟩, ⟨hv1, -⟩, hg, hdvd⟩ := (mem_ASet).mp hx
    have hcop : Nat.Coprime (x.1 * x.2) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm
    rcases t5_prime_rigid hu1 hv1 hcop hdvd with h | h | h | h | h <;>
      [exact Or.inl (Prod.ext h.1 h.2);
       exact Or.inr (Or.inl (Prod.ext h.1 h.2));
       exact Or.inr (Or.inr (Or.inl (Prod.ext h.1 h.2)));
       exact Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext h.1 h.2))));
       exact Or.inr (Or.inr (Or.inr (Or.inr (Prod.ext h.1 h.2))))]
  · intro h
    have mk : ∀ a b : ℕ, 1 ≤ a → a ≤ 3 → 1 ≤ b → b ≤ 3 →
        a * b ∣ p * (a + b + 1) → ¬ (p ∣ a * b) → Nat.gcd a b = 1 →
        ((a, b) ∈ ASet p ∧ ¬ (p ∣ (a, b).1 * (a, b).2)) := by
      intro a b ha1 ha3 hb1 hb3 hd hnd hgg
      exact ⟨(mem_ASet).mpr ⟨⟨ha1, by omega⟩, ⟨hb1, by omega⟩, hgg, hd⟩, hnd⟩
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact mk 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by simpa using fun hh => hp.one_lt.ne' (Nat.dvd_one.mp hh)) (by norm_num)
    · exact mk 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        ⟨2 * p, by ring⟩ (by simpa using hp2) (by norm_num)
    · exact mk 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        ⟨2 * p, by ring⟩ (by simpa using hp2) (by norm_num)
    · exact mk 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        ⟨p, by ring⟩ (by simpa using hp6) (by norm_num)
    · exact mk 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        ⟨p, by ring⟩ (by simpa using hp6) (by norm_num)

theorem Acop_card {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : (Acop p).card = 5 := by
  rw [Acop_eq hp h5]; decide

/-! ## The two divisible classes have the same size

The defining condition is symmetric in `u` and `v`, so exchanging the coordinates is a
bijection of `ASet` carrying `Aleft` to `Aright`. -/

theorem swap_mem_ASet {p : ℕ} {x : ℕ × ℕ} (hx : x ∈ ASet p) : x.swap ∈ ASet p := by
  obtain ⟨h1, h2, hg, hd⟩ := (mem_ASet).mp hx
  refine (mem_ASet).mpr ⟨h2, h1, ?_, ?_⟩
  · rw [Prod.fst_swap, Prod.snd_swap, Nat.gcd_comm]; exact hg
  · rw [Prod.fst_swap, Prod.snd_swap, Nat.mul_comm]
    rw [show x.2 + x.1 + 1 = x.1 + x.2 + 1 from by omega]
    exact hd

theorem Aleft_card_eq_Aright {p : ℕ} : (Aleft p).card = (Aright p).card := by
  refine Finset.card_bij' (fun x _ => x.swap) (fun y _ => y.swap) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Aleft, Aright, Finset.mem_filter] at ha ⊢
    exact ⟨swap_mem_ASet ha.1, by simpa using ha.2⟩
  · intro b hb
    simp only [Aleft, Aright, Finset.mem_filter] at hb ⊢
    exact ⟨swap_mem_ASet hb.1, by simpa using hb.2⟩
  · intro a _; simp
  · intro b _; simp

/-! ## The class `p ∣ u` is in bijection with the cubic

The map is `(s,t,m) ↦ (ps, st-1)`. Forward, `ps(st-1) ∣ p(ps + st-1 + 1) = ps(p+t)` reduces to
`(st-1) ∣ (p+t)`, which is the cleared cubic; coprimality is `gcd_image`. Backward, `p ∣ u`
gives `u = ps`, then `s ∣ v+1` puts `v = st-1`, and `(st-1) ∣ (p+t)` supplies `m`. -/

/-- `st ≥ 2` for any solution of the cubic, so `st - 1` is a positive natural. -/
theorem cubic_st_two {p s t m : ℕ} (hp : 0 < p) (h : s * t * m = p + t + m) : 2 ≤ s * t := by
  rcases Nat.lt_or_ge (s * t) 2 with hlt | hge
  · interval_cases h' : (s * t) <;> omega
  · exact hge

/-- **Forward.** A cubic solution gives a pair in `Aleft`. -/
theorem cubic_to_Aleft {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ cubicTriples p) : (p * x.1, x.1 * x.2.1 - 1) ∈ Aleft p := by
  obtain ⟨hbox, hrel⟩ := Finset.mem_filter.mp hx
  simp only [Finset.mem_product, Finset.mem_Icc] at hbox
  obtain ⟨⟨hs1, hs2⟩, ⟨ht1, ht2⟩, hm1, hm2⟩ := hbox
  have hst : 2 ≤ x.1 * x.2.1 := cubic_st_two (by omega) hrel
  have hclear : (x.1 * x.2.1 - 1) * x.2.2 = p + x.2.1 := acount_cubic_clear (by omega) hrel
  refine Finset.mem_filter.mpr ⟨(mem_ASet).mpr ⟨?_, ?_, ?_, ?_⟩, ⟨x.1, rfl⟩⟩
  · exact ⟨by nlinarith [hs1], by nlinarith [hs2, h5]⟩
  · exact ⟨by omega, by nlinarith [hs2, ht2, h5]⟩
  · exact gcd_image hp (by omega) hrel
  · -- `ps(st-1) ∣ p(ps + (st-1) + 1)`, and the right side is `p * s * (p+t)`
    have hsum : p * x.1 + (x.1 * x.2.1 - 1) + 1 = x.1 * (p + x.2.1) := by
      have : x.1 * x.2.1 - 1 + 1 = x.1 * x.2.1 := by omega
      calc p * x.1 + (x.1 * x.2.1 - 1) + 1 = p * x.1 + x.1 * x.2.1 := by omega
        _ = x.1 * (p + x.2.1) := by ring
    rw [hsum, ← hclear]
    exact ⟨x.2.2, by ring⟩

/-- **Injective.** `s` comes from `u = ps`, then `t` from `v = st-1`, then `m` from the
cleared cubic. -/
theorem cubic_to_Aleft_inj {p : ℕ} (hp : p.Prime) {x y : ℕ × ℕ × ℕ}
    (hx : x ∈ cubicTriples p) (hy : y ∈ cubicTriples p)
    (heq : (p * x.1, x.1 * x.2.1 - 1) = (p * y.1, y.1 * y.2.1 - 1)) : x = y := by
  obtain ⟨hbx, hrx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hby, hry⟩ := Finset.mem_filter.mp hy
  simp only [Finset.mem_product, Finset.mem_Icc] at hbx hby
  have hstx : 2 ≤ x.1 * x.2.1 := cubic_st_two hp.pos hrx
  have hsty : 2 ≤ y.1 * y.2.1 := cubic_st_two hp.pos hry
  simp only [Prod.mk.injEq] at heq
  have hs : x.1 = y.1 := Nat.eq_of_mul_eq_mul_left hp.pos heq.1
  have hst : x.1 * x.2.1 = y.1 * y.2.1 := by omega
  have ht : x.2.1 = y.2.1 := by
    rw [hs] at hst; exact Nat.eq_of_mul_eq_mul_left (by omega) hst
  have hm : x.2.2 = y.2.2 := by
    have cx := acount_cubic_clear (by omega) hrx
    have cy := acount_cubic_clear (by omega) hry
    rw [hst, ht] at cx
    exact Nat.eq_of_mul_eq_mul_left (by omega) (cx.trans cy.symm)
  exact Prod.ext hs (Prod.ext ht hm)

/-- **Surjective.** `p ∣ u` gives `u = ps`; then `s ∣ v+1` gives `v = st-1`; then
`(st-1) ∣ (p+t)` gives `m`. -/
theorem Aleft_to_cubic {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {y : ℕ × ℕ}
    (hy : y ∈ Aleft p) :
    ∃ x ∈ cubicTriples p, (p * x.1, x.1 * x.2.1 - 1) = y := by
  obtain ⟨hyA, ⟨s, hs⟩⟩ := Finset.mem_filter.mp hy
  obtain ⟨⟨hu1, -⟩, ⟨hv1, -⟩, hg, hd⟩ := (mem_ASet).mp hyA
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · omega
    · exact h
  -- `s*v ∣ p*s + v + 1`
  have hsv : s * y.2 ∣ p * s + y.2 + 1 := by
    have h1 : p * s * y.2 ∣ p * (p * s + y.2 + 1) := by rw [← hs]; exact hd
    have h2 : p * (s * y.2) ∣ p * (p * s + y.2 + 1) := by
      refine dvd_trans (dvd_of_eq ?_) h1; ring
    exact (mul_dvd_mul_iff_left hp.pos.ne').mp h2
  -- `s ∣ v+1`
  have hsv1 : s ∣ y.2 + 1 := by
    have h3 : s ∣ p * s + y.2 + 1 := dvd_trans (dvd_mul_right s y.2) hsv
    have h4 : s ∣ p * s := Dvd.dvd.mul_left dvd_rfl p
    have h6 := Nat.dvd_sub' h3 h4
    rwa [show p * s + y.2 + 1 - p * s = y.2 + 1 from by omega] at h6
  obtain ⟨t, ht⟩ := hsv1
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · omega
    · exact h
  have hstv : s * t - 1 = y.2 := by omega
  -- `(st-1) ∣ (p+t)`
  have hdt : (s * t - 1) ∣ p + t := by
    have h5' : s * (s * t - 1) ∣ s * (p + t) := by
      have e1 : s * (s * t - 1) = s * y.2 := congrArg (fun z => s * z) hstv
      have e2 : s * (p + t) = p * s + y.2 + 1 := by
        have hh : s * (p + t) = p * s + s * t := by ring
        omega
      rw [e1, e2]; exact hsv
    exact (mul_dvd_mul_iff_left (by omega : s ≠ 0)).mp h5'
  obtain ⟨m, hm⟩ := hdt
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · omega
    · exact h
  have hrel : s * t * m = p + t + m := acount_backward (by omega) hm.symm
  have hbox := cubic_box_complete (by omega : 0 < s) (by omega : 0 < t) (by omega : 0 < m) hrel
  refine ⟨(s, t, m), Finset.mem_filter.mpr ⟨?_, hrel⟩, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨hs1, hbox.1⟩, ⟨ht1, hbox.2.1⟩, hm1, hbox.2.2⟩
  · exact Prod.ext hs.symm hstv

/-! ## The count -/

theorem Aleft_card {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (cubicTriples p).card = (Aleft p).card :=
  Finset.card_bij (fun x _ => (p * x.1, x.1 * x.2.1 - 1))
    (fun _ hx => cubic_to_Aleft hp h5 hx)
    (fun _ hx _ hy h => cubic_to_Aleft_inj hp hx hy h)
    (fun b hb => by
      obtain ⟨x, hx, hxb⟩ := Aleft_to_cubic hp h5 hb
      exact ⟨x, hx, hxb⟩)

/-- **Lemma `lem:acount`.** `A(p) = 5 + 2C(p)` for a prime `p ≥ 5`. -/
theorem acount_eq {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (ASet p).card = 5 + 2 * (cubicTriples p).card := by
  rw [← ASet_split hp, Acop_card hp h5, ← Aleft_card hp h5,
    ← Aleft_card_eq_Aright (p := p), ← Aleft_card hp h5]
  ring

end VicoEnum
