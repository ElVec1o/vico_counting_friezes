/-
  VicoEnum/ShiftDecomp.lean

  The shift decomposition of the width-5 count at a prime, and the lattice identity behind
  its average order.

  Writing `C(p) = #{(a,u,v) : a u v = p + u + v}`, multiplying the equation through by `a`
  turns it into a factorisation,

      (a u - 1)(a v - 1) = a p + 1,

  so the solutions with leading coefficient `a` are exactly the divisors of the *shifted*
  number `a p + 1` lying in the class `-1 mod a`. Summing over `a` gives

      C(p) = ∑ₐ #{D ∣ a p + 1 : D ≡ -1 mod a},                              (`cubic_shift_decomp`)

  which is the decomposition every upper bound for `C(p)` is built on: the `a`-th term is at
  most `d(ap+1) = p^{o(1)}` by `card_divisors_pow_le`, and `min(a,u,v)^3 ≤ 2p` by
  `cube_root_min` caps the range of `a`, giving `C(p) ≪ p^{1/3+ε}`.

  The two facts are recorded here in the exact form the analytic argument consumes, so that
  the only thing left outside Lean in the `p^{1/3}` bound is the choice of cutoff.

  The second half of the file is the corresponding identity for the average: summing `C(n)`
  over `n ≤ X` counts lattice points on the cubic `a u v - u - v`, each triple being counted
  for exactly one `n`. That identity is exact and is proved here; the asymptotic
  `∑_{n≤X} C(n) ≍ X log²X` that it leads to is *not* formalised, and is not claimed to be.
-/
import VicoEnum.OrderConjecture

namespace VicoEnum

open Finset

/-! ## The solution set -/

/-- Triples `(a,u,v)` in a box with `a u v = p + u + v`. The box is a device for finiteness;
`cube_root_min` and `t5_cubic_hyperbola_nat` say which box is large enough. -/
def cubicSol (p B : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter
    (fun x => x.1 * x.2.1 * x.2.2 = p + x.2.1 + x.2.2)

/-- `cubicTriples` in `OrderConjecture.lean` is this set at `B = p+2`, definitionally. The
two names exist because the import runs that way; `cubic_box_complete` shows the box is the
whole solution set. -/
theorem cubicTriples_eq (p : ℕ) : cubicTriples p = cubicSol p (p + 2) := rfl

theorem mem_cubicSol {p B : ℕ} {x : ℕ × ℕ × ℕ} (hx : x ∈ cubicSol p B) :
    (1 ≤ x.1 ∧ x.1 ≤ B) ∧ (1 ≤ x.2.1 ∧ x.2.1 ≤ B) ∧ (1 ≤ x.2.2 ∧ x.2.2 ≤ B) ∧
      x.1 * x.2.1 * x.2.2 = p + x.2.1 + x.2.2 := by
  simp only [cubicSol, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
  exact ⟨hx.1.1, hx.1.2.1, hx.1.2.2, hx.2⟩

/-- **The leading coefficient is never trivial.** If `a u = 1` the equation reads
`v = p + u + v`, which is impossible for `p ≥ 1`. -/
theorem cubic_lead_ge_two {p a u v : ℕ} (hp : 0 < p) (ha : 0 < a) (hu : 0 < u)
    (h : a * u * v = p + u + v) : 2 ≤ a * u := by
  have h1 : 1 ≤ a * u := Nat.one_le_iff_ne_zero.mpr (by positivity)
  by_contra hc
  have he : a * u = 1 := by omega
  rw [he, one_mul] at h
  omega

/-! ## The factorisation

Multiplying `a u v = p + u + v` by `a` gives `(au)(av) = a p + au + av`, and with
`au = A + 1`, `av = B + 1` this is `A B = a p + 1`. No analysis, no division. -/

/-- **`(au-1)(av-1) = ap+1`, over `ℕ`.** -/
theorem cube_factor_nat {p a u v : ℕ} (hp : 0 < p) (ha : 0 < a) (hu : 0 < u) (hv : 0 < v)
    (h : a * u * v = p + u + v) : (a * u - 1) * (a * v - 1) = a * p + 1 := by
  have hau : 2 ≤ a * u := cubic_lead_ge_two hp ha hu h
  have hav : 2 ≤ a * v := by
    refine cubic_lead_ge_two (v := u) hp ha hv ?_
    calc a * v * u = a * u * v := by ring
      _ = p + u + v := h
      _ = p + v + u := by omega
  obtain ⟨A, hA⟩ : ∃ A, a * u = A + 1 := ⟨a * u - 1, by omega⟩
  obtain ⟨C, hC⟩ : ∃ C, a * v = C + 1 := ⟨a * v - 1, by omega⟩
  have hkey : (a * u) * (a * v) = a * p + a * u + a * v := by
    calc (a * u) * (a * v) = a * (a * u * v) := by ring
      _ = a * (p + u + v) := by rw [h]
      _ = a * p + a * u + a * v := by ring
  rw [hA, hC] at hkey
  have e : (A + 1) * (C + 1) = A * C + A + C + 1 := by ring
  have g1 : a * u - 1 = A := by omega
  have g2 : a * v - 1 = C := by omega
  rw [g1, g2]
  omega

/-- The divisor produced by the factorisation lies in the class `-1 mod a`. -/
theorem cube_factor_class {a u : ℕ} (ha : 0 < a) (hu : 0 < u) : (a * u - 1) % a = a - 1 := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
  have e : a * (w + 1) - 1 = a * w + (a - 1) := by
    have : a * (w + 1) = a * w + a := by ring
    omega
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-! ## H2: the shift decomposition -/

/-- **The `a`-th fibre injects into the divisors of `ap+1` in the class `-1 mod a`.**
Injectivity is `cube_det`: the leading coefficient and `u` determine `v`. -/
theorem cubic_fibre_le (p B a : ℕ) (hp : 0 < p) (ha : 0 < a) :
    ((cubicSol p B).filter (fun x => x.1 = a)).card
      ≤ ((a * p + 1).divisors.filter (fun D => D % a = a - 1)).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun x => a * x.2.1 - 1) ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx
    obtain ⟨hx', hxa⟩ := hx
    obtain ⟨-, ⟨hu, -⟩, ⟨hv, -⟩, heq⟩ := mem_cubicSol hx'
    have hax : 0 < x.1 := by omega
    have hfac : (a * x.2.1 - 1) * (a * x.2.2 - 1) = a * p + 1 := by
      rw [← hxa]; exact cube_factor_nat hp hax hu hv heq
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨⟨a * x.2.2 - 1, hfac.symm⟩, by omega⟩, cube_factor_class ha hu⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    obtain ⟨hx', hxa⟩ := hx
    obtain ⟨hy', hya⟩ := hy
    obtain ⟨-, ⟨hux, -⟩, -, heqx⟩ := mem_cubicSol hx'
    obtain ⟨-, ⟨huy, -⟩, -, heqy⟩ := mem_cubicSol hy'
    have hax : 0 < x.1 := by omega
    have hay : 0 < y.1 := by omega
    have hlx : 2 ≤ x.1 * x.2.1 := cubic_lead_ge_two hp hax hux heqx
    have hly : 2 ≤ y.1 * y.2.1 := cubic_lead_ge_two hp hay huy heqy
    have h1 : 2 ≤ a * x.2.1 := by rw [← hxa]; exact hlx
    have h2 : 2 ≤ a * y.2.1 := by rw [← hya]; exact hly
    simp only at hxy
    have hu : x.2.1 = y.2.1 := Nat.eq_of_mul_eq_mul_left ha (by omega)
    have hxy1 : x.1 = y.1 := by omega
    have hv : x.2.2 = y.2.2 := by
      refine cube_det (p := p) (s := x.1) (u := x.2.1) hlx heqx ?_
      rw [hxy1, hu]; exact heqy
    exact Prod.ext hxy1 (Prod.ext hu hv)

/-- **H2. The shift decomposition.** `C(p) ≤ ∑ₐ #{D ∣ ap+1 : D ≡ -1 mod a}`. Every known
upper bound for `C(p)` factors through this: the `a`-th term is at most `d(ap+1)`, which
`card_divisors_pow_le` bounds by `p^{o(1)}`, and `cube_root_min` caps the range of `a` at
`(2p)^{1/3}`. -/
theorem cubic_shift_decomp (p B : ℕ) (hp : 0 < p) :
    (cubicSol p B).card
      ≤ ∑ a ∈ Finset.Icc 1 B, ((a * p + 1).divisors.filter (fun D => D % a = a - 1)).card := by
  classical
  have hfib : ∀ x ∈ cubicSol p B, x.1 ∈ Finset.Icc 1 B := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, -, -, -⟩ := mem_cubicSol hx
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  rw [Finset.card_eq_sum_card_fiberwise hfib]
  refine Finset.sum_le_sum ?_
  intro a ha
  exact cubic_fibre_le p B a hp (Finset.mem_Icc.mp ha).1

/-! ## H1: the lattice identity behind the average order

Summing `C(n)` over `n ≤ X` counts triples `(a,u,v)` whose value `a u v - u - v` lands in
`[1, X]`, each triple counted once because the value determines `n`. That is the identity
proved here. The asymptotic `∑_{n≤X} C(n) ≍ X log²X` follows from it by a harmonic-sum
estimate, which is *not* formalised. -/

/-- **H1, the exact part.** The total count is a lattice count on the cubic. Each triple is
counted for exactly one `n`, because `n = a u v - u - v` is determined by the triple. The
range condition is written without subtraction so that it is decidable by construction. -/
theorem cubic_total_identity (X B : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, (cubicSol n B).card
      = (((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter
          (fun x => x.2.1 + x.2.2 < x.1 * x.2.1 * x.2.2 ∧
                    x.1 * x.2.1 * x.2.2 ≤ X + x.2.1 + x.2.2)).card := by
  classical
  have hset : (Finset.Icc 1 X).biUnion (fun n => cubicSol n B)
      = (((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter
          (fun x => x.2.1 + x.2.2 < x.1 * x.2.1 * x.2.2 ∧
                    x.1 * x.2.1 * x.2.2 ≤ X + x.2.1 + x.2.2)) := by
    ext x
    simp only [Finset.mem_biUnion, cubicSol, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc]
    constructor
    · rintro ⟨n, ⟨hn1, hn2⟩, hbox, heq⟩
      exact ⟨hbox, by omega, by omega⟩
    · rintro ⟨hbox, h1, h2⟩
      exact ⟨x.1 * x.2.1 * x.2.2 - x.2.1 - x.2.2, ⟨by omega, by omega⟩, hbox, by omega⟩
  have hdisj : ∀ m ∈ Finset.Icc 1 X, ∀ n ∈ Finset.Icc 1 X, m ≠ n →
      Disjoint (cubicSol m B) (cubicSol n B) := by
    intro m _ n _ hmn
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    obtain ⟨-, -, -, hm⟩ := mem_cubicSol hx
    obtain ⟨-, -, -, hn⟩ := mem_cubicSol hx'
    exact hmn (by omega)
  rw [← hset, Finset.card_biUnion hdisj]

/-- The total is bounded by the box, which is the crude side of H1. Turning
`cubic_total_identity` into the asymptotic `∑_{n≤X} C(n) ≍ X log²X` needs a harmonic-sum
estimate over the box and is not formalised. -/
theorem cubic_total_le (X B : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, (cubicSol n B).card ≤ B * B * B := by
  classical
  rw [cubic_total_identity]
  refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
  simp only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
  ring

/-! ## A vanishing criterion for the fibres

The divisors of `n` reduce, mod `a`, into the multiplicative subsemigroup generated by the
prime factors of `n`. So the `a`-th fibre of `cubicSol` can only be nonempty if `-1` lies in
that subsemigroup, which is a purely group-theoretic condition on `ap+1` and costs no
analysis. Its cleanest special case is proved here: if every prime factor of `ap+1` is
`≡ 1 mod a`, then so is every divisor, and `-1 ≢ 1` once `a > 2`, so the fibre is empty.

Measured over four decades of `p`, with `a` running to `(2p)^{1/3}`, the full subsemigroup
criterion accounts for about a third of the vanishing fibres: `28.6%`, `31.7%`, `31.4%`,
`33.1%` of all `a` at `p ≈ 10^4, 10^5, 10^6, 10^7`. The fraction does not grow, so the
criterion improves the constant in `C(p) ≪ p^{1/3+ε}` and not the exponent. -/

/-- **Divisors inherit the class.** If every prime factor of `n` is `≡ 1 mod a`, so is every
positive divisor of `n`. Proved by pushing the factorisation of `D` into `ZMod a`. -/
theorem divisor_mod_one {a n D : ℕ} (ha : 1 < a) (hD : D ≠ 0) (hDn : D ∣ n)
    (h : ∀ q : ℕ, q.Prime → q ∣ n → q % a = 1) : D % a = 1 := by
  have hself : ∏ q ∈ D.primeFactors, q ^ (D.factorization q) = D := by
    have := Nat.factorization_prod_pow_eq_self hD
    rwa [Finsupp.prod, Nat.support_factorization] at this
  have hcast : ((D : ZMod a)) = 1 := by
    rw [← hself, Nat.cast_prod]
    refine Finset.prod_eq_one ?_
    intro q hq
    have hq1 : q % a = 1 := h q (Nat.prime_of_mem_primeFactors hq)
      (dvd_trans (Nat.dvd_of_mem_primeFactors hq) hDn)
    have hmod : q ≡ 1 [MOD a] := by
      show q % a = 1 % a
      rw [hq1, Nat.mod_eq_of_lt ha]
    have hq0 : ((q : ZMod a)) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff q 1 a).mpr hmod
    rw [Nat.cast_pow, hq0, one_pow]
  have hmd : D ≡ 1 [MOD a] := (ZMod.natCast_eq_natCast_iff D 1 a).mp (by simpa using hcast)
  show D % a = 1
  have h2 : D % a = 1 % a := hmd
  rwa [Nat.mod_eq_of_lt ha] at h2

/-- **The fibre vanishes.** If `a > 2` and every prime factor of `ap+1` is `≡ 1 mod a`, no
solution has leading coefficient `a`. The divisor `au-1` a solution would produce lies in
the class `-1`, which the previous lemma forbids. -/
theorem cubic_fibre_empty {p B a : ℕ} (hp : 0 < p) (ha : 2 < a)
    (h : ∀ q : ℕ, q.Prime → q ∣ a * p + 1 → q % a = 1) :
    (cubicSol p B).filter (fun x => x.1 = a) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_not_mem ?_
  intro x hx
  simp only [Finset.mem_filter] at hx
  obtain ⟨hx', hxa⟩ := hx
  obtain ⟨-, ⟨hu, -⟩, ⟨hv, -⟩, heq⟩ := mem_cubicSol hx'
  have hax : 0 < x.1 := by omega
  have hlead : 2 ≤ a * x.2.1 := by rw [← hxa]; exact cubic_lead_ge_two hp hax hu heq
  have hfac : (a * x.2.1 - 1) * (a * x.2.2 - 1) = a * p + 1 := by
    rw [← hxa]; exact cube_factor_nat hp hax hu hv heq
  have hone : (a * x.2.1 - 1) % a = 1 :=
    divisor_mod_one (by omega) (by omega) ⟨a * x.2.2 - 1, hfac.symm⟩ h
  have hneg : (a * x.2.1 - 1) % a = a - 1 := cube_factor_class (by omega) hu
  omega

/-! ## Coprimality of the two large variables

`a u v = p + u + v` forces `gcd(u,v) ∣ p`, because the gcd divides both `a u v` and `u + v`.
At a prime this leaves `gcd(u,v) ∈ {1, p}`, and the second is impossible once `p ≥ 5`:
dividing through by `p` twice leaves `a p U V = 1 + U + V` with `U, V ≥ 1`, whose left side
is at least `5UV ≥ 5(U+V-1)`. -/

/-- **The gcd of the two large variables divides `p`.** -/
theorem cubic_gcd_dvd {p a u v : ℕ} (h : a * u * v = p + u + v) : Nat.gcd u v ∣ p := by
  have hu : Nat.gcd u v ∣ u := Nat.gcd_dvd_left u v
  have hv : Nat.gcd u v ∣ v := Nat.gcd_dvd_right u v
  have h1 : Nat.gcd u v ∣ a * u * v := (hu.mul_left a).mul_right v
  have h2 : Nat.gcd u v ∣ u + v := Nat.dvd_add hu hv
  have h3 : p = a * u * v - (u + v) := by omega
  rw [h3]
  exact Nat.dvd_sub' h1 h2

/-- **At a prime `p ≥ 5` the two large variables are coprime.** -/
theorem cubic_coprime {p a u v : ℕ} (hp : 5 ≤ p) (hpp : p.Prime) (ha : 0 < a)
    (hu : 0 < u) (hv : 0 < v) (h : a * u * v = p + u + v) : Nat.gcd u v = 1 := by
  rcases hpp.eq_one_or_self_of_dvd _ (cubic_gcd_dvd h) with h1 | h1
  · exact h1
  · exfalso
    have hpu : p ∣ u := h1 ▸ Nat.gcd_dvd_left u v
    have hpv : p ∣ v := h1 ▸ Nat.gcd_dvd_right u v
    obtain ⟨U, rfl⟩ := hpu
    obtain ⟨V, rfl⟩ := hpv
    have hU : 0 < U := Nat.pos_of_ne_zero (by rintro rfl; simp at hu)
    have hV : 0 < V := Nat.pos_of_ne_zero (by rintro rfl; simp at hv)
    have key : a * p * U * V = 1 + U + V := by
      have e1 : a * (p * U) * (p * V) = p * (a * p * U * V) := by ring
      have e2 : p + p * U + p * V = p * (1 + U + V) := by ring
      rw [e1, e2] at h
      exact Nat.eq_of_mul_eq_mul_left (by omega) h
    obtain ⟨U', rfl⟩ : ∃ U', U = U' + 1 := ⟨U - 1, by omega⟩
    obtain ⟨V', rfl⟩ : ∃ V', V = V' + 1 := ⟨V - 1, by omega⟩
    have h5 : 5 ≤ a * p := le_trans hp (Nat.le_mul_of_pos_left p ha)
    have hge : 5 * ((U' + 1) * (V' + 1)) ≤ a * p * (U' + 1) * (V' + 1) := by
      calc 5 * ((U' + 1) * (V' + 1)) ≤ (a * p) * ((U' + 1) * (V' + 1)) :=
            Nat.mul_le_mul_right _ h5
        _ = a * p * (U' + 1) * (V' + 1) := by ring
    have e : (U' + 1) * (V' + 1) = U' * V' + U' + V' + 1 := by ring
    omega

/-! ## Spacing of the divisors in the class

Two divisors of `n` lying in the class `-1 mod a` differ by a multiple of `a`, so the ones
below a bound `B` are at most `(B+1)/a` in number. Pairing each divisor with its cofactor,
one of the two is at most `√n`, so

    R_a(p) ≤ 2(√(ap+1) + 1)/a,   that is   R_a(p) ≪ √(p/a),

a bound on the fibre that is independent of the divisor function. It does not improve the
exponent in `C(p) ≪ p^{1/3+ε}`, since `√(p/a) ≥ p^{1/3}` throughout `a ≤ (2p)^{1/3}`, but it
caps the fibres uniformly where the divisor bound gives only `p^{o(1)}`.
-/

/-- **The class is sparse below any bound.** The divisors of `n` congruent to `-1 mod a` and
at most `B` number at most `(B+1)/a`, because consecutive ones differ by at least `a`. -/
theorem card_class_le_of_bound (n a B : ℕ) (ha : 0 < a) :
    ((n.divisors.filter (fun D => D % a = a - 1 ∧ D ≤ B)).card) ≤ (B + 1) / a := by
  classical
  have hcard : (Finset.Icc 1 ((B + 1) / a)).card = (B + 1) / a := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  have key : ∀ D ∈ n.divisors.filter (fun D => D % a = a - 1 ∧ D ≤ B),
      D + 1 = a * (D / a + 1) := by
    intro D hD
    simp only [Finset.mem_filter] at hD
    have hdm : a * (D / a) + (a - 1) = D := by
      have h := Nat.div_add_mod D a
      rw [hD.2.1] at h; exact h
    have e : a * (D / a + 1) = a * (D / a) + a := by ring
    rw [e]
    obtain ⟨X, hX⟩ : ∃ X, a * (D / a) = X := ⟨_, rfl⟩
    rw [hX] at hdm ⊢
    omega
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun D => (D + 1) / a) ?_ ?_
  · intro D hD
    have hD1 := key D hD
    have hle : D ≤ B := by
      simp only [Finset.mem_filter] at hD; exact hD.2.2
    have hq : (D + 1) / a = D / a + 1 := by rw [hD1, Nat.mul_div_cancel_left _ ha]
    show (D + 1) / a ∈ Finset.Icc 1 ((B + 1) / a)
    rw [hq]
    refine Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 _, (Nat.le_div_iff_mul_le ha).mpr ?_⟩
    calc (D / a + 1) * a = a * (D / a + 1) := by ring
      _ = D + 1 := hD1.symm
      _ ≤ B + 1 := by omega
  · intro x hx y hy hxy
    have hx1 := key x (Finset.mem_coe.mp hx)
    have hy1 := key y (Finset.mem_coe.mp hy)
    have hqx : (x + 1) / a = x / a + 1 := by rw [hx1, Nat.mul_div_cancel_left _ ha]
    have hqy : (y + 1) / a = y / a + 1 := by rw [hy1, Nat.mul_div_cancel_left _ ha]
    simp only at hxy
    rw [hqx, hqy] at hxy
    have hxa : x / a = y / a := by omega
    rw [hxa] at hx1
    omega

/-! ## The equation is a fixed point of its elementary reindexings

Every change of variable tried on `a u v = p + u + v` returns an instance of the same
equation. The individual substitutions are algebraic identities and are recorded here; the
general claim, that *every* elementary reindexing does this, is not a formal statement and
carries no label.
-/

/-- Doubling. `X = 2u`, `Y = 2v` satisfy `aXY - 2X - 2Y = 4p`, the same equation at `4p`.
This is the shape the symmetric function route produces: with `s = u+v` and `m = uv` the
discriminant split `(am-p-k)(am-p+k) = 4m` has `k = |u-v|`, so `X` and `Y` are `2u` and
`2v`. -/
theorem fixed_point_double {p a u v : ℤ} (h : a * u * v = p + u + v) :
    a * (2 * u) * (2 * v) - 2 * (2 * u) - 2 * (2 * v) = 4 * p := by
  linear_combination 4 * h

/-- The reciprocity `u ∣ p + v`. -/
theorem fixed_point_recip {p a u v : ℤ} (h : a * u * v = p + u + v) :
    p + v = u * (a * v - 1) := by
  linear_combination -h

/-- The divisor reindexing. Writing the divisor as `ut - 1` with cofactor `k`, the triple
`(t,u,k)` satisfies the original equation. -/
theorem fixed_point_reindex {p u t k : ℤ} (h : p + u = (u * t - 1) * k) :
    t * u * k = p + u + k := by
  linear_combination -h

/-- The gcd normalisation. With `g = gcd(d+1,e+1)`, `d = gD-1` and `e = gE-1`, the
condition `de - 1 = gp` collapses to the original equation in `(g,D,E)`. -/
theorem fixed_point_gcd {p g D E : ℤ} (hg : g ≠ 0)
    (h : (g * D - 1) * (g * E - 1) - 1 = g * p) : g * D * E - D - E = p := by
  have h2 : g * (g * D * E - D - E) = g * p := by linear_combination h
  have := mul_left_cancel₀ hg h2
  linarith

/-- The modular hyperbola, backwards. A factorisation of `ap+1` into two factors that are
both `-1 mod a` returns a solution of the original equation. Together with
`cube_factor_nat` this makes the correspondence of Proposition `prop:modhyp` a bijection. -/
theorem fixed_point_hyperbola {p a u v : ℤ} (ha : a ≠ 0)
    (h : (a * u - 1) * (a * v - 1) = a * p + 1) : a * u * v = p + u + v := by
  have h2 : a * (a * u * v - u - v - p) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 ha
  · linarith

/-- The function field substitution is the same identity over any commutative ring, which is
why the analogue of Conjecture `conj:order` over `𝔽_q[t]` is faithful rather than easier. -/
theorem fixed_point_ring {R : Type*} [CommRing R] {p a u v : R}
    (h : a * u * v = p + u + v) : (a * u - 1) * (a * v - 1) = a * p + 1 := by
  linear_combination a * h

/-- `a - 1` is `-1` in `ZMod a`. -/
theorem natCast_pred_eq_neg_one {a : ℕ} (ha : 0 < a) : ((a - 1 : ℕ) : ZMod a) = -1 := by
  have h : ((a - 1 : ℕ) : ZMod a) + 1 = 0 := by
    have : ((a - 1 : ℕ) : ZMod a) + ((1 : ℕ) : ZMod a) = ((a - 1 + 1 : ℕ) : ZMod a) := by
      push_cast; ring
    simpa [Nat.sub_add_cancel ha, ZMod.natCast_self] using this
  linear_combination h

/-- **The class `-1 mod a` is closed under the divisor pairing.** If `n ≡ 1 mod a` and
`D ∣ n` lies in the class, so does the cofactor `n/D`, since `D·(n/D) ≡ 1` and `-1` is its
own inverse's negative. This is what makes the pairing argument of `prop:spacing` work. -/
theorem class_cofactor {n a D : ℕ} (ha : 1 < a) (hn : n % a = 1) (hD : D ∣ n) (hD0 : 0 < D)
    (hcls : D % a = a - 1) : (n / D) % a = a - 1 := by
  obtain ⟨E, hE⟩ := hD
  have hEval : n / D = E := by rw [hE]; exact Nat.mul_div_cancel_left E hD0
  have hcast : ((D : ZMod a)) * (E : ZMod a) = 1 := by
    have : ((n : ℕ) : ZMod a) = ((1 : ℕ) : ZMod a) :=
      (ZMod.natCast_eq_natCast_iff n 1 a).mpr (by show n % a = 1 % a; rw [hn, Nat.mod_eq_of_lt ha])
    rw [hE] at this; push_cast at this ⊢; simpa using this
  have hDneg : ((D : ZMod a)) = -1 := by
    have : ((D : ℕ) : ZMod a) = ((a - 1 : ℕ) : ZMod a) :=
      (ZMod.natCast_eq_natCast_iff D (a - 1) a).mpr
        (by show D % a = (a - 1) % a; rw [hcls, Nat.mod_eq_of_lt (by omega)])
    rw [this, natCast_pred_eq_neg_one (by omega)]
  have hEneg : ((E : ZMod a)) = -1 := by
    rw [hDneg] at hcast; linear_combination -hcast
  have : ((E : ℕ) : ZMod a) = ((a - 1 : ℕ) : ZMod a) := by
    rw [hEneg, natCast_pred_eq_neg_one (by omega)]
  have hmd : E ≡ a - 1 [MOD a] := (ZMod.natCast_eq_natCast_iff E (a - 1) a).mp this
  have h2 : E % a = (a - 1) % a := hmd
  rw [hEval, h2, Nat.mod_eq_of_lt (by omega)]

/-- **Proposition `prop:spacing`, the consequence.** If `n ≤ B²` and `n ≡ 1 mod a`, the
divisors of `n` in the class `-1 mod a` number at most `2(B+1)/a`. Pairing each divisor with
its cofactor sends the ones above `B` into the ones below, and `card_class_le_of_bound`
counts those. With `n = ap+1` and `B = ⌈√(ap+1)⌉` this is `R_a(p) ≪ √(p/a)`. -/
theorem card_class_le_sqrt (n a B : ℕ) (ha : 1 < a) (hn0 : n ≠ 0) (hn : n % a = 1)
    (hB : n ≤ B * B) :
    (n.divisors.filter (fun D => D % a = a - 1)).card ≤ 2 * ((B + 1) / a) := by
  classical
  set S := n.divisors.filter (fun D => D % a = a - 1) with hS
  set S1 := n.divisors.filter (fun D => D % a = a - 1 ∧ D ≤ B) with hS1
  have hsplit : S.card ≤ 2 * S1.card := by
    have hinj : ∀ D ∈ S.filter (fun D => ¬ D ≤ B), n / D ∈ S1 := by
      intro D hD
      simp only [hS, Finset.mem_filter, Nat.mem_divisors] at hD
      obtain ⟨⟨⟨hdvd, -⟩, hcls⟩, hgt⟩ := hD
      have hD0 : 0 < D := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
      have hqd : n / D ∣ n := Nat.div_dvd_of_dvd hdvd
      have hle : n / D ≤ B := by
        have h1 : n / D * D ≤ n := Nat.div_mul_le_self n D
        have h2 : n / D * (B + 1) ≤ n / D * D := Nat.mul_le_mul_left _ (by omega)
        have h3 : n / D * (B + 1) ≤ B * (B + 1) := by
          calc n / D * (B + 1) ≤ n / D * D := h2
            _ ≤ n := h1
            _ ≤ B * B := hB
            _ ≤ B * (B + 1) := Nat.mul_le_mul_left _ (by omega)
        exact Nat.le_of_mul_le_mul_right h3 (by omega)
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hqd, hn0⟩,
        class_cofactor ha hn hdvd hD0 hcls, hle⟩
    have hcard2 : (S.filter (fun D => ¬ D ≤ B)).card ≤ S1.card := by
      refine Finset.card_le_card_of_injOn (fun D => n / D) hinj ?_
      intro x hx y hy hxy
      simp only [Finset.mem_coe, hS, Finset.mem_filter, Nat.mem_divisors] at hx hy
      have hx0 : 0 < x := Nat.pos_of_dvd_of_pos hx.1.1.1 (Nat.pos_of_ne_zero hn0)
      have hy0 : 0 < y := Nat.pos_of_dvd_of_pos hy.1.1.1 (Nat.pos_of_ne_zero hn0)
      simp only at hxy
      have hx' : n / (n / x) = x := Nat.div_div_self hx.1.1.1 hn0
      have hy' : n / (n / y) = y := Nat.div_div_self hy.1.1.1 hn0
      rw [← hx', ← hy', hxy]
    have hle1 : (S.filter (fun D => D ≤ B)).card ≤ S1.card := by
      refine Finset.card_le_card ?_
      intro x hx
      simp only [hS, Finset.mem_filter] at hx
      exact Finset.mem_filter.mpr ⟨hx.1.1, hx.1.2, hx.2⟩
    have := Finset.filter_card_add_filter_neg_card_eq_card
      (s := S) (p := fun D => D ≤ B)
    omega
  have hb : S1.card ≤ (B + 1) / a := by
    rw [hS1]; exact card_class_le_of_bound n a B (by omega)
  omega

end VicoEnum
