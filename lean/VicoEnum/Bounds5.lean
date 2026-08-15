/-
  VicoEnum/Bounds5.lean

  The width-5 reduction with `g` eliminated, and a linear bound on the parameters.

  Theorem `thm:markov` counts quadruples `(g,u,v,M)` subject to six conditions. Three of
  them are redundant.

  `t5_pos_auto`: the two positivity conditions `gu > N` and `gv > N` are automatic.
  Multiplying `gu > N` by `v > 0` turns it into `N(u+v)+M > Nv`, that is `Nu + M > 0`.

  `t5_elim_g`: `g` is determined by `(u,v,M)`, so the equation `guv = N(u+v)+M` is the
  divisibility `uv ∣ N(u+v)+M`, and `N ∣ gM` becomes `Nuv ∣ M(N(u+v)+M)`.

  What is left is a count of triples subject to three conditions:

      T(N,5) = #{(u,v,M) : gcd(u,v)=1, M ∣ N², uv ∣ N(u+v)+M, Nuv ∣ M(N(u+v)+M)}.

  The gain is not only cosmetic. Since `uv` divides a positive number it is at most that
  number, so

      (u - N)(v - N) ≤ N² + M ≤ 2N²                             (`t5_hyperbola`)

  and with `u ≤ v` this forces `(u-N)² ≤ 2N²`, hence `u < 3N` (`t5_min_bound`). The
  smaller parameter is bounded LINEARLY in `N`, where the bound previously available was
  `N² + 2N`. Since the larger satisfies `v ∣ Nu + M`, it ranges over divisors, and

      T(N,5) ≤ 2 ∑_{M ∣ N²} ∑_{u < 3N} d(Nu + M) = O_ε(N^{1+ε}).

  Both bounds are attained: `(u-N)(v-N) = 2N²` occurs for every `N ≥ 2` tested
  (`code/t5_bounds.py`).
-/
import VicoEnum.Markov

namespace VicoEnum

/-- **The positivity conditions are automatic.** First half of Theorem `thm:t5red`.
Given the width-5 equation with
`u, v, M, N` positive, the two conditions `gu > N` and `gv > N` of Theorem `thm:markov`
hold of themselves, so they impose nothing. -/
theorem t5_pos_auto {N g u v M : ℤ} (hu : 0 < u) (hv : 0 < v) (hM : 0 < M) (hN : 0 < N)
    (h : g * u * v = N * (u + v) + M) : N < g * u ∧ N < g * v := by
  constructor
  · by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hv.le]
  · by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_right hc hu.le]

/-- **`g` can be eliminated.** With `u v ≠ 0`, asking for a `g` solving the width-5
equation and satisfying `N ∣ gM` is the same as two divisibilities in `(u,v,M)` alone. -/
theorem t5_elim_g {N u v M : ℤ} (huv : u * v ≠ 0) :
    (∃ g : ℤ, g * u * v = N * (u + v) + M ∧ N ∣ g * M) ↔
      (u * v ∣ N * (u + v) + M ∧ N * (u * v) ∣ M * (N * (u + v) + M)) := by
  constructor
  · rintro ⟨g, hg, t, ht⟩
    refine ⟨⟨g, by linear_combination -hg⟩, ⟨t, ?_⟩⟩
    calc M * (N * (u + v) + M) = M * (g * u * v) := by rw [hg]
      _ = (g * M) * (u * v) := by ring
      _ = (N * t) * (u * v) := by rw [ht]
      _ = N * (u * v) * t := by ring
  · rintro ⟨⟨g, hg⟩, ⟨t, ht⟩⟩
    refine ⟨g, by linear_combination -hg, ⟨t, ?_⟩⟩
    have h : (u * v) * (g * M - N * t) = 0 := by linear_combination -M * hg + ht
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 huv
    · linarith [h1]

/-- **The hyperbola bound**, first half of Proposition `prop:hyp`. Since `uv` divides the
positive number `N(u+v)+M` it is at
most that number, and the difference is exactly `(u-N)(v-N) - N²`. -/
theorem t5_hyperbola {N u v M : ℤ} (h : u * v ≤ N * (u + v) + M) :
    (u - N) * (v - N) ≤ N ^ 2 + M := by
  nlinarith [h]

/-- **The smaller parameter is linear in `N`**, second half of Proposition `prop:hyp`.
With `M ∣ N²`, so `M ≤ N²`, and `u ≤ v`,
the hyperbola bound gives `(u-N)² ≤ 2N²`, hence `u < 3N`. The previously available bound
was `u ≤ N² + 2N`, quadratic in `N`. -/
theorem t5_min_bound {N u v M : ℤ} (hN : 0 < N) (hu : 0 < u) (huv : u ≤ v)
    (hM : M ≤ N ^ 2) (h : u * v ≤ N * (u + v) + M) : u < 3 * N := by
  rcases le_or_lt u N with hle | hlt
  · linarith
  · have hyp : (u - N) * (v - N) ≤ N ^ 2 + M := t5_hyperbola h
    have h2 : (u - N) * (v - N) ≤ 2 * N ^ 2 := by linarith
    have hun : 0 < u - N := by linarith
    have hsq : (u - N) ^ 2 ≤ 2 * N ^ 2 := by nlinarith [hun, huv]
    nlinarith [hsq, hN]

/-- **The larger parameter divides `Nu + M`.** From `v ∣ N(u+v)+M` and `v ∣ Nv`. This is
what makes the enumeration a divisor loop rather than a second sweep, and with
`t5_min_bound` it gives `T(N,5) ≤ 2 ∑_{M ∣ N²} ∑_{u < 3N} d(Nu+M)`. -/
theorem t5_large_dvd {N u v M : ℤ} (h : v ∣ N * (u + v) + M) : v ∣ N * u + M := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t - N, by linear_combination ht⟩

/-- The two halves of `uv ∣ S` when `u` and `v` are coprime, which is how the divisor
loop is justified. -/
theorem t5_split {u v S : ℤ} (hc : IsCoprime u v) :
    u * v ∣ S ↔ u ∣ S ∧ v ∣ S := by
  constructor
  · intro h
    exact ⟨dvd_trans (Dvd.intro v rfl) h, dvd_trans (Dvd.intro_left u rfl) h⟩
  · rintro ⟨h1, h2⟩
    exact hc.mul_dvd h1 h2

/-- **Each unordered pair is counted at most twice.** Sending a solution `(u,v,M)` to
`M`, the smaller of `u,v`, the larger, and the bit recording which of the two `u` is, is
injective. With `t5_min_bound` bounding the smaller by `3N` and `t5_large_dvd` placing the
larger among the divisors of `N·(smaller) + M`, this is the counting step of Corollary
`cor:t5upper`, and the factor `2` in that bound is this bit. -/
theorem t5_order_inj :
    Function.Injective
      (fun t : ℤ × ℤ × ℤ => (t.2.2, min t.1 t.2.1, max t.1 t.2.1, decide (t.1 ≤ t.2.1))) := by
  rintro ⟨u₁, v₁, M₁⟩ ⟨u₂, v₂, M₂⟩ h
  simp only [Prod.mk.injEq, decide_eq_decide] at h
  obtain ⟨hM, hmin, hmax, hb⟩ := h
  subst hM
  by_cases h1 : u₁ ≤ v₁
  · have h2 : u₂ ≤ v₂ := hb.mp h1
    rw [min_eq_left h1, min_eq_left h2] at hmin
    rw [max_eq_right h1, max_eq_right h2] at hmax
    subst hmin; subst hmax; rfl
  · have h2 : ¬ u₂ ≤ v₂ := fun hc => h1 (hb.mpr hc)
    push_neg at h1 h2
    rw [min_eq_right h1.le, min_eq_right h2.le] at hmin
    rw [max_eq_left h1.le, max_eq_left h2.le] at hmax
    subst hmin; subst hmax; rfl

/-! ## Why the count is small at primes

At a prime `N = p` the support condition of Proposition `prop:support` leaves only
`M ∈ {p, p²}`, and the `M = p` term counts pairs with `uv ∣ p(u+v+1)`. The part of that
solution set coprime to `p` is rigid: it consists of exactly five pairs, whatever `p` is.
So all remaining solutions require `p ∣ uv`, which is why `T(p,5)` stays small. It is also
why the numerical lower bound `T(N,5) ≥ cN` fails: the minimisers are primes.

The five pairs are conjectured to form a single orbit of the rotation action of `ℤ/5`,
which is neither proved nor checked here, consistent with
`no_pos_rat_root`. Coprimality of `u` and `v` is not needed. -/

/-- **Rigidity away from `p`.** If `uv` is coprime to `p` and `uv ∣ p(u+v+1)`, then
`(u,v)` is one of five pairs, independent of `p`. -/
theorem t5_prime_rigid {p u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hp : Nat.Coprime (u * v) p) (h : u * v ∣ p * (u + v + 1)) :
    (u = 1 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
      (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) := by
  have hup : Nat.Coprime u p := Nat.Coprime.coprime_dvd_left (dvd_mul_right u v) hp
  have hvp : Nat.Coprime v p := Nat.Coprime.coprime_dvd_left (dvd_mul_left v u) hp
  have hdu : u ∣ p * (u + v + 1) := dvd_trans (dvd_mul_right u v) h
  have hdv : v ∣ p * (u + v + 1) := dvd_trans (dvd_mul_left v u) h
  have h1 : u ∣ v + 1 := by
    have := (Nat.Coprime.dvd_of_dvd_mul_left hup hdu)
    have h2 : u ∣ (u + v + 1) - u := Nat.dvd_sub' this dvd_rfl
    have h3 : u + v + 1 - u = v + 1 := by omega
    rwa [h3] at h2
  have h2 : v ∣ u + 1 := by
    have := (Nat.Coprime.dvd_of_dvd_mul_left hvp hdv)
    have h3 : v ∣ (u + v + 1) - v := Nat.dvd_sub' this dvd_rfl
    have h4 : u + v + 1 - v = u + 1 := by omega
    rwa [h4] at h3
  have hle1 : u ≤ v + 1 := Nat.le_of_dvd (by omega) h1
  have hle2 : v ≤ u + 1 := Nat.le_of_dvd (by omega) h2
  rcases Nat.lt_trichotomy u v with hlt | heq | hgt
  · -- u < v, so v = u + 1
    have hv1 : v = u + 1 := by omega
    subst hv1
    have : u ∣ 2 := by
      have h5 : u ∣ (u + 1 + 1) - u := Nat.dvd_sub' h1 dvd_rfl
      have h6 : u + 1 + 1 - u = 2 := by omega
      rwa [h6] at h5
    have hu2 : u ≤ 2 := Nat.le_of_dvd (by norm_num) this
    interval_cases u
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · -- u = v forces u = 1
    subst heq
    have : u ∣ 1 := by
      have h5 : u ∣ (u + 1) - u := Nat.dvd_sub' h2 dvd_rfl
      have h6 : u + 1 - u = 1 := by omega
      rwa [h6] at h5
    have hu1' : u = 1 := Nat.dvd_one.mp this
    exact Or.inl ⟨hu1', hu1'⟩
  · -- v < u, so u = v + 1
    have hu1 : u = v + 1 := by omega
    subst hu1
    have : v ∣ 2 := by
      have h5 : v ∣ (v + 1 + 1) - v := Nat.dvd_sub' h2 dvd_rfl
      have h6 : v + 1 + 1 - v = 2 := by omega
      rwa [h6] at h5
    have hv2 : v ≤ 2 := Nat.le_of_dvd (by norm_num) this
    interval_cases v
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

/-! ## The prime case is square-root size

At a prime, substituting `u = ps` and `v+1 = st` in the `M = p` term turns the condition
into the symmetric cubic `stm - t - m = p`. Fixing `(t,m)` determines `s`, so the count is
bounded by the number of pairs with `tm ∣ p+t+m`. Two elementary facts then bound that:
the smaller variable is `O(√p)` and the larger runs over divisors of `p+t`. Since
`T(p,5) = 5 + 5C(p)` with `C(p)` that count, this gives `T(p,5) = O_ε(p^{1/2+ε})`, against
`O_ε(p^{1+ε})` from Corollary `cor:t5upper`.
-/

/-- **The cubic hyperbola bound.** From `tm ∣ p+t+m` with everything positive. -/
theorem t5_cubic_hyperbola {p t m : ℤ} (hp : 0 < p) (ht : 0 < t) (hm : 0 < m)
    (h : t * m ∣ p + t + m) : (t - 1) * (m - 1) ≤ p + 1 := by
  have hpos : 0 < p + t + m := by linarith
  have hle : t * m ≤ p + t + m := Int.le_of_dvd hpos h
  nlinarith [hle]

/-- **The smaller variable is `O(√p)`.** With `t ≤ m` the hyperbola bound gives
`(t-1)^2 ≤ p+1`, so `t ≤ 1 + √(p+1)`. This is what turns the linear bound of
`t5_min_bound` into a square-root bound at a prime. -/
theorem t5_cubic_min {p t m : ℤ} (hp : 0 < p) (ht : 0 < t) (hm : 0 < m) (htm : t ≤ m)
    (h : t * m ∣ p + t + m) : (t - 1) ^ 2 ≤ p + 1 := by
  have hh := t5_cubic_hyperbola hp ht hm h
  nlinarith [hh, htm, ht]

/-- **The larger variable divides `p+t`.** So for each `t` it runs over a divisor set, and
the pair count is at most `2 ∑_{t ≤ 1+√(p+1)} d(p+t)`. -/
theorem t5_cubic_dvd {p t m : ℤ} (h : t * m ∣ p + t + m) : m ∣ p + t := by
  have h1 : m ∣ (p + t) + m := dvd_trans (Dvd.intro_left t rfl) h
  exact (dvd_add_left (dvd_refl m)).mp h1

/-! ## The counting bound at a prime, as a cardinality

`t5_cubic_hyperbola` and `t5_cubic_dvd` are the two ingredients; this assembles them into
the inequality the proof of `thm:primesqrt` actually uses. Only the final step
`d(n) = O_ε(n^ε)` is left outside Lean, and that is a statement about `Nat.divisors` alone,
with no frieze content.
-/

/-- The hyperbola bound over `ℕ`, stated without subtraction: `(t-1)^2 ≤ p+1` is
`t^2 ≤ p + 2t`. -/
theorem t5_cubic_hyperbola_nat {p t m : ℕ} (ht : 0 < t) (hm : 0 < m) (htm : t ≤ m)
    (h : t * m ∣ p + t + m) : t * t ≤ p + 2 * t := by
  have hpos : 0 < p + t + m := by omega
  have hle : t * m ≤ p + t + m := Nat.le_of_dvd hpos h
  nlinarith [hle, htm, ht, hm]

/-- The larger variable divides `p + t`, over `ℕ`. -/
theorem t5_cubic_dvd_nat {p t m : ℕ} (h : t * m ∣ p + t + m) : m ∣ p + t := by
  have h1 : m ∣ (p + t) + m := dvd_trans (Dvd.intro_left t rfl) h
  exact (Nat.dvd_add_iff_left (dvd_refl m)).mpr h1

/-- **The counting bound.** Every pair `(t,m)` with `t ≤ m` and `tm ∣ p+t+m` has `t ≤ K`
and `m` a divisor of `p+t`, so the pairs are at most `∑_{t ≤ K} d(p+t)`. With
`K = 1 + ⌊√p⌋` supplied by `t5_cubic_hyperbola_nat`, and `T(p,5) = 5 + 5C(p)`, this is the
inequality behind `thm:primesqrt`. -/
theorem t5_prime_count_bound (p K B : ℕ) (hp : 0 < p)
    (hK : ∀ t m : ℕ, 0 < t → 0 < m → t ≤ m → t * m ∣ p + t + m → t ≤ K) :
    (((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter
        (fun x : ℕ × ℕ => x.1 ≤ x.2 ∧ x.1 * x.2 ∣ p + x.1 + x.2)).card
      ≤ ∑ t ∈ Finset.Icc 1 K, (p + t).divisors.card := by
  classical
  have hsub :
      (((Finset.Icc 1 B) ×ˢ (Finset.Icc 1 B)).filter
        (fun x : ℕ × ℕ => x.1 ≤ x.2 ∧ x.1 * x.2 ∣ p + x.1 + x.2))
      ⊆ (Finset.Icc 1 K).biUnion
          (fun t => ({t} : Finset ℕ) ×ˢ (p + t).divisors) := by
    rintro ⟨t, m⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨ht1, -⟩, ⟨hm1, -⟩⟩, htm, hdvd⟩ := hx
    have ht : 0 < t := ht1
    have hm : 0 < m := hm1
    refine Finset.mem_biUnion.mpr ⟨t, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨ht, hK t m ht hm htm hdvd⟩
    · refine Finset.mem_product.mpr ⟨Finset.mem_singleton_self t, ?_⟩
      exact Nat.mem_divisors.mpr ⟨t5_cubic_dvd_nat hdvd, by omega⟩
  have hsum : ∑ t ∈ Finset.Icc 1 K, (({t} : Finset ℕ) ×ˢ (p + t).divisors).card
      = ∑ t ∈ Finset.Icc 1 K, (p + t).divisors.card :=
    Finset.sum_congr rfl (fun t _ => by simp)
  calc _ ≤ ((Finset.Icc 1 K).biUnion
              (fun t => ({t} : Finset ℕ) ×ˢ (p + t).divisors)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ t ∈ Finset.Icc 1 K, (({t} : Finset ℕ) ×ˢ (p + t).divisors).card :=
        Finset.card_biUnion_le
    _ = ∑ t ∈ Finset.Icc 1 K, (p + t).divisors.card := hsum

/-! ## Where the remaining difficulty is

Counting by `(g,M)` rather than `(u,v)` turns the width-5 count into a count of divisors
in residue classes. With `x = gu` and `y = gv` the equation `guv = N(u+v)+M` becomes
`(x-N)(y-N) = N^2 + gM`, and `g ∣ x` says that `D := x - N` lies in the class `-N` modulo
`g`. So each solution is a divisor `D` of `N^2 + gM` in a prescribed class mod `g`, and
`t5_g_bound` makes the range of `g` finite. That is the exact shape of the obstruction to
Conjecture `conj:order`; no frieze structure is left in it.
-/

/-- **The Markov parameter is bounded.** From `guv = N(u+v)+M` with `u,v ≥ 1` and
`M ≤ N^2`, one gets `g ≤ N^2 + 2N`. The bound is attained: the largest `g` occurring is
exactly `N^2 + 2N` for every `N ≥ 6` tested. -/
theorem t5_g_bound {N g u v M : ℤ} (hu : 0 < u) (hv : 0 < v) (hN : 0 < N)
    (hM : M ≤ N ^ 2) (h : g * u * v = N * (u + v) + M) :
    g ≤ N ^ 2 + 2 * N := by
  have huv : 0 < u * v := mul_pos hu hv
  have h1 : u ≤ u * v := le_mul_of_one_le_right hu.le hv
  have h2 : v ≤ u * v := le_mul_of_one_le_left hv.le hu
  have h3 : M ≤ N ^ 2 * (u * v) := by nlinarith [huv, hM]
  have h4 : g * (u * v) ≤ (N ^ 2 + 2 * N) * (u * v) := by nlinarith [h, h1, h2, h3, hN]
  exact le_of_mul_le_mul_right (by linarith [h4]) huv

/-- **The residue-class shape.** If `g ∣ x` then `x - N ≡ -N` modulo `g`. Together with
`(x-N)(y-N) = N^2 + gM`, this places each solution as a divisor of `N^2+gM` in a fixed
class mod `g`. -/
theorem t5_residue_shape {N g x : ℤ} (h : g ∣ x) : g ∣ (x - N) + N := by
  simpa using h

/-- The product identity behind that reformulation: with `x = gu` and `y = gv`,
`(x-N)(y-N) = N^2 + gM` whenever `guv = N(u+v)+M`. -/
theorem t5_shifted_product {N g u v M : ℤ} (h : g * u * v = N * (u + v) + M) :
    (g * u - N) * (g * v - N) = N ^ 2 + g * M := by
  linear_combination g * h

end VicoEnum
