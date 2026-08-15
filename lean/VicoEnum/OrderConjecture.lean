/-
  VicoEnum/OrderConjecture.lean

  Conjecture `conj:order`, stated in Lean, and the cases of it that are theorems.

  `conj:order` asserts `T(N,5) = N^{o(1)}`. It is open, so it cannot be VERIFIED: a Lean
  file containing an unproved placeholder is not a formalization. What can be done, and is done here, is to state
  it exactly (Rule 5: formalize the statement first, which pins the semantics and catches
  quantifier errors), and then prove what is provable around it.

  The statement is written in the same shape as the divisor bound of `DivisorBound.lean`,
  avoiding real exponents:

      OrderConj  :  ∀ k > 0, ∃ C, ∀ N > 0,  T(N,5)^k ≤ C · N.

  Since `T(N,5) ≤ (C·N)^{1/k}` for every `k`, this is exactly `T(N,5) = O_ε(N^ε)`.

  Three things are then proved unconditionally.

  * `orderConj_width4`: the analogue at width 4 is TRUE. There `T(N,4) = d(2N^2)`, and the
    divisor bound gives `T(N,4)^k ≤ 2 C_k N^2`, so `T(N,4) = N^{o(1)}`.
  * `divisorCount_orderShape`: the divisor function satisfies the same shape, so the form
    of the statement is one that can hold.
  * `orderConj_imp_linear`: the conjecture implies `T(N,5) = O(N)`, which is the weakest
    open case and the one the data supports most directly.
-/
import VicoEnum.DivisorBound
import VicoEnum.Count
import VicoEnum.Width4
import VicoEnum.Width4Count

namespace VicoEnum

/-- **Conjecture `conj:order`**, stated. For every `k` there is a constant `C` with
`T(N,5)^k ≤ C·N` for all `N ≥ 1`; equivalently `T(N,5) = O_ε(N^ε)`.

This is a `Prop`, not a theorem. It is open. -/
def OrderConj : Prop :=
  ∀ k : ℕ, 0 < k → ∃ C : ℕ, ∀ N : ℕ, 0 < N → (T5 N) ^ k ≤ C * N

/-- The shape of `OrderConj` is one that can hold: the divisor function satisfies it, by
`card_divisors_pow_le`. -/
theorem divisorCount_orderShape :
    ∀ k : ℕ, 0 < k → ∃ C : ℕ, ∀ n : ℕ, 0 < n → (n.divisors.card) ^ k ≤ C * n := by
  intro k hk
  exact ⟨divBoundConst k, fun n hn => card_divisors_pow_le k hk hn.ne'⟩

/-- The divisor bound applied to the set of admissible FIRST ENTRIES. This is not yet a
statement about friezes; `orderConj_width4_friezes` below is. -/
theorem orderConj_width4 (k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, ∀ N : ℕ, 0 < N →
      (Set.ncard {a : ℚ | 0 < a ∧ InLattice N a ∧ InLattice N (2 / a)}) ^ k
        ≤ C * N ^ 2 := by
  refine ⟨2 * divBoundConst k, fun N hN => ?_⟩
  have hne : 2 * N ^ 2 ≠ 0 := by positivity
  calc (Set.ncard {a : ℚ | 0 < a ∧ InLattice N a ∧ InLattice N (2 / a)}) ^ k
      = ((2 * N ^ 2).divisors.card) ^ k := by rw [width4_card N hN]
    _ ≤ divBoundConst k * (2 * N ^ 2) := card_divisors_pow_le k hk hne
    _ = 2 * divBoundConst k * N ^ 2 := by ring

/-- The conjecture implies `T(N,5) = O(N)`, the weakest form still open. Taking `k = 1`. -/
theorem orderConj_imp_linear (h : OrderConj) :
    ∃ C : ℕ, ∀ N : ℕ, 0 < N → T5 N ≤ C * N := by
  obtain ⟨C, hC⟩ := h 1 one_pos
  exact ⟨C, fun N hN => by simpa using hC N hN⟩

/-- The conjecture is monotone in `k` in the expected way: a witness for `k` gives one for
every smaller positive `k'`, so it suffices to prove it along any unbounded set of `k`. -/
theorem orderConj_of_cofinal
    (h : ∀ k : ℕ, 0 < k → ∃ k' : ℕ, k ≤ k' ∧ ∃ C : ℕ, ∀ N : ℕ, 0 < N → (T5 N) ^ k' ≤ C * N) :
    OrderConj := by
  intro k hk
  obtain ⟨k', hkk', C, hC⟩ := h k hk
  refine ⟨C, fun N hN => ?_⟩
  by_cases hT : T5 N = 0
  · rw [hT, zero_pow hk.ne']
    exact Nat.zero_le _
  · have h1 : 1 ≤ T5 N := Nat.one_le_iff_ne_zero.mpr hT
    calc (T5 N) ^ k ≤ (T5 N) ^ k' := Nat.pow_le_pow_right h1 hkk'
      _ ≤ C * N := hC N hN

/-! ## The minimal open case

At a prime, `d(p^2) = 3`, so `OrderConj` asserts `T(p,5) = O(\log^2 p)`, far stronger than
the `O(\sqrt p \log p)` of Theorem `thm:primesqrt`. That case is itself open, and it has a
clean shape: `cubic_pair_iff` turns the condition `tm ∣ p+t+m` into "`m` divides `p+t`, and
`t` divides `w+1` where `p+t = mw`". So the count is

    ∑_{t ≤ 1+⌊√p⌋}  #{ divisors w of p+t with w ≡ -1 (mod t) },

and `OrderConj` at a prime is the assertion that this is `O(\log^2 p)`. Nothing about
friezes remains in it. -/

/-- **The minimal open case, reduced.** `tm ∣ p+t+m` holds exactly when `m ∣ p+t` and,
writing `p+t = mw`, also `t ∣ w+1`. -/
theorem cubic_pair_iff {p t m : ℕ} (hm : 0 < m) :
    t * m ∣ p + t + m ↔ ∃ w : ℕ, p + t = m * w ∧ t ∣ w + 1 := by
  constructor
  · intro h
    have hmd : m ∣ p + t + m := dvd_trans (Dvd.intro_left t rfl) h
    have hmpt : m ∣ p + t := (Nat.dvd_add_iff_left (dvd_refl m)).mpr hmd
    obtain ⟨w, hw⟩ := hmpt
    refine ⟨w, hw, ?_⟩
    have hrw : p + t + m = m * (w + 1) := by rw [hw]; ring
    rw [hrw] at h
    have h2 : m * t ∣ m * (w + 1) := by rwa [Nat.mul_comm t m] at h
    exact (mul_dvd_mul_iff_left hm.ne').mp h2
  · rintro ⟨w, hw, hz⟩
    obtain ⟨z, hzz⟩ := hz
    refine ⟨z, ?_⟩
    calc p + t + m = m * (w + 1) := by rw [hw]; ring
      _ = m * (t * z) := by rw [hzz]
      _ = t * m * z := by ring

/-! ## A lower bound, and what it costs the conjecture

Taking `u = 1` in the cubic `suv = p + u + v` leaves `sv = p + 1 + v`, which has a
solution for every divisor `v` of `p+1`, namely `s = (p+1)/v + 1`. Distinct divisors give
distinct solutions, so

    C(p) ≥ d(p+1),      hence      T(p,5) = 5 + 5C(p) ≥ 5 d(p+1).

This is the first lower bound in the project, and it constrains the conjecture. At a prime
`d(p^2) = 3`, so the equivalence form `T(N,5) ≍ d(N^2)\log^2 N` would force
`d(p+1) = O(\log^2 p)`. The divisor function has maximal order exceeding every fixed power
of the logarithm, so that form cannot hold for all primes unless `d(p+1)` is unusually
tame along shifted primes. The `N^{o(1)}` form, which is what `OrderConj` states, is
untouched, since `d(p+1) = p^{o(1)}`. -/

/-- Every divisor of `p+1` solves the cubic with `u = 1`. -/
theorem cubic_sol_of_divisor {p v : ℕ} (hv : v ∈ (p + 1).divisors) :
    ((p + 1) / v + 1) * v = p + 1 + v := by
  obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hv
  have hv0 : 0 < v := Nat.pos_of_dvd_of_pos hdvd (by omega)
  rw [add_mul, one_mul, Nat.div_mul_cancel hdvd]

/-- **The lower bound.** Any set of solutions containing the `u = 1` family has at least
`d(p+1)` elements, because `v ↦ ((p+1)/v + 1, v)` is injective. -/
theorem cubic_lower_card (p : ℕ) (S : Finset (ℕ × ℕ))
    (hS : ∀ v ∈ (p + 1).divisors, ((p + 1) / v + 1, v) ∈ S) :
    (p + 1).divisors.card ≤ S.card := by
  refine Finset.card_le_card_of_injOn (fun v => ((p + 1) / v + 1, v)) hS ?_
  intro a _ b _ h
  simpa using congrArg Prod.snd h

/-! ## Narrowing the gap at primes

The upper bound of Theorem `thm:primesqrt` went through the divisor bound and produced
`O_ε(p^{1/2+ε})`. It can be sharpened to `O(√p log p)`, with no `ε` and no appeal to
`card_divisors_pow_le`, by counting in residue classes directly.

Divisors `w` of `n = p+t` with `t ∣ w+1` pair with `n/w`, which lies in the fixed class
`-p` mod `t` since `n ≡ p`. The smaller member of each pair is at most `√n`, and the
integers up to `B` in a fixed class mod `t` number at most `B/t + 1`
(`card_class_le`). So

    #{w ∣ p+t : t ∣ w+1}  ≤  2(√(p+t)/t + 1),

and summing over `t ≤ 1+⌊√p⌋`, with the factor `2` for the two orders, gives
`C(p) = O(√p log p)`. Against the lower bound `C(p) ≥ d(p+1)` of `cubic_lower_card`, the
gap at primes is now

    d(p+1)  ≤  C(p)  =  O(√p log p),

with `d(p+1)` exceeding every fixed power of `log p` infinitely often, so neither end is
known to be the truth. -/

/-- **Integers in a residue class.** At most `B/t + 1` of the integers in `[1,B]` are
congruent to `c` modulo `t`. This is the counting step behind the sharpened bound. -/
theorem card_class_le (B t c : ℕ) (ht : 0 < t) :
    ((Finset.Icc 1 B).filter (fun w => w % t = c)).card ≤ B / t + 1 := by
  classical
  have h : ((Finset.Icc 1 B).filter (fun w => w % t = c)).card
      ≤ (Finset.range (B / t + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun w => w / t) (fun w hw => ?_) ?_
    · simp only [Finset.mem_filter, Finset.mem_Icc] at hw
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hw.1.2))
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at ha hb
      have ha2 := Nat.div_add_mod a t
      have hb2 := Nat.div_add_mod b t
      have hab' : a / t = b / t := hab
      rw [ha.2] at ha2
      rw [hb.2] at hb2
      rw [hab'] at ha2
      omega
  simpa using h

/-! ## The exponent one third

Conrey and Shah bound the number of representations `n = xyz+x+y+z` by
`n^{1/3}\log n(\log\log n)^4`, using that full symmetry forces the smallest variable below
`n^{1/3}` and then a divisor-sum estimate over polynomial values. Our prime equation
`suv = p+u+v` is symmetric only in `u` and `v`, but the cube-root bound survives anyway.

If `min(s,u,v)^3 > 2p` then `suv > 2p`, so `p < u+v`, so `suv = p+u+v < 2(u+v) ≤ 4\max(u,v)`,
and cancelling the maximum leaves a product of two of the variables below `4`, while each
is at least `3`. That is `cube_root_min`.

With it, splitting on which variable is smallest and using
`(su-1)(sv-1) = sp+1` and `v(su-1) = p+u`, every solution is a divisor of `tp+1` or of
`p+t` for some `t ≤ (2p)^{1/3}`, so

    C(p) ≤ ∑_{t ≤ (2p)^{1/3}} ( τ(tp+1) + 2τ(p+t) ).

A divisor-sum bound of Shiu type then gives `C(p) = O(p^{1/3+o(1)})`, improving the
`O(√p log p)` above and matching the state of the art for this family of equations. -/

/-- **Lemma `lem:cuberoot`, the smallest variable is below the cube root.** For `p ≥ 4`,
every positive solution
of `suv = p+u+v` has `min(s,u,v)^3 ≤ 2p`. Elementary, and it is what lets the
Conrey--Shah argument run here despite the equation being symmetric only in `u` and `v`. -/
theorem cube_root_min {p s u v : ℕ} (hp : 4 ≤ p) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v)
    (h : s * u * v = p + u + v) :
    (min s (min u v)) ^ 3 ≤ 2 * p := by
  by_contra hcon
  push_neg at hcon
  set m := min s (min u v) with hm
  have hms : m ≤ s := min_le_left _ _
  have hmu : m ≤ u := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmv : m ≤ v := le_trans (min_le_right _ _) (min_le_right _ _)
  -- m ≥ 3, since m^3 > 2p ≥ 8
  have hm3 : 3 ≤ m := by
    by_contra hlt
    push_neg at hlt
    have hle8 : m ^ 3 ≤ 8 := by interval_cases m <;> norm_num
    omega
  -- m^3 ≤ s u v
  have hcube : m ^ 3 ≤ s * u * v := by
    calc m ^ 3 = m * m * m := by ring
      _ ≤ s * u * v := Nat.mul_le_mul (Nat.mul_le_mul hms hmu) hmv
  have h2p : 2 * p < s * u * v := lt_of_lt_of_le hcon hcube
  have huv : p < u + v := by omega
  rcases le_total u v with hle | hle
  · -- v is the maximum: s u v < 4 v forces s u < 4
    have hlt : s * u * v < 4 * v := by nlinarith [h, huv, hle]
    have : s * u < 4 := by
      by_contra hge
      push_neg at hge
      nlinarith [hlt, hge, hv]
    nlinarith [this, hm3, hms, hmu]
  · -- u is the maximum
    have hlt : s * u * v < 4 * u := by nlinarith [h, huv, hle]
    have : s * v < 4 := by
      by_contra hge
      push_neg at hge
      nlinarith [hlt, hge, hu]
    nlinarith [this, hm3, hms, hmv]

/-! ## The cube-root branches, and why the two-branch split cannot work

Theorem `thm:primecube` splits a solution of `suv = p+u+v` according to which variable is
least. The two factorisations that drive it are `cube_factor` and `cube_branch_u`: in the
first branch `su-1` divides `sp+1`, in the second it divides `p+u`. Each branch therefore
contributes at most a divisor count, and `cube_root_min` bounds the range of the least
variable by `(2p)^{1/3}`.

The natural attempt to do better splits instead by the least `k` with `kt-1 ∣ p+t`. Terms
with `k ≤ K` are governed by divisors of `kp+1` and cost `O(K log p)`; terms with `k > K`
force a small complementary divisor `v < p/K` with `t ∣ p+v` and cost `O((p/K) log p)`.
`split_cost_ge` shows that no choice of `K` brings the sum below `2√p`, which is worse than
the trivial bound `p^{1/3}`. So the split cannot help, and that is a theorem about the
method rather than a report of failure. -/

/-- **The branch factorisation.** From `suv = p+u+v`, multiplying by `s` gives
`(su-1)(sv-1) = sp+1`. -/
theorem cube_factor {p s u v : ℤ} (h : s * u * v = p + u + v) :
    (s * u - 1) * (s * v - 1) = s * p + 1 := by linear_combination s * h

/-- First branch: `su-1` divides `sp+1`, so the solution is pinned by a divisor of
`sp+1`. -/
theorem cube_branch_s {p s u v : ℤ} (h : s * u * v = p + u + v) :
    (s * u - 1) ∣ (s * p + 1) := ⟨s * v - 1, (cube_factor h).symm⟩

/-- Second branch: `su-1` divides `p+u`, so the solution is pinned by a divisor of
`p+u`. -/
theorem cube_branch_u {p s u v : ℤ} (h : s * u * v = p + u + v) :
    (s * u - 1) ∣ (p + u) := ⟨v, by linear_combination -h⟩

/-- **The two-branch split cannot beat the trivial bound.** If the two branches cost `K`
and `q` with `p ≤ Kq`, their sum is at least `2√p`, since `4p ≤ 4Kq ≤ (K+q)^2`. With
`K = √p` this is exactly the balance point, and `√p` exceeds the trivial bound `p^{1/3}`.
-/
theorem split_cost_ge {p K q : ℕ} (h : p ≤ K * q) : 4 * p ≤ (K + q) ^ 2 := by
  have hZ : (4 : ℤ) * ((K : ℤ) * q) ≤ ((K : ℤ) + q) ^ 2 := by
    nlinarith [sq_nonneg ((K : ℤ) - q)]
  have h1 : (4 : ℤ) * (p : ℤ) ≤ 4 * ((K : ℤ) * q) := by exact_mod_cast Nat.mul_le_mul_left 4 h
  have h2 : (4 : ℤ) * (p : ℤ) ≤ ((K : ℤ) + q) ^ 2 := le_trans h1 hZ
  exact_mod_cast h2

/-- **A solution is pinned by two coordinates.** If `su > 1`, a solution of
`suv = p+u+v` is determined by `s` and `su`. Together with `cube_branch_s` and
`cube_branch_u`, which put `su-1` among the divisors of `sp+1` respectively `p+u`, this is
what makes each branch of Theorem `thm:primecube` a divisor count: the least variable
ranges over `t ≤ (2p)^{1/3}` by `cube_root_min`, and the rest of the solution is one
divisor. -/
theorem cube_det {p s u v v' : ℕ} (hsu : 1 < s * u)
    (h : s * u * v = p + u + v) (h' : s * u * v' = p + u + v') : v = v' := by
  rcases lt_trichotomy v v' with hlt | heq | hgt
  · exfalso; nlinarith [h, h', hsu]
  · exact heq
  · exfalso; nlinarith [h, h', hsu]

/-- The same statement with the first coordinate recovered: `s` and `s*u` determine `u`
when `s > 0`. -/
theorem cube_det_fst {s u u' : ℕ} (hs : 0 < s) (hd : s * u = s * u') : u = u' :=
  Nat.eq_of_mul_eq_mul_left hs hd

/-! ## The `s = 2` family, and why no `d(p+1) + polylog` formula can hold

Splitting `C(p) = ∑_a R_a(p)` by the value of `s = a`, the term `a = 1` is `d(p+1)`
(`cubic_lower_card`). The term `a = 2` is *also* a full divisor count, and for a reason
that costs nothing: at `s = 2` the cubic `2uv = p + u + v` factors as

    (2u - 1)(2v - 1) = 2p + 1,

and `2p + 1` is odd, so **every** divisor of it is odd and therefore of the form `2u - 1`.
Unlike `a ≥ 3`, where only divisors in one residue class mod `a` count, the `a = 2` family
loses nothing to a congruence. Hence `R₂(p) = d(2p+1)` exactly.

The consequence is negative and it is the point of this section. Since the two families
have different `s`, they are disjoint, so

    C(p) ≥ d(p+1) + d(2p+1),

and `d(2p+1)` is not controlled by `d(p+1)` and powers of `log p`: choosing `p` in the
arithmetic progression `2p ≡ -1 (mod q)` for `q` a primorial forces `q ∣ 2p+1`, while
`p+1` is left free. So no asymptotic formula for `C(p)` built from `d(p+1)` and `log p`
alone can be correct. This refutes the shape of Conjecture `conj:prime`, and it refutes it
by the same mechanism that refuted `T(N,5) ≍ d(N²)log²N`: a divisor count at a *shifted*
argument that the formula does not see.
-/

/-- **The `s = 2` cubic is a factorisation.** Every odd factorisation `2p+1 = (2u+1)(2v+1)`
gives a solution of `2UV = p + U + V` with `U = u+1`, `V = v+1`. Division free. -/
theorem cubic_sol_two {p u v : ℕ} (h : (2 * u + 1) * (2 * v + 1) = 2 * p + 1) :
    2 * (u + 1) * (v + 1) = p + (u + 1) + (v + 1) := by
  have e1 : (2 * u + 1) * (2 * v + 1) = 4 * (u * v) + 2 * u + 2 * v + 1 := by ring
  have e2 : 2 * (u + 1) * (v + 1) = 2 * (u * v) + 2 * u + 2 * v + 2 := by ring
  omega

/-- Every divisor of `2p+1` is odd. -/
theorem odd_of_dvd_two_mul_succ {p D : ℕ} (hD : D ∣ 2 * p + 1) : D % 2 = 1 := by
  rcases Nat.even_or_odd D with he | ho
  · exact absurd (dvd_trans he.two_dvd hD) (by omega)
  · exact Nat.odd_iff.mp ho

/-- **`R₂(p) ≥ d(2p+1)`.** The map `D ↦ (D+1)/2` is injective on the divisors of `2p+1`,
because they are all odd. -/
theorem cubic_lower_two (p : ℕ) (S : Finset ℕ)
    (hS : ∀ D ∈ (2 * p + 1).divisors, (D + 1) / 2 ∈ S) :
    (2 * p + 1).divisors.card ≤ S.card := by
  refine Finset.card_le_card_of_injOn (fun D => (D + 1) / 2) hS ?_
  intro a ha b hb h
  have ha2 := odd_of_dvd_two_mul_succ (Nat.mem_divisors.mp ha).1
  have hb2 := odd_of_dvd_two_mul_succ (Nat.mem_divisors.mp hb).1
  simp only at h
  omega

/-- **`C(p) ≥ d(p+1) + d(2p+1)`, the counting half.** The `a = 1` and `a = 2` families are
disjoint, being distinguished by their first coordinate. Both hypotheses record the pair
`(a, u)`; `cubic_family_one` and `cubic_family_two` below supply the solutions that make them
instantiable. The resulting bound on `C(p)` is stronger than `cubic_lower_card`'s, but the
two lemmas are not comparable: `cubic_lower_card` records the `u = 1` family and this one the
`a = 1` family, two disjoint families that happen to share the cardinality `d(p+1)`. The bound
is what no formula in `d(p+1)` and `log p` alone can accommodate. -/
theorem cubic_lower_two_families (p : ℕ) (S : Finset (ℕ × ℕ))
    (h1 : ∀ D ∈ (p + 1).divisors, (1, D + 1) ∈ S)
    (h2 : ∀ D ∈ (2 * p + 1).divisors, (2, (D + 1) / 2) ∈ S) :
    (p + 1).divisors.card + (2 * p + 1).divisors.card ≤ S.card := by
  classical
  have hsub : (S.filter (fun x => x.1 = 1)) ∪ (S.filter (fun x => x.1 = 2)) ⊆ S :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hdisj : Disjoint (S.filter (fun x => x.1 = 1)) (S.filter (fun x => x.1 = 2)) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    exact absurd (hx.2.symm.trans hx'.2) (by norm_num)
  have c1 : (p + 1).divisors.card ≤ (S.filter (fun x => x.1 = 1)).card := by
    refine Finset.card_le_card_of_injOn (fun D => ((1 : ℕ), D + 1)) ?_ ?_
    · intro D hD; exact Finset.mem_filter.mpr ⟨h1 D hD, rfl⟩
    · intro a _ b _ h; have := congrArg Prod.snd h; simp only at this; omega
  have c2 : (2 * p + 1).divisors.card ≤ (S.filter (fun x => x.1 = 2)).card := by
    refine cubic_lower_two p ((S.filter (fun x => x.1 = 2)).image Prod.snd) ?_ |>.trans ?_
    · intro D hD
      exact Finset.mem_image.mpr ⟨(2, (D + 1) / 2), Finset.mem_filter.mpr ⟨h2 D hD, rfl⟩, rfl⟩
    · exact Finset.card_image_le
  calc (p + 1).divisors.card + (2 * p + 1).divisors.card
      ≤ (S.filter (fun x => x.1 = 1)).card + (S.filter (fun x => x.1 = 2)).card :=
        Nat.add_le_add c1 c2
    _ = ((S.filter (fun x => x.1 = 1)) ∪ (S.filter (fun x => x.1 = 2))).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ S.card := Finset.card_le_card hsub

/-- **The order conjecture is a theorem at width 4**, for the friezes themselves. The set
bounded in `orderConj_width4` is the set of admissible first entries; `width4_card` and
`paper_count4` identify its cardinality with the count over Definition `def:frieze`, so the
bound transfers to `T(N,4)`. This is the first case of `conj:order` and it is unconditional. -/
theorem orderConj_width4_friezes (k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, ∀ N : ℕ, 0 < N →
      ({F : Fin 5 → ℤ → ℚ | PaperFrieze4 N F}.ncard) ^ k ≤ C * N ^ 2 := by
  obtain ⟨C, hC⟩ := orderConj_width4 k hk
  refine ⟨C, fun N hN => ?_⟩
  have h : {F : Fin 5 → ℤ → ℚ | PaperFrieze4 N F}.ncard
      = Set.ncard {a : ℚ | 0 < a ∧ InLattice N a ∧ InLattice N (2 / a)} := by
    rw [paper_count4 hN, width4_card N hN]
  rw [h]
  exact hC N hN

/-! ## The two families are genuine solutions

Without these the counting lemma above is vacuous: it bounds the size of any `S` containing
the two families, but nothing says a set of solutions contains them. Writing `DE = p+1` for
the first family and `DE = 2p+1` for the second, both identities are the same expansion
`(D+1)(E+1) = DE + D + E + 1`. -/

/-- **The `a = 1` family.** For `D ∣ p+1` the triple `(1, D+1, (p+1)/D + 1)` solves
`auv = p+u+v`. -/
theorem cubic_family_one {p D : ℕ} (hD : D ∣ p + 1) (hD0 : 0 < D) :
    1 * (D + 1) * ((p + 1) / D + 1) = p + (D + 1) + ((p + 1) / D + 1) := by
  obtain ⟨E, hE⟩ := hD
  have hEq : (p + 1) / D = E := by rw [hE]; exact Nat.mul_div_cancel_left E hD0
  rw [hEq]
  have : D * E = p + 1 := hE.symm
  nlinarith [this]

/-- **The `a = 2` family.** For `D ∣ 2p+1` the triple `(2, (D+1)/2, ((2p+1)/D + 1)/2)` solves
`auv = p+u+v`. Both `D` and `(2p+1)/D` are odd, so the halvings are exact. -/
theorem cubic_family_two {p D : ℕ} (hD : D ∣ 2 * p + 1) (hD0 : 0 < D) :
    2 * ((D + 1) / 2) * (((2 * p + 1) / D + 1) / 2)
      = p + (D + 1) / 2 + ((2 * p + 1) / D + 1) / 2 := by
  obtain ⟨E, hE⟩ := hD
  have hEq : (2 * p + 1) / D = E := by rw [hE]; exact Nat.mul_div_cancel_left E hD0
  rw [hEq]
  have hDE : D * E = 2 * p + 1 := hE.symm
  have hDodd : D % 2 = 1 := by
    rcases Nat.even_or_odd D with h | h
    · exfalso
      have h2 : (2 : ℕ) ∣ D * E := Dvd.dvd.mul_right h.two_dvd E
      rw [hDE] at h2; omega
    · exact Nat.odd_iff.mp h
  have hEodd : E % 2 = 1 := by
    rcases Nat.even_or_odd E with h | h
    · exfalso
      have h2 : (2 : ℕ) ∣ D * E := Dvd.dvd.mul_left h.two_dvd D
      rw [hDE] at h2; omega
    · exact Nat.odd_iff.mp h
  obtain ⟨d, hd⟩ : ∃ d, D = 2 * d + 1 := ⟨D / 2, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, E = 2 * e + 1 := ⟨E / 2, by omega⟩
  subst hd; subst he
  have h1 : (2 * d + 1 + 1) / 2 = d + 1 := by omega
  have h2 : (2 * e + 1 + 1) / 2 = e + 1 := by omega
  rw [h1, h2]
  nlinarith [hDE]

/-! ## `prop:twofam` assembled

The counting half bounds any set containing the two families. To make it a bound on `C(p)`
the families must sit inside an actual solution set, so they are placed in the box `[1,p+2]³`,
which is generous enough for both. -/

/-- **The box is complete.** Every positive solution of `auv = p+u+v` has all three
coordinates at most `p+2`, so `cubicTriples` below is the full solution set and not a
truncation. If `u > p+2` then `v(au-1) = p+u` with `au-1 ≥ u-1` forces `v = 1`, whence
`u(a-1) = p+1` and `u ≤ p+1`; the bound on `a` splits on whether `uv` is `1`. -/
theorem cubic_box_complete {p a u v : ℕ} (ha : 0 < a) (hu : 0 < u) (hv : 0 < v)
    (h : a * u * v = p + u + v) : a ≤ p + 2 ∧ u ≤ p + 2 ∧ v ≤ p + 2 := by
  obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  have huv : u' * v' ≤ p + 1 := by nlinarith [h]
  -- the two outer bounds first; the bound on `a` uses them
  have hu2 : u' ≤ p + 1 := by
    rcases Nat.eq_zero_or_pos v' with rfl | hv1
    · have key : c * (u' + 1) = p + 1 := by nlinarith [h]
      have hc : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with rfl | h1
        · simp only [Nat.zero_mul] at key; omega
        · exact h1
      have := Nat.le_mul_of_pos_left (u' + 1) hc
      omega
    · nlinarith [huv, hv1]
  have hv2 : v' ≤ p + 1 := by
    rcases Nat.eq_zero_or_pos u' with rfl | hu1
    · have key : c * (v' + 1) = p + 1 := by nlinarith [h]
      have hc : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with rfl | h1
        · simp only [Nat.zero_mul] at key; omega
        · exact h1
      have := Nat.le_mul_of_pos_left (v' + 1) hc
      omega
    · nlinarith [huv, hu1]
  refine ⟨?_, by omega, by omega⟩
  rcases Nat.eq_zero_or_pos u' with rfl | hu1
  · rcases Nat.eq_zero_or_pos v' with rfl | hv1
    · simp at h; omega
    · nlinarith [h, hv1]
  · rcases Nat.eq_zero_or_pos v' with rfl | hv1
    · nlinarith [h, hu1]
    · have hfour : 4 ≤ (u' + 1) * (v' + 1) := by nlinarith [hu1, hv1]
      have h4 : (c + 1) * 4 ≤ (c + 1) * ((u' + 1) * (v' + 1)) :=
        Nat.mul_le_mul_left (c + 1) hfour
      have hexp : (c + 1) * ((u' + 1) * (v' + 1)) = p + (u' + 1) + (v' + 1) := by
        rw [← mul_assoc]; exact h
      omega

/-- The solutions of the cubic inside the box `[1, p+2]³`, which by `cubic_box_complete` is
every solution. -/
def cubicTriples (p : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 (p + 2)) ×ˢ (Finset.Icc 1 (p + 2)) ×ˢ (Finset.Icc 1 (p + 2))).filter
    (fun x => x.1 * x.2.1 * x.2.2 = p + x.2.1 + x.2.2)

/-- **Proposition `prop:twofam`.** `C(p) ≥ d(p+1) + d(2p+1)`, with `C(p)` realised as the
solution set of the cubic inside the box `[1,p+2]³`. `cubic_box_complete` below shows that
box contains every solution, so this is the full count. -/
theorem twofam_bound {p : ℕ} (hp : 0 < p) :
    (p + 1).divisors.card + (2 * p + 1).divisors.card ≤ (cubicTriples p).card := by
  classical
  set S := (cubicTriples p).image (fun x => (x.1, x.2.1)) with hS
  have hbound : S.card ≤ (cubicTriples p).card := Finset.card_image_le
  refine le_trans ?_ hbound
  refine cubic_lower_two_families p S ?_ ?_
  · intro D hD
    obtain ⟨hDdvd, -⟩ := Nat.mem_divisors.mp hD
    have hD0 : 0 < D := Nat.pos_of_dvd_of_pos hDdvd (by omega)
    have hDle : D ≤ p + 1 := Nat.le_of_dvd (by omega) hDdvd
    have hE : (p + 1) / D ≤ p + 1 := Nat.div_le_self _ _
    have hE0 : 0 < (p + 1) / D := Nat.div_pos (Nat.le_of_dvd (by omega) hDdvd) hD0
    refine Finset.mem_image.mpr ⟨(1, D + 1, (p + 1) / D + 1), ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, cubic_family_one hDdvd hD0⟩
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩
  · intro D hD
    obtain ⟨hDdvd, -⟩ := Nat.mem_divisors.mp hD
    have hD0 : 0 < D := Nat.pos_of_dvd_of_pos hDdvd (by omega)
    have hDle : D ≤ 2 * p + 1 := Nat.le_of_dvd (by omega) hDdvd
    have hE : (2 * p + 1) / D ≤ 2 * p + 1 := Nat.div_le_self _ _
    have hE0 : 0 < (2 * p + 1) / D := Nat.div_pos (Nat.le_of_dvd (by omega) hDdvd) hD0
    refine Finset.mem_image.mpr ⟨(2, (D + 1) / 2, ((2 * p + 1) / D + 1) / 2), ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, cubic_family_two hDdvd hD0⟩
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega⟩

end VicoEnum
