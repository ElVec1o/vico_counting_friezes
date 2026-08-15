/-
  VicoEnum/GeneralN.lean

  The structural half of Theorem `thm:orbit`, with primality removed.

  At a prime, `prop:intcount` says the number of integral quiddity entries is 3 or 5, and 5
  only for the Conway--Coxeter cycle. That proof is a p-adic valuation argument and does not
  survive composite `N`. Two of its consequences do, and are proved here for every `N`:

  `not_four_integral`: no orbit has exactly four integral entries. `eq:w5cyc` at `j = k+2`
  has both left factors divisible by `N` when `k` is the only non-integral index, so `N^2`
  divides `N(q_k + N)`, forcing `N | q_k`.

  `allint_card`: exactly five `W5` pairs are all-integral, and they are one rotation orbit,
  the Conway--Coxeter one scaled by `N`. Dividing `eq:w5cyc` by `N^2` turns it into the
  integral relation `a_j a_{j+1} = a_{j+3} + 1`, which `cc_classify` solves without
  reference to any prime.

  What does NOT generalise is the arithmetic half. At a prime the parameter `M` takes only
  the values `p` and `p^2`, every non-exceptional orbit splits `2:3`, and `A(p) = 5 + 2C(p)`
  collapses the count to a single cubic. For composite `N` the parameter ranges over the
  divisors of `N^2` and the orbit profiles are many, so no single cubic can carry the count:
  `T(N,5) = 5 + 5C(N)` with `C(N) = #{(a,u,v) : auv = N+u+v}` is FALSE, already at `N = 12`,
  where the left side is 310 and the right side is 40.
-/
import VicoEnum.RotCount

namespace VicoEnum
/-- **No orbit has exactly four integral entries**, for every `N`. -/
theorem not_four_integral {N : ℕ} (hN : 0 < N) {x : ℕ × ℕ} (hw : W5 N x.1 x.2) (k : ZMod 5)
    (h : ∀ j, j ≠ k → N ∣ qOn N x j) : N ∣ qOn N x k := by
  have e2 : ∀ j : ZMod 5, j + 2 ≠ j := by decide
  have e3 : ∀ j : ZMod 5, j + 2 + 1 ≠ j := by decide
  have hidx : ∀ j : ZMod 5, j + 2 + 3 = j := by decide
  have hrel := qOn_rel hN hw (k + 2)
  rw [hidx k] at hrel
  obtain ⟨b, hb⟩ := h (k + 2) (e2 k)
  obtain ⟨c, hc⟩ := h (k + 2 + 1) (e3 k)
  rw [hb, hc] at hrel
  have hmul : N * (N * (b * c)) = N * (qOn N x k + N) := by rw [← hrel]; ring
  have h2 : N * (b * c) = qOn N x k + N := Nat.eq_of_mul_eq_mul_left hN hmul
  exact (Nat.dvd_add_right ⟨1, by ring⟩).mp ⟨b * c, by omega⟩
/-- **The all-integral orbit is the Conway--Coxeter one, for every `N`.** No primality:
dividing `eq:w5cyc` by `N^2` gives the integral relation, which `cc_classify` solves. -/
theorem allint_of_orbit {N : ℕ} (hN : 0 < N) {x : ℕ × ℕ} (hw : W5 N x.1 x.2)
    (hall : ∀ j, N ∣ qOn N x j) : x ∈ orb (rotOn N) (3 * N, N) := by
  classical
  have key : ∀ j : ZMod 5, ∃ c : ℕ, 0 < c ∧ qOn N x j = N * c := by
    intro j
    obtain ⟨c, hc⟩ := hall j
    refine ⟨c, ?_, hc⟩
    rcases Nat.eq_zero_or_pos c with rfl | h
    · exact absurd (by simpa using hc ▸ qOn_pos hN hw j) (by simp)
    · exact h
  choose a hapos hqa using key
  have hrel : ∀ j : ZMod 5, a j * a (j + 1) = a (j + 3) + 1 := by
    intro j
    have h := qOn_rel hN hw j
    rw [hqa j, hqa (j + 1), hqa (j + 3)] at h
    have h2 : N * N * (a j * a (j + 1)) = N * N * (a (j + 3) + 1) := by
      rw [show N * N * (a j * a (j + 1)) = N * a j * (N * a (j + 1)) from by ring, h]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hN hN) h2
  have hcc : ∃ k : ZMod 5, a k = 3 ∧ a (k + 1) = 1 ∧ a (k + 2) = 2 ∧ a (k + 3) = 2 ∧
      a (k + 4) = 1 := cc_classify a hapos hrel
  obtain ⟨k, hk0, hk1, -, -, -⟩ := hcc
  have e1 : qOn N x k = 3 * N := by rw [hqa k, hk0]; ring
  have e2 : qOn N x (k + 1) = N := by rw [hqa (k + 1), hk1]; ring
  have hidx : orbIdx (rotOn N) x k = (3 * N, N) :=
    Prod.ext (by rw [show (orbIdx (rotOn N) x k).1 = qOn N x k from rfl, e1])
      (by rw [qOn_succ hN hw k, e2])
  exact orb_symm (rotOn_ord hN) (hidx ▸ orbIdx_mem_orb (rotOn N) x k)

/-- Every pair on the Conway--Coxeter orbit is all-integral. -/
theorem allint_of_mem_orb {N : ℕ} (hN : 0 < N) {x : ℕ × ℕ}
    (hx : x ∈ orb (rotOn N) (3 * N, N)) : ∀ j, N ∣ qOn N x j := by
  have hw : W5 N (3 * N, N).1 (3 * N, N).2 :=
    (Finset.mem_filter.mp (exc_mem hN)).2
  intro j
  have hmem : orbIdx (rotOn N) x j ∈ orb (rotOn N) (3 * N, N) :=
    orb_subset (fun y hy => orb_invariant (rotOn_ord hN) hy) hx (orbIdx_mem_orb (rotOn N) x j)
  rw [exc_orb hN] at hmem
  have : qOn N x j = (orbIdx (rotOn N) x j).1 := rfl
  rw [this]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h <;> rw [h] <;> simp [Nat.dvd_mul_left, dvd_refl]

/-- **Exactly five `W5` pairs are all-integral, for every `N`.** They form a single
rotation orbit, the Conway--Coxeter one. This is the structural half of `thm:orbit`,
with primality removed. -/
theorem allint_card {N : ℕ} (hN : 0 < N) :
    ((W5box N).filter (fun x => ∀ j, N ∣ qOn N x j)).card = 5 := by
  classical
  have hset : (W5box N).filter (fun x => ∀ j, N ∣ qOn N x j) = orb (rotOn N) (3 * N, N) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hb, hall⟩
      exact allint_of_orbit hN (Finset.mem_filter.mp hb).2 hall
    · intro hx
      exact ⟨orb_subset (rotOn_maps hN) (exc_mem hN) hx, allint_of_mem_orb hN hx⟩
  rw [hset, card_orb (rotOn_ord hN) (rotOn_free hN _ (exc_mem hN))]

end VicoEnum
