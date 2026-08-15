/-
  VicoEnum/Count.lean

  D8:  the width-5 count `T(N,5)` is a computable finite quantity, and the
       tabulated values are correct.

  The content is completeness: `width5_bound` says every solution lies inside an
  explicit box, so the a priori infinite solution set is literally equal to a
  `Finset.filter` over that box. Once that is proved, the count is a closed term
  and specific values are decided by the kernel.
-/
import VicoEnum.Basic

namespace VicoEnum

open Finset

/-- The arithmetic conditions on the numerators `p = N·a₀`, `q = N·a₁` defining a
positive width-5 frieze over `(1/N)ℤ`. -/
def W5 (N p q : ℕ) : Prop :=
  0 < p ∧ 0 < q ∧ N ^ 2 < p * q ∧ N ∣ p * q ∧
    (p * q - N ^ 2) ∣ N ^ 2 * (p + N) ∧ (p * q - N ^ 2) ∣ N ^ 2 * (q + N)

instance (N p q : ℕ) : Decidable (W5 N p q) := by unfold W5; infer_instance

/-- **Lemma `lem:w5bound`.** The `ℕ` form of the search bound, transferred from
`width5_bound` over `ℤ`. -/
theorem width5_bound_nat {N p q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hlt : N ^ 2 < p * q) (hdvd : (p * q - N ^ 2) ∣ N ^ 2 * (q + N)) :
    p ≤ N ^ 3 + 2 * N ^ 2 := by
  have hcast : ((p * q - N ^ 2 : ℕ) : ℤ) = (p : ℤ) * (q : ℤ) - (N : ℤ) ^ 2 := by
    have : (N : ℕ) ^ 2 ≤ p * q := hlt.le
    push_cast [Nat.cast_sub this]
    ring
  have hZ : ((p : ℤ) * (q : ℤ) - (N : ℤ) ^ 2) ∣ (N : ℤ) ^ 2 * ((q : ℤ) + (N : ℤ)) := by
    have := Int.natCast_dvd_natCast.mpr hdvd
    rw [hcast] at this
    push_cast at this
    exact this
  have hposZ : 0 < (p : ℤ) * (q : ℤ) - (N : ℤ) ^ 2 := by
    rw [← hcast]; exact_mod_cast Nat.sub_pos_of_lt hlt
  have hNZ : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have := width5_bound hNZ hqZ hposZ hZ
  exact_mod_cast this

/-- The proved search box. -/
def box5 (N : ℕ) : Finset (ℕ × ℕ) :=
  Icc 1 (N ^ 3 + 2 * N ^ 2) ×ˢ Icc 1 (N ^ 3 + 2 * N ^ 2)

/-- The width-5 count, as a closed computable term. -/
def T5 (N : ℕ) : ℕ := ((box5 N).filter (fun x => W5 N x.1 x.2)).card

/-- **D8, completeness.** The full solution set, which is a priori an unbounded
subset of `ℕ × ℕ`, is exactly the filtered box. This is what makes `T5` the honest
count rather than the result of a cutoff. -/
theorem W5_setOf_eq_box (N : ℕ) (hN : 0 < N) :
    {x : ℕ × ℕ | W5 N x.1 x.2} = ((box5 N).filter (fun x => W5 N x.1 x.2) : Finset (ℕ × ℕ)) := by
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Set.mem_setOf_eq, box5, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_coe, Finset.mem_filter]
  constructor
  · intro h
    have hp := h.1
    have hq := h.2.1
    have hlt := h.2.2.1
    have hdp := h.2.2.2.2.1
    have hdq := h.2.2.2.2.2
    refine ⟨⟨⟨hp, width5_bound_nat hN hq hlt hdq⟩, ⟨hq, ?_⟩⟩, h⟩
    -- the bound on `q` is the same statement with the roles of `p` and `q` swapped
    have hlt' : N ^ 2 < q * p := by rwa [mul_comm]
    have hdp' : (q * p - N ^ 2) ∣ N ^ 2 * (p + N) := by rwa [mul_comm q p]
    exact width5_bound_nat hN hp hlt' hdp'
  · tauto

/-- The solution set is finite, with cardinality `T5 N`. -/
theorem W5_ncard (N : ℕ) (hN : 0 < N) :
    Set.ncard {x : ℕ × ℕ | W5 N x.1 x.2} = T5 N := by
  rw [W5_setOf_eq_box N hN, Set.ncard_coe_Finset, T5]

/-! ## The tabulated values

Each is a kernel computation over the proved box. -/

set_option maxRecDepth 40000 in
theorem T5_one : T5 1 = 5 := by decide

set_option maxRecDepth 400000 in
theorem T5_two : T5 2 = 20 := by decide

set_option maxRecDepth 4000000 in
theorem T5_three : T5 3 = 40 := by decide

set_option maxRecDepth 20000000 in
theorem T5_four : T5 4 = 60 := by decide

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 4000000 in
theorem T5_five : T5 5 = 60 := by decide

/-
  `T5 6` and beyond are out of reach for `decide` on this representation: the
  attempt aborts (SIGABRT) rather than timing out, so it is a hard limit of kernel
  evaluation over `Finset.filter`, not a budget that can be raised. Reaching larger
  `N` needs the divisor-based enumeration of `code/verify_width5_proved.py` carried
  into Lean and proved equal to `T5`, which turns the cost from O(B^2) into
  O(B * d(N^2(p+N))). That is the next step, not a bigger `maxRecDepth`.
-/

end VicoEnum
