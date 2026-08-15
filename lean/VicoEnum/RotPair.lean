/-
  VicoEnum/RotPair.lean

  The rotation on numerator pairs preserves `W5`.

  Transporting Theorem `thm:free` to the index set of `T5` needs the rotation of quiddity
  cycles written as a map on the pairs `(p,q)` that `W5` constrains. Reading the
  parameterisation, the next numerator is `r = N²(p+N)/(pq-N²)`. Division in `ℕ` makes that
  awkward to work with, so the step is stated relationally, by its defining equation

      r · (pq - N²) = N²(p + N),

  and `W5 N p q` together with that equation is shown to give `W5 N q r`. Everything is
  driven by one identity: writing `e = pq - N²` and `f = qr - N²`,

      f · e = N³(q + N),

  from which each of the six clauses of `W5 N q r` follows by cancelling `e`.

  What is proved in `Assemble.lean` as `rotPair_five` is that iterating the step five times returns to `(p,q)`. That is
  the cyclic closure; with `five_dvd_card_of_free` it gives `5 ∣ T5 N`, and `Count5.lean`
  carries that to `5 ∣ T(N,5)`.
-/
import VicoEnum.Count

namespace VicoEnum

/-- The rotation step on numerator pairs, stated by its defining equation so that no
division occurs. -/
def RotStep (N p q r : ℕ) : Prop := r * (p * q - N ^ 2) = N ^ 2 * (p + N)

/-- **The rotation preserves `W5`.** -/
theorem W5_rot {N p q r : ℕ} (hN : 0 < N) (h : W5 N p q) (hr : RotStep N p q r) :
    W5 N q r := by
  obtain ⟨hp, hq, hlt, hdvd, hdp, hdq⟩ := h
  -- name e = pq - N², so that pq = N² + e and e > 0
  obtain ⟨e, he⟩ : ∃ e, p * q = N ^ 2 + e ∧ 0 < e := ⟨p * q - N ^ 2, by omega, by omega⟩
  obtain ⟨hpq, hepos⟩ := he
  have hesub : p * q - N ^ 2 = e := by omega
  simp only [RotStep] at hr
  rw [hesub] at hr hdp hdq
  -- N ∣ e
  have hNe : N ∣ e := by
    obtain ⟨c, hc⟩ := hdvd
    have hsq : N ^ 2 = N * N := sq N
    have hcN : N ≤ c := by nlinarith [hN, hepos, hpq, hc]
    obtain ⟨d, rfl⟩ : ∃ d, c = N + d := ⟨c - N, by omega⟩
    refine ⟨d, ?_⟩
    have hexp : N * (N + d) = N * N + N * d := by ring
    omega
  -- e ∣ N²(q+N), say N²(q+N) = e·k
  obtain ⟨k, hk⟩ := hdq
  -- r > 0
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · exfalso
      simp only [zero_mul] at hr
      have : 0 < N ^ 2 * (p + N) := by positivity
      omega
    · exact h
  -- the driving identity: (qr - N²)·e = N³(q+N), via qr·e = N²(pq + qN)
  have hqre : q * r * e = N ^ 2 * (p * q + q * N) := by
    calc q * r * e = q * (r * e) := by ring
      _ = q * (N ^ 2 * (p + N)) := by rw [hr]
      _ = N ^ 2 * (p * q + q * N) := by ring
  have hgt : N ^ 2 < q * r := by
    by_contra hcon
    push_neg at hcon
    have h1 : q * r * e ≤ N ^ 2 * e := Nat.mul_le_mul_right e hcon
    rw [hqre] at h1
    nlinarith [hpq, hepos, hN, hq]
  obtain ⟨f, hf⟩ : ∃ f, q * r = N ^ 2 + f ∧ 0 < f := ⟨q * r - N ^ 2, by omega, by omega⟩
  obtain ⟨hqr, hfpos⟩ := hf
  have hfsub : q * r - N ^ 2 = f := by omega
  have hfe : f * e = N ^ 3 * (q + N) := by
    have h1 : (N ^ 2 + f) * e = N ^ 2 * (p * q + q * N) := by rw [← hqr]; exact hqre
    have h2 : (N ^ 2 + f) * e = N ^ 2 * e + f * e := by ring
    have h3 : N ^ 2 * (p * q + q * N) = N ^ 2 * (N ^ 2 + e) + N ^ 2 * q * N := by
      rw [hpq]; ring
    have h4 : N ^ 2 * (N ^ 2 + e) + N ^ 2 * q * N = N ^ 2 * e + N ^ 3 * (q + N) := by ring
    omega
  -- f = N·k, so N ∣ qr and f ∣ N²(q+N)
  have hfk : f = N * k := by
    have h1 : f * e = N * (e * k) := by
      rw [hfe]
      have : N ^ 3 * (q + N) = N * (N ^ 2 * (q + N)) := by ring
      rw [this, hk]
    have h2 : f * e = N * k * e := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hepos h2
  refine ⟨hq, hrpos, hgt, ?_, ?_, ?_⟩
  · -- N ∣ qr
    obtain ⟨c, hc⟩ := hNe
    exact ⟨N + k, by rw [hqr, hfk]; ring⟩
  · -- (qr - N²) ∣ N²(q+N)
    rw [hfsub]
    obtain ⟨d, hd⟩ := hNe
    exact ⟨d, by rw [hfk, hk, hd]; ring⟩
  · -- (qr - N²) ∣ N²(r+N), with cofactor p
    rw [hfsub]
    refine ⟨p, ?_⟩
    have h1 : N ^ 2 * (r + N) * e = N ^ 3 * (p * (q + N)) := by
      calc N ^ 2 * (r + N) * e = N ^ 2 * (r * e) + N ^ 3 * e := by ring
        _ = N ^ 2 * (N ^ 2 * (p + N)) + N ^ 3 * e := by rw [hr]
        _ = N ^ 3 * (N * p + (N ^ 2 + e)) := by ring
        _ = N ^ 3 * (N * p + p * q) := by rw [← hpq]
        _ = N ^ 3 * (p * (q + N)) := by ring
    have h2 : f * p * e = N ^ 3 * (p * (q + N)) := by
      calc f * p * e = (f * e) * p := by ring
        _ = N ^ 3 * (q + N) * p := by rw [hfe]
        _ = N ^ 3 * (p * (q + N)) := by ring
    have h3 : N ^ 2 * (r + N) * e = f * p * e := by rw [h1, h2]
    exact Nat.eq_of_mul_eq_mul_right hepos h3

end VicoEnum
