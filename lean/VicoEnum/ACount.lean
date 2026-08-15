/-
  VicoEnum/ACount.lean

  The correspondence behind Lemma `lem:acount`, and the round trip of Proposition
  `prop:modhyp`.

  `lem:acount` states `A(p) = 5 + 2C(p)`, where

      A(p) = #{(u,v) : gcd(u,v) = 1, uv ∣ p(u+v+1)},
      C(p) = #{(s,t,m) : s t m = p + t + m}.

  Its proof has four steps: the solutions coprime to `p` are the five of
  `prop:rigid5`; otherwise `p` divides exactly one of `u` and `v`; the two halves are
  equinumerous by the symmetry in `u` and `v`; and the half with `p ∣ u` corresponds to the
  cubic. What is proved here is the arithmetic of that fourth step: the cubic in its cleared
  form, the divisibility half of the `A`-condition under the substitution, and both factors
  of the coprimality. The count itself, and the backward map from an `A`-solution to the
  cubic, need the three bookkeeping steps packaged as `Finset` cardinalities and are not
  proved here.

  The arithmetic is arranged so that the only subtraction is `st - 1`, guarded by `1 < st`.
-/
import VicoEnum.ShiftDecomp

namespace VicoEnum

/-! ## The substitution `u = ps`, `v = st - 1` -/

/-- With `1 < st` the identity `ps + (st-1) + 1 = s(p+t)` holds over `ℕ`. -/
theorem acount_sum {p s t : ℕ} (hst : 1 < s * t) :
    p * s + (s * t - 1) + 1 = s * (p + t) := by
  obtain ⟨w, hw⟩ : ∃ w, s * t = w + 1 := ⟨s * t - 1, by omega⟩
  have e : s * (p + t) = s * p + s * t := by ring
  have e2 : p * s = s * p := by ring
  omega

/-- The cubic, cleared of its subtraction: `stm = p+t+m` is `(st-1)m = p+t`. -/
theorem acount_cubic_clear {p s t m : ℕ} (hst : 1 < s * t) (h : s * t * m = p + t + m) :
    (s * t - 1) * m = p + t := by
  obtain ⟨w, hw⟩ : ∃ w, s * t = w + 1 := ⟨s * t - 1, by omega⟩
  have e : (w + 1) * m = w * m + m := by ring
  have hsub : s * t - 1 = w := by omega
  rw [hw] at h
  rw [hsub]
  omega

/-- **Forward.** A solution of the cubic gives a solution of the `A`-condition with
`p ∣ u`, via `u = ps` and `v = st - 1`. -/
theorem acount_forward {p s t m : ℕ} (hst : 1 < s * t) (h : s * t * m = p + t + m) :
    (p * s) * (s * t - 1) ∣ p * (p * s + (s * t - 1) + 1) := by
  refine ⟨m, ?_⟩
  rw [acount_sum hst, ← acount_cubic_clear hst h]
  ring

/-- The reverse implication of the same rearrangement: `(st-1)m = p+t` gives back
`stm = p+t+m`. This is not the backward map of the paper's proof, which starts from an
`A`-solution and produces `s`, `t` and `m`; that map is not formalised here. -/
theorem acount_backward {p s t m : ℕ} (hst : 1 < s * t) (hm : (s * t - 1) * m = p + t) :
    s * t * m = p + t + m := by
  obtain ⟨w, hw⟩ : ∃ w, s * t = w + 1 := ⟨s * t - 1, by omega⟩
  have e : (w + 1) * m = w * m + m := by ring
  rw [hw]
  rw [hw] at hm
  simp only [Nat.add_sub_cancel] at hm
  omega

/-- The cubic and its cleared form are equivalent. -/
theorem acount_iff {p s t m : ℕ} (hst : 1 < s * t) :
    s * t * m = p + t + m ↔ (s * t - 1) * m = p + t :=
  ⟨acount_cubic_clear hst, acount_backward hst⟩

/-! ## Coprimality of the image

`gcd(ps, st-1) = 1`. The factor `s` is prime to `st-1` outright, and `p` is prime to it
because `st ≡ 1 mod p` would force `p ∣ t` and then `st ≡ 0`. -/

/-- `s` is prime to `st - 1`. -/
theorem gcd_left {s t : ℕ} (hst : 1 < s * t) : Nat.gcd s (s * t - 1) = 1 := by
  have h : Nat.gcd s (s * t - 1) ∣ s := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd s (s * t - 1) ∣ s * t - 1 := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd s (s * t - 1) ∣ s * t := Dvd.dvd.mul_right h t
  have h4 : Nat.gcd s (s * t - 1) ∣ 1 := by
    have hd := Nat.dvd_sub' h3 h2
    rwa [show s * t - (s * t - 1) = 1 from by omega] at hd
  exact Nat.eq_one_of_dvd_one h4

/-- **`p` is prime to `st - 1`.** This is the second factor of the coprimality, and it uses
the cubic: `st ≡ 1 mod p` would give `m ≡ t + m`, hence `p ∣ t`, hence `st ≡ 0`. -/
theorem p_not_dvd_of_cubic {p s t m : ℕ} (hp : 1 < p) (hst : 1 < s * t)
    (h : s * t * m = p + t + m) : ¬ (p ∣ s * t - 1) := by
  haveI : Fact (1 < p) := ⟨hp⟩
  rintro ⟨c, hc⟩
  have hstp : s * t = p * c + 1 := by omega
  have h1 : ((s : ZMod p)) * t = 1 := by
    have hcast : ((s * t : ℕ) : ZMod p) = ((p * c + 1 : ℕ) : ZMod p) := by rw [hstp]
    push_cast at hcast
    simpa using hcast
  have h2 : ((s : ZMod p)) * t * m = t + m := by
    have hcast : ((s * t * m : ℕ) : ZMod p) = ((p + t + m : ℕ) : ZMod p) := by rw [h]
    push_cast at hcast
    simpa using hcast
  rw [h1, one_mul] at h2
  have ht : ((t : ZMod p)) = 0 := by linear_combination -h2
  rw [ht, mul_zero] at h1
  exact zero_ne_one h1

/-- **The full coprimality.** Both factors together: `gcd(ps, st-1) = 1`. -/
theorem gcd_image {p s t m : ℕ} (hp : p.Prime) (hst : 1 < s * t)
    (h : s * t * m = p + t + m) : Nat.gcd (p * s) (s * t - 1) = 1 := by
  have hpd : ¬ (p ∣ s * t - 1) := p_not_dvd_of_cubic hp.one_lt hst h
  have hcp : Nat.Coprime p (s * t - 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hcs : Nat.Coprime s (s * t - 1) := gcd_left hst
  exact Nat.Coprime.mul hcp hcs

/-! ## Proposition `prop:modhyp`, the round trip

The map `(a,u,v) ↦ (au-1, av-1)` sends a solution of `auv = p+u+v` to a factorisation of
`ap+1`, and `fixed_point_hyperbola` sends such a factorisation back to a solution. What is
proved below is the factorisation together with injectivity of the map in `u` and `v` for a
fixed `a`. Recovering `a` itself from the pair, as `(de-1)/p`, is the remaining part of
Proposition `prop:modhyp` and is not formalised. -/

/-- The factorisation, together with injectivity of `x ↦ ax-1` for fixed `a`. The second
conjunct does not use the hypothesis `h`; it is recorded here because it is the part of the
injectivity that the counting argument consumes. -/
theorem modhyp_round_trip {p a u v : ℤ} (ha : a ≠ 0) (h : a * u * v = p + u + v) :
    (a * u - 1) * (a * v - 1) = a * p + 1 ∧
    (∀ u' v' : ℤ, a * u' - 1 = a * u - 1 → a * v' - 1 = a * v - 1 →
      u' = u ∧ v' = v) := by
  refine ⟨by linear_combination a * h, ?_⟩
  intro u' v' hu hv
  constructor
  · have : a * u' = a * u := by linarith
    exact mul_left_cancel₀ ha this
  · have : a * v' = a * v := by linarith
    exact mul_left_cancel₀ ha this

end VicoEnum
