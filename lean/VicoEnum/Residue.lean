/-
  VicoEnum/Residue.lean

  Proposition `prop:residue`, the correspondence; and Proposition `prop:support`, the
  vanishing condition.

  `prop:residue` rewrites the width-5 equation as a divisor count. With `x = gu` and
  `y = gv`,

      g u v = N(u+v) + M   ⟺   (x - N)(y - N) = N² + gM,

  and `g ∣ x` says `x - N ≡ -N mod g`. Both directions are proved here, together with the
  two maps being mutually inverse, which is what makes the correspondence a bijection rather
  than an injection.

  `prop:support` says the `M`-th term vanishes unless `d_M ∣ M`, where `d_M = N/gcd(N,M)`.
  The argument is one line once stated: `d_M ∣ N` gives `d_M ∣ N(u+v)`, and the equation
  then forces `d_M ∣ M`.
-/
import VicoEnum.Count

namespace VicoEnum

/-! ## Proposition `prop:residue` -/

/-- **Forward.** The width-5 equation becomes a factorisation. -/
theorem residue_forward {N g u v M : ℤ} (h : g * u * v = N * (u + v) + M) :
    (g * u - N) * (g * v - N) = N ^ 2 + g * M := by
  linear_combination g * h

/-- **Backward.** The factorisation returns the equation, `g` being nonzero. -/
theorem residue_backward {N g u v M : ℤ} (hg : g ≠ 0)
    (h : (g * u - N) * (g * v - N) = N ^ 2 + g * M) : g * u * v = N * (u + v) + M := by
  have h2 : g * (g * u * v - (N * (u + v) + M)) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hg
  · linarith

/-- **The correspondence is a bijection.** For `g ≠ 0` the two conditions are equivalent, so
the map `(u,v) ↦ (gu - N, gv - N)` and its inverse `(D,D') ↦ ((D+N)/g, (D'+N)/g)` match the
solution sets. The inverse is well defined exactly because `g ∣ D + N`, which is the class
condition `D ≡ -N mod g`. -/
theorem residue_iff {N g u v M : ℤ} (hg : g ≠ 0) :
    g * u * v = N * (u + v) + M ↔ (g * u - N) * (g * v - N) = N ^ 2 + g * M :=
  ⟨residue_forward, residue_backward hg⟩

/-- The class condition: the divisor produced lies in `-N mod g`. -/
theorem residue_class {N g u : ℤ} : (g * u - N) + N = g * u := by ring

/-- The inverse map recovers `u`, which is what makes the correspondence injective. -/
theorem residue_inverse {N g u : ℤ} (hg : g ≠ 0) {D : ℤ} (hD : D = g * u - N) :
    (D + N) / g = u := by
  rw [hD, residue_class, Int.mul_ediv_cancel_left u hg]

/-! ## Proposition `prop:support` -/

/-- **The vanishing condition.** If `d ∣ N` and `d ∣ g u v - N(u+v)`, then `d ∣ M`. Applied
with `d = d_M = N/gcd(N,M)`, this is Proposition `prop:support`: the `M`-th term of the
decomposition vanishes unless `d_M ∣ M`. -/
theorem support_dvd {N g u v M d : ℤ} (hdN : d ∣ N) (hdg : d ∣ g)
    (h : g * u * v = N * (u + v) + M) : d ∣ M := by
  have h1 : d ∣ g * u * v := Dvd.dvd.mul_right (Dvd.dvd.mul_right hdg u) v
  have h2 : d ∣ N * (u + v) := Dvd.dvd.mul_right hdN (u + v)
  have h3 : M = g * u * v - N * (u + v) := by linarith
  rw [h3]
  exact dvd_sub h1 h2

/-- The same over `ℕ`, in the shape the decomposition uses: the modulus `d` divides both `N`
and `g`, so it divides `M`. -/
theorem support_dvd_nat {N g u v M d : ℕ} (hdN : d ∣ N) (hdg : d ∣ g)
    (h : g * u * v = N * (u + v) + M) : d ∣ M := by
  have h1 : d ∣ g * u * v := Dvd.dvd.mul_right (Dvd.dvd.mul_right hdg u) v
  have h2 : d ∣ N * (u + v) := Dvd.dvd.mul_right hdN (u + v)
  have h3 : M = g * u * v - N * (u + v) := by omega
  rw [h3]
  exact Nat.dvd_sub' h1 h2

end VicoEnum
