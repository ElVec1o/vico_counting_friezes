/-
  VicoEnum/FordToFrieze.lean

  The explicit map from a solution of Ford's cubic to a frieze.

  A solution `(s,t,m)` of `stm = p+t+m` gives the coprime pair `(u,v) = (ps, st-1)`
  (`cubic_to_Aleft`), which lies in `ASet p`; `mkG` completes it to a Markov quadruple and
  `mkv` returns the `W5` pair `(gu-p, gv-p)`, where `g = p(u+v+1)/uv`. That pair is the
  numerator pair of a width-5 frieze over `(1/p)Z`.

  `cubic_to_Aleft_inj` and `Aleft_to_cubic` make this a bijection onto the pairs of `ASet p`
  with `p | u`, and `T5_eq_five_add_five_mul` says the friezes number `5 + 5 C(p)`, of which
  five are the integral ones. So the solutions of the cubic correspond to the rotation
  orbits of the non-integral friezes, one solution per orbit.

  Through Theorem B of the classification cited in the paper, each such frieze is a minimal
  closed clockwise path of length five in the Farey graph `F_p`, obtained from the quiddity
  by `v_{i+1} = (q_i/p) v_i - v_{i-1}`. The composite sends a solution of the cubic to one
  pentagon per rotation orbit.
-/
import VicoEnum.FordParity

namespace VicoEnum

/-- **The explicit map from a Ford triple to a frieze.** A solution `(s,t,m)` of
`stm = p+t+m` gives the coprime pair `(ps, st-1)`, which `mkG` completes to a Markov
quadruple and `mkv` sends to a `W5` pair. -/
theorem cubic_to_W5 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ cubicTriples p) :
    mkv p (mkG p (p * x.1, x.1 * x.2.1 - 1)) ∈ W5Set p := by
  have hA : (p * x.1, x.1 * x.2.1 - 1) ∈ Aleft p := cubic_to_Aleft hp h5 hx
  have hAS : (p * x.1, x.1 * x.2.1 - 1) ∈ ASet p := (Finset.mem_filter.mp hA).1
  exact mkv_mapsTo hp.pos (ASet_to_MarkovAt_p hp hAS).1

end VicoEnum
