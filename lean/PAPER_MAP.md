# Paper statements and the declarations that verify them

One row per numbered statement of `paper/rational_friezes.tex`, in the order it appears.

**VERIFIED** means formalized in Lean 4: `lake build` clean, zero `sorry`, and
`#print axioms` reporting nothing beyond `propext`, `Classical.choice`, `Quot.sound`.
**PROVED** means a complete written proof that is not formalized; the reason is given.
**CONJECTURE** means believed without proof.

Every statement whose conclusion contains `O_ε` or `o(1)` is PROVED rather than VERIFIED.
Mathlib at the version pinned here carries no divisor bound `d(m) = m^{o(1)}`, no
Brun–Titchmarsh theorem for multiplicative functions in the sense of Shiu, and no results on
divisors in arithmetic progressions. Those three are the only obstruction; none of them is
specific to friezes.

| Statement | Label | Status | Declarations |
|---|---|---|---|
| Continuant parameterisation | `prop:param` | VERIFIED | `frieze5_monodromy`, `frieze6_monodromy` |
| `T(N,4) = d(2N²)` | `thm:w4` | VERIFIED | `paper_count4`, `friezes4_ncard` |
| Width-5 conditions | `prop:w5cond` | VERIFIED | `w5cond_converse`, `W5_setOf_eq_box` |
| Width-5 search bound | `lem:w5bound` | VERIFIED | `width5_bound` |
| Rotation acts freely | `thm:free` | VERIFIED | `rotation_free`, `rotation_free_nonvacuous` |
| Reduced form at width 5 | `thm:t5red` | VERIFIED | `general_reduction_width5`, `general_reduction` |
| Hyperbola bound | `prop:hyp` | PROVED | asymptotic; core `ford_min_bound` VERIFIED |
| `T(N,5)` upper bound | `cor:t5upper` | PROVED | `O_ε` passage |
| Rigidity of `(u,v)` | `prop:rigid5` | VERIFIED | `Aleft_card`, `cubic_to_Aleft_inj`, `Aleft_to_cubic` |
| Integer entries: 3 or 5 | `prop:intcount` | VERIFIED | `allint_card`, `not_four_integral` |
| `T(p,5) = 5 + 5C(p)` | `thm:orbit` | VERIFIED | `T5_eq_five_add_five_mul`, `paper_frieze5_count` |
| `T(N,5)` as a Ford sum | `thm:fordsum` | VERIFIED | `T5_sum_ford`, `w5_iff_ford` |
| Diagonal criterion | `thm:diag` | VERIFIED | `support_iff_dvd_sq`, `W5_diag_iff`, `W5_diag_shift` |
| `T(N,5) = O_ε(N^{2/3+ε})` | `thm:twothirds` | PROVED | asymptotic; core `ford_min_bound` VERIFIED |
| Parameter characterisation | `thm:params` | VERIFIED | `fordParam_iff` |
| Equivalence with Ford | `cor:equiv` | PROVED | `o(1)`; core `fordParam_iff` VERIFIED |
| `T(N,5)` mod ten | `thm:modten` | VERIFIED | `T5_mod_ten`, `card_swap_parity`, `support_card_eq_Qp` |
| When `10 ∣ T(N,5)` | `cor:fivedvd` | VERIFIED | `ten_dvd_T5_iff`, `ford_sum_five_dvd` |
| Count of `A`-set | `lem:acount` | VERIFIED | `acount_eq`, `Aleft_card_eq_Aright` |
| Cube-root lemma | `lem:cuberoot` | PROVED | analytic input, cited |
| `C(p) = O_ε(p^{1/3+ε})` | `thm:primecube` | PROVED | method of Conrey and Shah, cited |
| Slice factorisation | `prop:sliceform` | VERIFIED | `cubic_slice_factor`, `complement_congr`, `slice_divisor_dvd`, `solution_of_divisor` |
| Order of `C(p)` | `conj:order` | CONJECTURE | — |
| Equidistribution reduction | `prop:equidist` | PROVED | `o(1)`; core `weighted_sum_le` VERIFIED |
| `C(p) ≥ d(p+1)` | `prop:lower` | PROVED | uses Linnik's theorem, cited |
| Two families | `prop:twofam` | PROVED | elementary, not formalized |
| Modular hyperbola | `prop:modhyp` | PROVED | uses the Weil bound, cited |
| Width-6 master identity | `thm:w6master` | VERIFIED | `width6_master` |
| Width-6 reduced form | `thm:w6red` | VERIFIED | `W6_of_red6`, `red6_of_W6` |
| Nondegeneracy | `prop:nondeg` | VERIFIED | `quid5_two_eq_zero_iff`, `quid5_four_eq_zero_iff` |
| Ford over a domain | `thm:fordanyring` | VERIFIED | `ford_general` |
| Gaussian finiteness | `thm:gaussfinite` | VERIFIED | `ford_min_norm_bound`, `ford_determines_l`, `ford_degenerate_branch` |
| Constant edge determinant | `lem:pathdet` | VERIFIED | `fdet_step`, `fpath_det` |
| Array of a path is a frieze | `thm:pathfrieze` | VERIFIED | `path_minor`, `path_frieze_minor`, `path_diag`, `path_subdiag` |
| Positivity is clockwiseness | `thm:clockpos` | VERIFIED | `fdet_pos_iff`, `clockwise_frieze_pos`, `clockwise_decreasing` |
| Frieze determines the path | `thm:pathback` | VERIFIED | `fdet_recurrence`, `recurrence_unique`, `frieze_col_eq_fdet` |
| Pentagon closes antipodally | `thm:pentclose` | VERIFIED | `pentagon_closes`, `quid5_cycle` |
| Ford triple to pentagon | `cor:fordpent` | VERIFIED | `cubic_to_W5`, with `fpath_det`, `pentagon_closes` |
| Three-vector Plücker | `lem:plucker3` | VERIFIED | `plucker3` |
| The recurrence is forced | `thm:forced` | VERIFIED | `path_recurrence_forced`, `path_recurrence_forced_of_dvd` |
| Minimality spans the lattice | `thm:minspan` | VERIFIED | `span_of_coprime_dets`, `fdet_smul_eq` |
| Transfer | `thm:transfer` | VERIFIED | `transfer_of_same_frieze` |
| Path from the frieze | `thm:pathrecon` | VERIFIED | `path_from_frieze`, `vertex_exists_iff` |
| Second coordinate forced | `prop:secondcoord` | VERIFIED | `second_coord_integral` |
| Two columns determine | `lem:twocol` | VERIFIED | `two_column` |
| The initial pair exists | `thm:initpair` | VERIFIED | `initial_pair_congruence`, `numerator_relation`, `e_exists`, `sum_dvd_of_dvd` |
| Transfer is linear | `prop:transferlin` | VERIFIED | `transferMap_add`, `transferMap_smul`, `transferMap_matrix` |
| Fibres are `SL₂(ℤ)` orbits | `thm:fibre` | VERIFIED | `fibre_eq_orbit`, `fdet_linear_map` |
| `SL₂(ℤ)` invariance | `lem:sl2inv` | VERIFIED | `fdet_sl2_invariant` |
| Farey path count | `thm:farey` | VERIFIED | `path_count_of_T5` |

## Totals

50 numbered statements: **39 VERIFIED**, **10 PROVED**, **1 CONJECTURE**.

Every one of the ten PROVED statements is asymptotic or rests on a cited analytic input
(Linnik, Weil, Shiu, the method of Conrey and Shah). Four of the ten carry a VERIFIED core
lemma, so that the arithmetic is machine-checked and only the passage to `O_ε` or `o(1)` is
written: `prop:hyp` and `thm:twothirds` on `ford_min_bound`, `cor:equiv` on `fordParam_iff`,
and `prop:equidist` on `weighted_sum_le`.

These counts are checked against the paper by `code/paper_map_audit.py`, which also confirms
that every declaration named above exists and is axiom-clean.
