# Counting positive rational friezes over (1/N)Z

[![verify](https://github.com/ElVec1o/vico_counting_friezes/actions/workflows/verify.yml/badge.svg)](https://github.com/ElVec1o/vico_counting_friezes/actions/workflows/verify.yml)

Let `T(N,n)` be the number of positive rational frieze patterns of width `n` whose entries
all lie in `(1/N)Z`, in the sense of Karpenkov, Short, van Son and Zabolotskii
(arXiv:2601.21445, section 6). Conway and Coxeter give `T(1,n) = C_(n-2)`.

**Per-statement map.** `lean/PAPER_MAP.md` names, for each of the fifty numbered statements
of the paper, the declarations that verify it or the reason none exists: **39 VERIFIED, 10
PROVED, 1 CONJECTURE**. Every one of the ten written proofs is asymptotic or rests on a cited
analytic input, and four carry a verified core lemma. `code/paper_map_audit.py` checks the
map against the paper and the library; CI checks the declarations are axiom-clean.

Every claim below carries one of five labels. **VERIFIED** means formalized in Lean 4:
`lake build` clean, zero `sorry`, and `#print axioms` reporting nothing beyond
`propext`, `Classical.choice`, `Quot.sound`. **PROVED** means a complete written proof,
not formalized. **HEURISTIC** means computational support only. **CONJECTURE** means
believed without proof. **FALSE** means a counterexample is in hand.

## Structure at every width

Write `a_j = p_j / N` and let `C_k` be the homogenised frieze continuant,

    C_0 = 1,  C_1(p) = p,  C_k(p_i..p_{i+k-1}) = p_{i+k-1} C_{k-1} - N^2 C_{k-2},

so that `K_k(a_i,...) = C_k(p_i,...) / N^k`.

- **The lattice criterion at every width.** Rows `r` and `n-r` of a frieze carry the same
  entries, so the conditions defining a frieze over `(1/N)Z` come from rows
  `2 <= r <= floor(n/2)` only, and read

      C_{r-1}(p_j,...,p_{j+r-2}) > 0    and    N^{r-2} | C_{r-1}(p_j,...,p_{j+r-2})

  for every such `r` and every `j` mod `n`. VERIFIED (`glide`, `glide_core`, `Kr_homog`,
  `row_lattice_iff`, `row_pos_iff`). The glide needs no extra input: splitting the
  monodromy as `PQ = -I` with `det P = 1` and reading entries `(0,1)` and `(1,1)` gives
  `Q_11 = -P_00`, and those two entries are the two continuants.

  The cutoff is sharp both ways. Truncating at `floor(n/2)-1` overcounts; extending to
  `floor(n/2)+1` changes nothing. At `N = 1` the Cuntz-Holm box is small enough to sweep
  completely and the criterion returns `5, 14, 42, 132, 429` at widths `5..9`, the Catalan
  numbers.

- **A Markov-type reduction at every width.** With
  `g = gcd(A + N^{n-4}, B + N^{n-4})` for the two continuant windows `A`, `B`, coprime
  quotients `U`, `V`, and `M = gUV - N^{n-4}(U+V)`, the lattice conditions on the outer
  entries collapse to

      g U V = N^{n-4}(U+V) + M,     N^{n-4} R | g M,     M | N^2 R,

  where `R` is a third continuant window, empty at width `5`. VERIFIED
  (`general_reduction`, `general_dvd_iff`, `general_factor`). The mechanism is the
  Desnanot-Jacobi identity `E R - A B = -N^{2(n-4)}`, that is the determinant of a product
  of matrices `[[p_j, -N^2],[1,0]]` each of determinant `N^2` (`Cw_desnanot`, VERIFIED).

- **A uniform bound on the entries.** Every entry of a positive frieze of width `n` over
  `(1/N)Z` satisfies `a_i <= (n-4)N^2 + 2N`. This is Theorem 3.6 of Cuntz and Holm,
  J. Comb. Algebra 3 (2019) 153-188, specialised to `(1/N)Z`; it is theirs, not ours. The
  version here is re-proved directly by telescoping rather than by contradiction
  (`cuntz_holm_bound`, VERIFIED). At `N = 1` it is the Conway-Coxeter fact that a vertex of
  a triangulated `n`-gon meets at most `n-2` triangles. It is sharp: the *rational fan*
  `((n-4)N^2+2N, 1/N, N+1, 2,...,2, N+1, 1/N)` attains it (`fan_monodromy`, `fan_col_one`,
  `fan_col_zero`, VERIFIED).

## The path model, width six, and other coefficient rings

- **The frieze relation is the Plucker relation.** For a sequence of integer vectors with
  `v_{i+1} = c_i v_i - v_{i-1}`, every consecutive determinant is equal to the first
  (`fdet_step`, `fpath_det`, VERIFIED), so one edge check places the whole path in a single
  Farey graph `F_R`. Setting `m_{i,j} = det(v_j, v_i) / R`, every adjacent 2x2 minor equals
  `1`, the diagonal is `0` and the first subdiagonal is `1` (`plucker`, `path_minor`,
  `path_frieze_minor`, VERIFIED). The proof is the Plucker relation
  `[ab][cd] - [ac][bd] + [ad][bc] = 0` applied to `(v_j, v_i, v_{j+1}, v_{i+1})`, which
  turns the minor into `[v_j,v_{j+1}][v_i,v_{i+1}] = R^2`.

  This is width-uniform. The width-five and width-six reductions each need a continuant
  window and hold at one width; this holds for all `i` and `j` at once.

- **Positivity is clockwiseness.** For vertices with positive second coordinate,
  `det(v_j, v_i) > 0` exactly when the vertices are in strict clockwise order on the real
  line, since `R m_{i,j} = b_i b_j (a_j/b_j - a_i/b_i)` (`fdet_pos_iff`,
  `clockwise_frieze_pos`, VERIFIED). Positivity of a frieze and the clockwise condition on
  the path are one condition read on two sides.

- **The path is the frieze's own columns.** `det(v_j, -)` is linear, so a column of the path
  array satisfies the same three-term recurrence as the path, and a solution of a three-term
  recurrence is fixed by two consecutive values (`fdet_recurrence`, `recurrence_unique`,
  `frieze_col_eq_fdet`, VERIFIED). This is the passage back from frieze to path.

  Not formalized: the quotient by `SL_2(Z)` and surjectivity, which are what make Theorem B
  of arXiv:2601.21445 a bijection of sets. That theorem is cited, not reproved.

- **Surjectivity, from the three-vector Plucker identity.** `[w,x]u - [u,x]w + [u,w]x = 0`
  applied to three consecutive vertices of a path in `F_R`, where `[u,w] = [w,x] = R`, gives
  `R x = [u,x] w - R u` (`plucker3`, `path_recurrence_forced`, VERIFIED). So every path in
  `F_R` satisfies the recurrence of the construction, with coefficient its own frieze entry,
  whether or not it was built that way. The construction is not a special family.

- **Minimality means the vertices generate the lattice.** The same identity with `x`
  arbitrary reads `[u,w]x = [u,x]w - [w,x]u`, so if some integer combination of determinants
  equals `1` then every integer vector is an integer combination of vertices
  (`fdet_smul_eq`, `span_of_coprime_dets`, VERIFIED). That is what makes the change of basis
  between two paths integral rather than rational. `transfer_of_same_frieze` is then
  injectivity modulo `SL_2(Z)`, and `fdet_sl2_invariant` is well-definedness. VERIFIED.

  At a prime and width five the correspondence is complete without citing Theorem B of
  arXiv:2601.21445. At general `R` and general width the remaining step is the choice of an
  initial pair realising a prescribed frieze, which is not formalized.

- **The width-six reduced form.** With `A = pq - N^2`, `B = qr - N^2`, `g = gcd(A,B)`,
  `U = A/g`, `V = B/g`, `R = q`, the defining relation is the single master identity

      A B = N^4 + N^2 q f,     that is     g^2 U V = N^4 + N^2 R f,

  again of Ford type (`width6_master`, VERIFIED). The frieze conditions then become a
  divisibility system in `(g,U,V,R)` that is necessary and sufficient (`W6_of_red6`,
  `red6_of_W6`, VERIFIED). `R` is not free: it divides `gcd(gU+N^2, gV+N^2)`.

  The defining conditions alone do not suffice. The lattice condition on the row fixed by
  the glide adds `N | A` and `N | B`; without them `(p,q,r,f) = (1,5,8,1)` at `N = 2`
  satisfies the relations but is not a frieze.

- **Width five over any coefficient ring.** The width-five parameterisation closes after
  five steps over any field (`quid5_cycle`, VERIFIED), and the reduction uses no order.
  Eliminating `p` and `q` gives Ford's equation over any commutative domain,

      D k l = N^4 + N^3 (k + l),

  where `D = pq - N^2`, `N^2(p+N) = Dk`, `N^2(q+N) = Dl` (`ford_general`, VERIFIED).

  Two conditions that positivity hides must be imposed separately: `a_2 = 0` exactly when
  `a_0 = -1`, and `a_4 = 0` exactly when `a_1 = -1` (`quid5_two_eq_zero_iff`,
  `quid5_four_eq_zero_iff`, VERIFIED). Without them the divisibility is vacuous and the
  solution set is infinite.

- **Finiteness over the Gaussian integers.** Over `Z[i]` there is no order, and finiteness
  comes from the norm instead: `min(||k||, ||l||) <= 8N^6 + 2N^8` (`ford_min_norm_bound`,
  VERIFIED), while `l (Dk - N^3) = N^4 + N^3 k` pins the third variable
  (`ford_determines_l`, `ford_degenerate_branch`, VERIFIED). The counts of width-five
  friezes over `(1/N)Z[i]` are `55, 580, 815` for `N = 1, 2, 3`
  (`code/gaussian_width5.py`), against `T(1,5) = 5` over `Z`.

## The width direction at fixed N

- **A new sequence.** `T(2,n) = 4, 20, 102, 511, 2576, 13101` for `n = 4..9`, proved-complete
  via the Cuntz-Holm entry bound `a_i <= (n-4)N^2+2N` (`code/width_sequence.py`,
  `data/T_N2_widths.txt`). `T(2,7) = 511` is new. The sequence is **not in the OEIS** (the
  Catalan control returns matches, this returns none), and `T(1,n)` is the Catalan number
  `C_{n-2}`.

- **No first-order recurrence.** There is no `(alpha n + beta) T(n+1) = (gamma n + delta) T(n)`:
  the five equations these six terms impose have rank four, so only the trivial solution.
  Whether the sequence is P-recursive at all is OPEN, and six terms cannot decide it.

- **Why not more terms.** The proved box costs `(((n-4)N^2+2N)N)^(n-3)`, which at `N=2`,
  `n=10` is already `10^12`. A transfer-matrix enumeration over path states was considered,
  legitimate now that the path model is proved, and killed at the consistency pass: the
  frieze's column entries grow by a factor of about 2.4 per width at `N=2` (8, 20, 48 at
  `n = 5, 6, 7`), so the state space is exponential and the DP does not beat direct
  enumeration. No machinery was built.

- **The N direction is different.** A closed form for `T(N,5)` is Ford-hard: `T(p,5) = 5 + 5C(p)`
  means it would determine the order of `C(p)`.

## The conjectured order, reduced

- **Equidistribution implies the conjecture.** Write `H(n) = sum over a of d(an+1)/a`, the
  count predicted by assuming the divisors of `an+1` fall equally often into each class
  mod `a`. Then `C(p) = O(H(p))` implies `C(p) = p^{o(1)}`. PROVED, elementary: every
  `an+1` with `a <= n+2` is at most `(n+1)^2`, so `H(n) <= (max divisor count) * (harmonic
  sum)`, and `d(m) = m^{o(1)}`. `weighted_sum_le` is the finite core, VERIFIED; the
  remaining input `d(m) = m^{o(1)}` is the Mathlib gap already recorded.

  This does not prove the conjecture. It replaces it by a one-sided bound of standard shape,
  at exactly the moduli where the technology stops.

- **Numerically.** `C(p)/H(p)` lies in `[0.426, 1.074]` over 72 primes below 2000, stable
  from `p` about 60 onwards, mean `0.752`. Three predictions were fixed before the
  computation and all held (`code/equidistribution.py`).

## Where the analytic difficulty sits

- **The cubic is a divisor sum in progressions.** Multiplying `auv = n+u+v` by `a` gives
  `(au-1)(av-1) = an+1`, so the solutions on the `a`-slice are the divisors `d` of `an+1`
  with `d = -1 mod a`; the congruence on the complementary divisor is automatic
  (`cubic_slice_factor`, `complement_congr`, `slice_divisor_dvd`, `solution_of_divisor`,
  VERIFIED). Hence

      C(n) = sum over a = 1..n+2 of #{ d | an+1 : d = -1 mod a }

  needing no primality; checked on 36 values (`code/divisor_slice.py`).

  This locates the difficulty rather than removing it. The modulus `a` and the quantity
  `an+1` move together, so at `a` of size `n^(1/2)` the modulus is comparable to the square
  root of the quantity: the range where equidistribution of divisors in progressions gives
  nothing. It is the same obstruction the modular hyperbola records, with a Weil error of
  size `p^(1/2)` against a quantity of size `p^(1/3)`. The analytic half is not a missing
  trick, it is this problem at that modulus.

- **The fibre description is one theorem.** `fibre_eq_orbit` (VERIFIED): two paths have the
  same frieze **if and only if** they differ by an integer matrix of determinant one. A
  single biconditional, no quotient types, no prose assembly. The forward direction reads
  the four matrix entries off the transfer map by linearity (`transferMap_matrix`) and gets
  the determinant from `fdet_linear_map`, since the matrix preserves a nonzero determinant.
  The backward direction is `fdet_sl2_invariant`.

- **The fibres are exactly the SL_2(Z) orbits.** The transfer formula, read as a function
  of an arbitrary vector, is additive and homogeneous (`transferMap_add`,
  `transferMap_smul`, VERIFIED), so it is an integer matrix; it carries `v k` to `v' k`
  (`transferMap_apply`) and preserves every determinant (`transferMap_det`), so it lies in
  `SL_2(Z)`. This is the quotient statement of the classification.

- **The initial pair exists, constructively.** Two adjacent columns determine a frieze:
  for fixed `j`, both `m_{i,j}` and `m_{j,0} m_{i,1} - m_{j,1} m_{i,0}` satisfy the same
  three-term recurrence in `i` and agree at `i = j` and `i = j+1` (`two_column`, VERIFIED).
  The proof uses only the frieze recurrence, not the path model, which would be circular.
  Cleared of denominators this is `mu_i nu_j - nu_i mu_j = N w_{j,i}` with `K | w_{j,i}`.

  Choosing `lambda` with `sum lambda_j mu_j = g0` and `K e = sum lambda_j nu_j` then gives
  `K(mu_i e - nu_i d) = N sum_j lambda_j w_{j,i} = N K (integer)`, and cancelling `K` gives
  the congruence (`initial_pair_congruence`, VERIFIED). `e` is exhibited, not merely shown
  to exist.

  **With this the correspondence no longer rests on Theorem B of arXiv:2601.21445**, for all
  `R` and all widths: surjectivity (`path_recurrence_forced`), the frieze relations
  (`path_minor`), positivity (`clockwise_frieze_pos`), injectivity modulo `SL_2(Z)`
  (`transfer_of_same_frieze`), and the initial pair (`initial_pair_congruence`). Each is a
  Lean declaration; the packaging of the five into one statement about sets in bijection is
  assembled in the paper, not in Lean.

- **The canonical initial pair.** With `g0` the gcd of the column-zero numerators, taking
  `v0 = (g0/K, 0)` and `v1 = (e, N/g0)` gives `[v0,v1] = R`, and the second coordinate of
  every vertex is then integral automatically, being `mu_i/g0` (`second_coord_integral`,
  VERIFIED). The scale of the pair is forced, not chosen. What remains is one congruence in
  the single unknown `e`, namely `N | mu_i e - nu_i g0/K`; its solvability is CONJECTURE,
  checked on 1510 width-five friezes for `N <= 14` (`code/initial_pair.py`). Replacing
  `g0/K` by `1` does not suffice: it fails for 15 friezes at `N = 12`.

- **The initial pair is a congruence, not a normalisation.** With `[v0,v1] = R` every vertex
  is `m_{i,0} v1 - m_{i,1} v0` (`path_from_frieze`, VERIFIED), so a path realising a
  prescribed frieze has no freedom once the initial pair is fixed. Writing the two leading
  columns as `mu_i/N` and `nu_i/N`, the vertex lies in `Z^2` exactly when `N` divides both
  components of `mu_i v1 - nu_i v0` (`vertex_exists_iff`, VERIFIED). The criterion is
  formalized; its solvability for every `R` and every width is the one open step.

## Closed counts

- **Width 4.** `T(N,4) = d(2N^2)`, the number of divisors of `2N^2` (OEIS A361689).
  VERIFIED (`width4_card`).

- **Width 5.** A Markov-type count of quadruples `(g,u,v,M)`. Three of its six conditions
  are removable: both positivity conditions are automatic, and `g` is determined, leaving

      T(N,5) = #{(u,v,M) : gcd(u,v)=1, M | N^2, uv | N(u+v)+M, N uv | M(N(u+v)+M)}.

  VERIFIED (`t5_pos_auto`, `t5_elim_g`).

- **Width 6.** A closed count. Rows `2`, `3`, `4` are the interior rows; row `4` is row `2`
  permuted and row `3` has period `3`, so `(p_0,p_1,p_2)` gives a frieze if and only if,
  with `e = (p_0p_1p_2 - N^2(p_0+p_2))/N^2` and `p_3 = p_0p_1/e`,

      N^2 | p_0p_1p_2 - N^2(p_0+p_2),  e > 0,   e | p_0p_1,   e | p_1p_2,
      N | p_0p_1, p_1p_2, p_2p_3,      N^2 < p_0p_1, p_1p_2, p_2p_3.

  PROVED, with the ingredients VERIFIED (`w6_row4`, `w6_glide`, `row3_lattice_iff`,
  `row3_pos_iff`, `w6_row3_reduce`). Checked exhaustively over the Cuntz-Holm box for
  `N <= 6`, reproducing `T(N,6) = 14, 102, 259, 487, 504, 1197`.

- **Width 7.** `N | p_j p_{j+1}` and `N^2 < p_j p_{j+1}` for every `j` mod `7`. PROVED.

- **Widths 8 and 9.** The same two conditions plus, writing `w_j = p_j p_{j+1}/N`,
  `N | p_{j+2} w_j` and `p_{j+2}(p_j p_{j+1} - N^2) > N^2 p_j`. PROVED. Sweeping the
  Cuntz-Holm box with the criterion as a pruning rule gives

      T(N,8) = 132, 2576, 9980, 28604   (N = 1..4)
      T(N,9) = 429, 13101               (N = 1,2)

  with `N = 1` giving `C_6` and `C_7`. Neither sequence is in the OEIS.

## The size of T(N,5)

- **Upper bound.** Since `uv` divides a positive number, `(u-N)(v-N) <= N^2 + M <= 2N^2`,
  so `min(u,v) < 3N`: the smaller parameter is *linear* in `N`, against `N^3 + 2N^2` for
  the original parameters. Hence

      T(N,5) <= 2 sum_{M | N^2} sum_{u < 3N} d(Nu + M) = O_eps(N^{1+eps}).

- **The exponent, improved to 2/3.** Sorting each term of the Ford decomposition by its
  least variable gives `T(N,5) = O_eps(N^{2/3+eps})` for every `N`, against the
  `O_eps(N^{1+eps})` above. The engine is `ford_min_bound`: `h u v = A(u+v) + B` forces
  `min(h,u,v)^3 <= 2A min + B`, with no positivity hypotheses. Every term of the
  decomposition has `A <= N` and `B <= N^2`, so `min(h,u,v)^3 <= 8N^2`. VERIFIED
  (`ford_min_bound`, `ford_min_bound_N`, `ford_params_le`); the passage to `O_eps` needs
  only the divisor bound `card_divisors_pow_le`, not a Shiu-type input. The exponent is
  the limit of the method rather than of the truth: the least variable really does reach
  order `N^{2/3}`. At a prime `thm:primecube` stays sharper, at `p^{1/3+eps}`, because the
  substitution of `lem:acount` lowers `B` from `p^2` to `p`.


  VERIFIED (`t5_hyperbola`, `t5_min_bound`, `t5_large_dvd`, `t5_split`, `t5_order_inj`).
  The hyperbola bound is attained for every `2 <= N <= 24`. The classical divisor bound
  `d(n) = O_eps(n^eps)` is not in Mathlib v4.15.0, so it is proved here from scratch as
  `card_divisors_pow_le`, in the form `d(n)^k <= ((2k)^k)^(2^k) * n`; the usual appeal to
  analysis is avoided by writing `a = kb + r` with `r < k`, which gives
  `(a+1)^k <= (2k)^k 2^a` directly.

- **A lower bound, and a disproof.** Taking `u = 1` in the cubic gives a solution for
  every divisor of `p+1`, so `C(p) >= d(p+1)` and `T(p,5) >= 5 d(p+1)`. VERIFIED
  (`cubic_sol_of_divisor`, `cubic_lower_card`). This kills the sharper guess
  `T(N,5) ~ d(N^2) log^2 N`: at a prime `d(p^2) = 3`, so it would force
  `d(p+1) = O(log^2 p)`, and Linnik's theorem applied to `p = -1 mod (primorial)` gives
  primes with `d(p+1) >= 2^r` and `log p << r log r`. The crossover is near `r = 20`,
  where the primorial already exceeds `10^25`, which is why no computation sees it.

- **The conjecture is a problem of Conrey and Ford.** Conrey asked whether
  `xyz + x + y = n` has `O_eps(n^eps)` positive solutions; Ford generalised this to
  `xyz = A(x+y) + B` with `O_eps(|AB|^eps)` solutions (both recorded in Huang,
  arXiv:1108.0095). The width-5 equation `g u v = N(u+v) + M` is Ford's with `A = N`,
  `B = M`. Writing `R_a(n) = #{(x,y) : axy - x - y = n}`, at a prime
  `C(p) = sum_a R_a(p)` and `R_1(p) = d(p+1)`, both checked for every prime below 200.
  So the lower bound proved here is the `a = 1` term, and the conjecture is a named open
  problem. **The contribution is the connection**: frieze patterns over `(1/N)Z` are
  counted by Ford's equation.

- **Conjecturally `N^{o(1)}`.** The surviving form. The evidence for the discarded
  equivalence form was strong and still wrong: frozen on `N <= 600` and tested on the
  disjoint range `601..3000`, the mean ratio moves from
  `2.979` to `2.838`, a shift of `0.953`, with out-of-sample block means `2.847, 2.832,
  2.835, 2.839`. Every rival normalisation drifts on the same test (`d(N^2) sqrt(N)` by
  `0.676`, `N` by `0.424`). HEURISTIC, and it is the only statement in the project below
  PROVED. Proving it needs a bound on divisors in residue classes uniform in the modulus,
  with cancellation across `M`, since a per-`M` bound cannot work: one `M` alone
  contributes 765 pairs at `N = 420`.

- **The conjecture is stated in Lean**, and two cases of it are theorems. `OrderConj` is
  a `Prop`, written as `T(N,5)^k <= C_k * N` so no real exponents are needed.
  `orderConj_width4` proves it **unconditionally at width 4**, since `T(N,4) = d(2N^2)`
  and the divisor bound applies. At a prime `d(p^2) = 3`, so the conjecture says
  `T(p,5) = O(log^2 p)`, and `cubic_pair_iff` reduces that to

      C(p) = sum_{t <= 1+sqrt(p)} #{ w | p+t : w = -1 mod t }  =  O(log^2 p)?

  which is the minimal open case, self-contained and frieze-free.

- **The barrier is exact.** Counting by `(g,M)` instead of `(u,v)`: with `x = gu`,
  `y = gv` the equation becomes `(x-N)(y-N) = N^2 + gM`, and `g | x` says `x-N` lies in
  the class `-N` mod `g`. With `g <= N^2 + 2N` (attained), this makes `T(N,5)` exactly a
  count of divisors of `N^2+gM` in a prescribed residue class mod `g`. PROVED, with
  `t5_g_bound` and `t5_shifted_product` VERIFIED. Every elementary route stops at
  `O(N^{1+o(1)})`: pairing divisors gives `#{D} <= 2(sqrt(N^2+gM)/g + 1)` and the `+1`
  alone sums to `Theta(N)`.

- **No linear lower bound.** `T(N,5) >= cN` is **FALSE**. The minimum of `T(N,5)/N` over
  blocks of fifty decays steadily to `0.2957` at `N = 541`, and every minimiser is prime
  (`code/t5_growth.rs`, `N <= 600`). The true order of `T(N,5)` is open at both ends: the
  exponent `1` is not attained on the computed range either.

- **Why primes are small.** If `gcd(uv,p) = 1` and `uv | p(u+v+1)` then `(u,v)` is one of
  `(1,1), (1,2), (2,1), (2,3), (3,2)`, whatever `p` is. VERIFIED (`t5_prime_rigid`). Those
  five pairs form a single orbit of the `Z/5` rotation action. Every further solution at a
  prime needs `p | uv`.

- **At a prime**, `T(p,5) = A(p) + B(p)` with `A = #{uv | p(u+v+1)}` and
  `B = #{uv | p(u+v+p)}` over coprime pairs, and `10 | T(p,5)`. Every `Z/5` orbit splits
  `2:3` between the two terms except the rigid one, which is `5:0`, so

      3 A(p) - 2 B(p) = 15    and    T(p,5) = (5 A(p) - 15)/2.

  VERIFIED (`orb_IsMp_card`, `W5box_IsMp_count`). The key step is that the number of
  *integer* entries in a width-5 quiddity over `(1/p)Z` is always 3 or 5, and 5 only for the
  Conway-Coxeter frieze `(2,2,1,3,1)` (`w5_val_step`, `zmod5_card`, `w5_integer_count`);
  that pins the orbit profile, and the last position is closed by `w5_last_position`. The
  orbit relation and the `M = p` criterion are carried around the orbit by `qOn_rel` and
  `isMp_iff`, the dichotomy by `dich_pair`, and the exceptional orbit is identified as that
  of `(3p, p)` by `notall_of_not_orb`.

- **The count at every N.** Writing `e = gcd(N,M)` and `d = N/e`,

      T(N,5) = sum over M | N^2 with d | M  of  F(e, M/d),
      F(A,B) = #{(u,v) > 0 : gcd(u,v)=1, uv | A(u+v)+B}

  where `F(A,B)` is the count in Ford's problem for `xyz = A(x+y)+B`. The omitted divisors
  contribute nothing. VERIFIED (`T5_sum_ford`, with `w5_iff_ford` the bijection at each `M`,
  `div_gcd_dvd_of_w5` the support condition and `MarkovAt_eq_empty` the vanishing off it).
  The number of terms is the number of square divisors of `N^3`, OEIS A092520. At `N = p`
  only `M = p, p^2` survive and the two terms are `A(p)` and `B(p)`, so this contains the
  split below. It does not collapse for composite `N`: `T(N,5) = 5 + 5C(N)` is false at
  `N = 12`, where the sides are 310 and 40. Checked against the enumeration for every
  `N <= 60`, the range `31..60` disjoint from the one that suggested it.

- **Counting the objects of KSSZ Theorem B.** Karpenkov, Short, van Son and Zabolotskii
  (arXiv:2601.21445) classify positive rational friezes over `(1/N)Z` of width `n` and gcd
  `K` by the minimal clockwise paths of length `n` in the Farey graph `F_R`, `R = N/K`,
  modulo `SL(2,Z)`. That classification is counted here. Writing `P(R)` for the number of
  those path classes at width five,

      T(N,5) = sum over R | N of P(R),   so   P(R) = sum over d | R of mu(R/d) T(d,5),

  which `T5_sum_ford` evaluates. At every prime `p >= 5`, `P(p) = 5 C(p)`: the Farey graph
  `F_p` carries exactly `5C(p)` closed clockwise pentagons up to `SL(2,Z)`, and counting
  them is Ford's problem. VERIFIED (`path_count_of_T5`); regenerated by
  `code/farey_paths.py`.

- **Which instances of Ford's equation occur, exactly.** A pair `(A,B)` arises as the
  parameters of a term, for some `N`, if and only if `B | gcd(A,B)^2`; and then it arises
  at some `N <= A^2`. VERIFIED (`fordParam_iff`), both directions constructive. Consequence:
  `T(N,5) = N^{o(1)}` is **equivalent** to Ford's conjecture restricted to that family, not
  merely implied by it. The width-five frieze count is a faithful reformulation of a
  subfamily of Ford's problem, so settling either settles the other.

- **The index set is the symmetric friezes.** The support of the decomposition is exactly
  `{M : M | N^2 and N | M^2}`, and `M -> M+N` is a bijection onto the reflection-symmetric
  `W5` pairs, those with `p = q`. So the decomposition carries one Ford term per symmetric
  frieze and the number of terms is `Qp(N)`, the number of square divisors of `N^3`, OEIS
  A092520. VERIFIED (`support_iff_dvd_sq`, `W5_diag_iff`, `W5_diag_shift`).

- **T(N,5) mod 10, exactly.** VERIFIED end to end (`card_swap_parity`,
  `support_card_eq_diag`, `support_card_eq_Qp`, `T5_mod_ten`, `ten_dvd_T5_iff`). `T(N,5) = 5 Qp(N) mod 10`, so `10 | T(N,5)` if and only if
  some exponent in the factorisation of `N` is `1` or `2` mod `4`. The reflection is an
  involution on the `W5` pairs whose fixed points are the symmetric ones, so `T` and `Qp`
  share parity; `five_dvd_T5` supplies the other factor. At a prime this recovers
  `ten_dvd_T5_prime`; the smallest `N > 1` with `10` not dividing `T` is `N = 8`, where
  `Qp = 5` and `T = 145`.

- **A congruence for Ford counts.** For every `N`, five divides the sum of the Ford counts
  of the decomposition, though it divides almost none of the summands: at `N = 8` they are
  17, 27, 31, 31, 39 and sum to 145, and over `N <= 25` only 23 of 101 terms are divisible
  by five while all 25 sums are. VERIFIED (`ford_sum_five_dvd`,
  `ford_sum_five_dvd_squarefree`); it follows from the free rotation action, and nothing in
  `xyz = A(x+y)+B` suggests it. This is what the frieze side gives back to the Diophantine
  side. Regenerated by `code/ford_congruence.py`.

- **Integrality at every N.** Exactly five `W5` pairs have all five quiddity entries
  integral, for every `N`, and they form one rotation orbit, the Conway-Coxeter one; and no
  orbit has exactly four. VERIFIED (`allint_card`, `not_four_integral`). This is the
  structural half of the orbit split with primality removed.

- **The count at a prime.** For every prime `p >= 5`,

      T(p,5) = 5 + 5 C(p),    C(p) = #{(a,u,v) > 0 : a u v = p + u + v}.

  VERIFIED (`T5_eq_five_add_five_mul`), and stated over Definition 2.1 itself as
  `paper_frieze5_count`: the counted object is the set of positive width-5 friezes over
  `(1/p)Z` with periodicity *derived* rather than assumed (`pf_period`), and `C(p)` is the
  full solution count, its search box proved complete by `cubic_box_complete`.
  Independently recomputed for `p = 5, 7, 11, 13, 17, 19`.

  No closed form for `T(p,5)` should be expected: substituting `u = ps`, `v+1 = st` turns
  the `M = p` condition into the symmetric cubic `stm - t - m = p`, that is
  `(st-1)(sm-1) = sp+1`, so `A(p)` is a divisor sum over factorisations of `sp+1`.

- **Primes are cube-root size.** Importing the method of Conrey and Shah
  (arXiv:2112.15551), who bound representations of `n = xyz+x+y+z` by `n^{1/3}` and whose
  Conjecture 1 is the problem in question: every solution of `suv = p+u+v` has
  `min(s,u,v)^3 <= 2p` (VERIFIED, `cube_root_min`), so

      C(p) <= sum_{t <= (2p)^{1/3}} ( d(tp+1) + 2 d(p+t) ),

  and a Shiu-type divisor bound gives `T(p,5) = O_eps(p^{1/3+eps})`. This is the state of
  the art for the family. Note also that the general bound `O_eps(N^{1+eps})` is already
  optimal given that state of the art: its per-`M` input has strength `|AB|^{1/3}`,
  exactly Conrey-Shah, so improving it needs progress on Ford's problem itself.

- **Primes are square-root size** (self-contained proof, retained).** The same cubic bounds the count. Fixing `(t,m)`
  determines `s`, so `C(p) <= #{(t,m) : tm | p+t+m}`; there `tm <= p+t+m` gives
  `(t-1)(m-1) <= p+1`, so the smaller variable is at most `1 + sqrt(p+1)`, and the larger
  divides `p+t`. Since `T(p,5) = 5 + 5 C(p)`,

      T(p,5) <= 5 + 10 sum_{t <= 1+sqrt(p+1)} d(p+t) = O_eps(p^{1/2+eps}),

  against `O_eps(p^{1+eps})` in general. PROVED, ingredients VERIFIED
  (`t5_cubic_hyperbola`, `t5_cubic_min`, `t5_cubic_dvd`). Checked on all 123 primes below
  700; there `T(p,5)/sqrt(p)` has mean 15.2, and 12.0 for `p > 400`.

## Symmetry at width 5

- The rotation action of `Z/5` is free, because a rotation-invariant cycle would need
  `a^3 - 2a - 1 = 0` with `a` positive rational, and the only positive root is the golden
  ratio. Hence `5 | T(N,5)`. VERIFIED (`no_pos_rat_root` for the no-constant-cycle step,
  `five_dvd_friezes5` for the divisibility itself).
- The cycles fixed by a reflection are exactly `(t(t+2), 1/t, t+1, t+1, 1/t)` for rational
  `t > 0`. Over `(1/N)Z` they correspond to integers `k` with `k^2 | N^3`, so their number
  is `5 Q(N)` with `Q(N) = prod over p^a || N of (floor(3a/2) + 1)`, OEIS A092520.
  VERIFIED (`palindromic_iff`, `lattice_criterion`, `Qp_eq_card`).
- `sum Q(N) N^-s = zeta(s)^2 zeta(2s) / zeta(3s)`, proved analysis-free as the Dirichlet
  convolution identity `Q * c = d * s`. VERIFIED
  (`Q_conv_cube_eq_sigma_conv_square`). The full count is not multiplicative:
  `T(2,5) T(3,5) = 800` while `T(6,5) = 110`.

## What is not new

The uniform bound is Cuntz-Holm Theorem 3.6. The glide symmetry of a frieze is classical.
The fold bijection for symmetric integer friezes (reflection-invariant triangulations of an
odd `n`-gon correspond to triangulations of an `((n+1)/2)`-gon) goes back to Cayley; it is
included only because it is the `N = 1` case of the symmetry count and fixes the
normalisation. The continuant parameterisation of section 2 may be known or implicit in the
literature; no claim of priority is made for it. A search did not find the arithmetic
criterion `N^{r-2} | C_{r-1}` over `(1/N)Z` in the literature, which is not the same as
establishing that it is new.

## Layout

    paper/rational_friezes.tex        the paper
    lean/VicoEnum/                    the Lean 4 library, 19 modules, sorry-free
    code/                             every script that generates a number in the paper
    data/                             the resulting sequences

## Reproduce

    python3 code/verify_width5_proved.py 40     # T(N,5), proved-complete
    python3 code/verify_width6_proved.py 20     # T(N,6), proved-complete
    python3 code/glide_criterion.py             # the criterion vs full array expansion
    python3 code/w6_sufficiency.py 6            # width-6 count over the Cuntz-Holm box
    python3 code/general_reduction.py           # the reduction at widths 5, 6, 7
    python3 code/t5_primes_split.py 200         # T(p,5) = A(p) + B(p) at primes
    rustc -O -o t5g code/t5_growth.rs && ./t5g 600    # T(N,5) growth

## Machine-checked

`lean/` builds against Mathlib v4.15.0. All 117 theorem and lemma declarations report
`[propext, Classical.choice, Quot.sound]` or a subset under `#print axioms`, and there is
no `sorry` and no `native_decide`.

    cd lean && lake exe cache get && lake build VicoEnum

Section 11 of the paper maps every numbered statement to its Lean declaration and records
which are PROVED rather than VERIFIED, and why.

## Open

1. The true order of `T(N,5)`. Both ends are open: the upper bound `O_eps(N^{1+eps})` is
   not attained on `N <= 600`, and the linear lower bound is false.
2. More terms of `T(N,8)` and `T(N,9)`. The criterion makes the enumeration effective and
   the sweep is complete over a proved box, but its cost grows steeply in `N`.
3. The order of `C(p)`, which is the problem of Conrey and Ford; the frieze count supplies
   a family of instances but says nothing about its size.

## Citing

See `CITATION.cff`.
