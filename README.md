# Counting positive rational friezes over (1/N)Z

[![verify](https://github.com/ElVec1o/vico_counting_friezes/actions/workflows/verify.yml/badge.svg)](https://github.com/ElVec1o/vico_counting_friezes/actions/workflows/verify.yml)

Let `T(N,n)` be the number of positive rational frieze patterns of width `n` whose entries
all lie in `(1/N)Z`, in the sense of Karpenkov, Short, van Son and Zabolotskii
(arXiv:2601.21445, section 6). Conway and Coxeter give `T(1,n) = C_(n-2)`.

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
