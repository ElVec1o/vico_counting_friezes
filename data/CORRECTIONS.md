# Corrections

An earlier private note circulated a table of counts under the heading "VERIFIED
SEQUENCES", with the qualifier "all values saturation-checked". Saturation is not
verification: a count that stops changing as a cutoff rises can still be missing
solutions, because the cutoff may never have reached them. This file records exactly
which of those values survive a proved search bound and which do not.

## What was wrong

`T(N,6)` was wrong for every `N >= 11`. Correct values, from an enumeration whose
search range is proved (`p*q <= 2N^2(N+1)`, `VicoEnum.width6_bound_nat`):

| N | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|
| proved | 1002 | 4961 | 918 | 3288 | 5214 | 4413 | 1242 | 7443 | 1356 | 9660 |
| circulated | 1000 | 4959 | 912 | 3274 | 5166 | 4371 | 1188 | 7383 | 1294 | 9524 |

Every circulated value is too small, and the deficit grows with `N`. That is the
signature of a search that never saturated.

Confirmed two independent ways: exhaustive brute force over `(p,q,r)` reproduces the
proved solution *sets*, not merely the counts, for `N = 2,3,4,5`; and the proved
solution sets are closed under the dihedral action on the quiddity cycle for
`N = 11..20`, which an incomplete set fails.

## What was right

- `T(N,4) = d(2N^2)`, and its identification with OEIS A361689.
- `T(N,5)` for `N = 1..40`, all forty values.
- `T(N,6)` for `N = 1..10`.
- The parameterization theorem and the monodromy identity, which the accompanying
  sympy script did check symbolically.

The pattern is exact: everything cross-checked against a second, independent
implementation is correct. Everything resting on saturation alone is where the
errors are. The circulated note said widths 4, 5 and 6 had been checked against a
separate enumeration "for N = 1..8", and that is precisely the range that holds up.

## What remains unverified

Widths `8` and `9` are no longer in this category. The values published in the paper are
swept over the entry box of Cuntz and Holm (J. Comb. Algebra 3 (2019), Theorem 3.6),
instantiated at `M = 1/N`, by `code/w89_count.rs`; that box is a proved bound, so those
counts are complete rather than saturated. All six were reproduced from a clean tree:
`T(N,8) = 132, 2576, 9980, 28604` and `T(N,9) = 429, 13101`, with `T(1,8) = C_6` and
`T(1,9) = C_7` as anchors.

The remaining width `>= 7` rows below were never cross-checked and were produced without a
proved search bound. They should be treated as conjectural:

    N=2, widths 7, 10, 11:  511, 67370, 350141
    N=3, widths 7, 9     :  1610, 62307
    N=4, width 7         :  3759
    N=5, width 7         :  3787
    N=6, width 7         :  11802

(The width-8 and width-9 entries that stood here are now covered by the proved box above.
`T(3,9) = 62307` is not: the paper tabulates width 9 only to `N = 2`.)

`T(2,7) = 511`, `T(3,7) = 1610` and `T(2,8) = 2576` are now corroborated. An independent width-7
enumerator built from the continuant parameterisation (`code/explore_width7.py`,
a different route entirely from the SL_2(Z)-orbit method that produced the
circulated table) reproduces all three, with `T(1,7) = 42 = C_5` and `T(1,8) = 132 = C_6` as anchors.
Those three values are therefore no longer conjectural in the way the rest are,
though the enumeration still lacks a fully proved search bound. The remaining
width >= 7 entries are uncorroborated.

## Standing rule

No count leaves this project without a proved search bound. Empirical saturation is
not evidence. It failed four times here: `N=3` at width 5 (35 for a true 40), `N=2`
at width 6 (60 for a true 102), the palindromic count at `n=15` (131 for a true 132,
which briefly cast doubt on a theorem that was true), and `T(N,6)` for `N >= 11`.
