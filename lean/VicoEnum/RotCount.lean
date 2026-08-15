/-
  VicoEnum/RotCount.lean

  Step 3 of `thm:orbit`: the `M = p` condition in the language of `W5` pairs, and the orbit
  count that follows.

  The paper writes `M_j = p p_{j+3} / g_j` with `g_j = gcd(p_j + p, p_{j+1} + p)`, so
  `M_j = p` exactly when `g_j = p_{j+3}`. Since `eq:w5cyc` gives `p_{j+3} = (p_j p_{j+1} - p^2)/p`,
  that condition on the pair `x = (p_j, p_{j+1})` is, division-free,

      gcd(x.1 + N, x.2 + N) * N = x.1 * x.2 - N^2,

  which is `IsMp` below. Checked against the quadruple's `M` for every `W5` pair at
  `N = 5, 7, 11, 13`: the two agree, and the only values `M` takes are `N` and `N^2`.

  `rotPair` is the rotation, free of order five on the `W5` pairs (`W5_rotPair`,
  `rotPair_five`, `rotPair_free`), so `orbit_count_one_exception` applies once the per-orbit
  count is known, and `orbit_split` supplies that count.

  `orbit_split` assumes a dichotomy `g j = q (j+3)` or `p g j = q (j+3)`. That is NOT an extra
  assumption here: `M_gcd_q3` gives `M g = N q3`, and `MarkovSet_M_cases` gives `M ∈ {N, N^2}`,
  so `dich_of_M` derives it. What remains is the indexing, carrying `orbit_split`'s conclusion
  about the five values of `j : ZMod 5` over to the five iterates of `rotOn`.
-/
import VicoEnum.Assemble
import VicoEnum.Orbit
import VicoEnum.PrimeOrbit
import VicoEnum.MSplit
import VicoEnum.IntCount
import VicoEnum.PaperDef

namespace VicoEnum

open Finset

/-- The `M = N` condition on a `W5` pair, division-free. -/
def IsMp (N : ℕ) (x : ℕ × ℕ) : Prop := Nat.gcd (x.1 + N) (x.2 + N) * N = x.1 * x.2 - N ^ 2

instance (N : ℕ) (x : ℕ × ℕ) : Decidable (IsMp N x) := by unfold IsMp; infer_instance

/-- The `W5` pairs as a `Finset`, which is what `T5` counts. -/
def W5box (N : ℕ) : Finset (ℕ × ℕ) := (box5 N).filter (fun x => W5 N x.1 x.2)

theorem W5box_card (N : ℕ) : (W5box N).card = T5 N := rfl

/-- The rotation maps the `W5` box to itself. -/
theorem rotPair_maps {N : ℕ} (hN : 0 < N) : ∀ x ∈ W5box N, rotPair N x ∈ W5box N := by
  intro x hx
  simp only [W5box, Finset.mem_filter] at hx ⊢
  have hw' := W5_rotPair hN hx.2
  exact ⟨by simpa using mem_box5_of_W5 hN hw', hw'⟩

/-- The rotation is free on the `W5` box. -/
theorem rotPair_free_box {N : ℕ} (hN : 0 < N) : ∀ x ∈ W5box N, rotPair N x ≠ x := by
  intro x hx
  simp only [W5box, Finset.mem_filter] at hx
  exact rotPair_free hN hx.2

/-- The rotation has order five on the `W5` box, in the form `orbit_count_one_exception`
wants: a globally defined map that is the identity off the box. -/
noncomputable def rotOn (N : ℕ) : ℕ × ℕ → ℕ × ℕ :=
  fun x => if W5 N x.1 x.2 then rotPair N x else x

theorem rotOn_ord {N : ℕ} (hN : 0 < N) (x : ℕ × ℕ) :
    rotOn N (rotOn N (rotOn N (rotOn N (rotOn N x)))) = x := by
  have hstep : ∀ y, W5 N y.1 y.2 → rotOn N y = rotPair N y := by
    intro y h; simp only [rotOn]; exact if_pos h
  by_cases h : W5 N x.1 x.2
  · have i1 := W5_rotPair hN h
    have i2 := W5_rotPair hN i1
    have i3 := W5_rotPair hN i2
    have i4 := W5_rotPair hN i3
    rw [hstep x h, hstep _ i1, hstep _ i2, hstep _ i3, hstep _ i4]
    exact rotPair_five hN h
  · have hid : rotOn N x = x := by simp only [rotOn]; exact if_neg h
    simp only [hid]

theorem rotOn_maps {N : ℕ} (hN : 0 < N) : ∀ x ∈ W5box N, rotOn N x ∈ W5box N := by
  intro x hx
  have hw : W5 N x.1 x.2 := (Finset.mem_filter.mp hx).2
  rw [show rotOn N x = rotPair N x from by simp only [rotOn]; exact if_pos hw]
  exact rotPair_maps hN x hx

theorem rotOn_free {N : ℕ} (hN : 0 < N) : ∀ x ∈ W5box N, rotOn N x ≠ x := by
  intro x hx
  have hw : W5 N x.1 x.2 := (Finset.mem_filter.mp hx).2
  rw [show rotOn N x = rotPair N x from by simp only [rotOn]; exact if_pos hw]
  exact rotPair_free_box hN x hx

/-! ## The orbit count

With the per-orbit split as a hypothesis, `orbit_count_one_exception` gives the identity
`thm:orbit` displays. The hypothesis is `orbit_split` restated for rotation orbits: every
orbit but the Conway--Coxeter one meets `IsMp` in exactly two points, and that one meets it in
five. -/

/-- **The orbit count of `thm:orbit`.** Given the per-orbit split, `5A = 2T + 15`. -/
theorem rot_orbit_count {N : ℕ} (hN : 0 < N) (e : ℕ × ℕ) (he : e ∈ W5box N)
    (hord : ∀ x ∈ W5box N \ orb (rotOn N) e, ((orb (rotOn N) x).filter (IsMp N)).card = 2)
    (hexc : ((orb (rotOn N) e).filter (IsMp N)).card = 5) :
    5 * ((W5box N).filter (IsMp N)).card = 2 * (T5 N - 5) + 25 := by
  have h := orbit_count_one_exception (rotOn_ord hN) (IsMp N) 2 5 (W5box N) e he
    (rotOn_maps hN) (rotOn_free hN) hord hexc
  rw [W5box_card] at h
  omega

/-! ## The bridge from `M` to the pair

The quadruple's `M` and the pair's gcd are tied by one identity: with `gu = x.1 + N` and
`gv = x.2 + N`,

    M g = (gu)(gv) - N(gu + gv) = x.1 x.2 - N^2,

so `M g + N^2 = x.1 x.2`. Since `rot3_fst` gives `q3 N + N^2 = x.1 x.2` as well, `M g = N q3`.
With `M ∈ {N, N^2}` from `MarkovSet_M_cases`, that is exactly the dichotomy `orbit_split`
assumes: `M = N` gives `g = q3`, which is `IsMp`, and `M = N^2` gives `q3 = N g`. -/

/-- **`M g + N^2 = x.1 x.2`.** -/
theorem M_gcd_identity {N x1 x2 g u v M : ℕ}
    (hgu : g * u = x1 + N) (hgv : g * v = x2 + N)
    (hM : M + N * (u + v) = g * u * v) :
    M * g + N ^ 2 = x1 * x2 := by
  have key : M * g + (N * (g * u) + N * (g * v)) = (g * u) * (g * v) := by
    have h : M * g + (N * (g * u) + N * (g * v)) = (M + N * (u + v)) * g := by ring
    rw [h, hM]; ring
  rw [hgu, hgv] at key
  nlinarith [key]

/-- **`M g = N q3`.** The pair's `q3` and the quadruple's `M` determine each other. -/
theorem M_gcd_q3 {N x1 x2 g u v M q3 : ℕ}
    (hgu : g * u = x1 + N) (hgv : g * v = x2 + N)
    (hM : M + N * (u + v) = g * u * v) (hq3 : q3 * N + N ^ 2 = x1 * x2) :
    M * g = N * q3 := by
  have h := M_gcd_identity hgu hgv hM
  have hc : q3 * N = N * q3 := by ring
  omega

/-- **The dichotomy, from `M ∈ {N, N^2}`.** This is `orbit_split`'s `hdich`, which is
therefore not an open hypothesis: it follows from `MarkovSet_M_cases`. -/
theorem dich_of_M {N g q3 M : ℕ} (hN : 0 < N) (hg : 0 < g)
    (hMg : M * g = N * q3) (hcase : M = N ∨ M = N ^ 2) :
    g = q3 ∨ N * g = q3 := by
  rcases hcase with rfl | rfl
  · left
    exact Nat.eq_of_mul_eq_mul_left hN hMg
  · right
    have : N * (N * g) = N * q3 := by rw [← hMg]; ring
    exact Nat.eq_of_mul_eq_mul_left hN this

/-! ## Assembling `orbit_split`

`orbit_split` is stated for `q g : ZMod 5 → ℤ`. The quiddity is read off the orbit by
`q j = (orbIdx (rotOn N) x j).1`, and the pair at step `j` is `(q j, q (j+1))` because the
rotation shifts: `(rotOn N x).1 = x.2`. -/

/-- The rotation shifts the pair: the second coordinate becomes the first. -/
theorem rotOn_fst {N : ℕ} {x : ℕ × ℕ} (hw : W5 N x.1 x.2) : (rotOn N x).1 = x.2 := by
  simp only [rotOn, if_pos hw, rotPair]

/-- Every iterate of a `W5` pair is a `W5` pair. -/
theorem rotOn_iterate_W5 {N : ℕ} (hN : 0 < N) {x : ℕ × ℕ} (hw : W5 N x.1 x.2) :
    ∀ k, W5 N ((rotOn N)^[k] x).1 ((rotOn N)^[k] x).2 := by
  intro k
  induction k with
  | zero => exact hw
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rw [show rotOn N ((rotOn N)^[m] x) = rotPair N ((rotOn N)^[m] x) from by
      simp only [rotOn]; exact if_pos ih]
    exact W5_rotPair hN ih

/-- The quiddity read off the orbit. -/
noncomputable def qOn (N : ℕ) (x : ℕ × ℕ) (j : ZMod 5) : ℕ := (orbIdx (rotOn N) x j).1

/-- **The pair at step `j` is `(q j, q (j+1))`.** The wraparound at `j = 4` uses order five:
the fifth iterate returns, so its first coordinate is `x.1`. -/
theorem qOn_succ {N : ℕ} (hN : 0 < N) {x : ℕ × ℕ} (hw : W5 N x.1 x.2) (j : ZMod 5) :
    (orbIdx (rotOn N) x j).2 = qOn N x (j + 1) := by
  have step : ∀ k, ((rotOn N)^[k] x).2 = ((rotOn N)^[k + 1] x).1 := by
    intro k
    rw [Function.iterate_succ_apply']
    exact (rotOn_fst (rotOn_iterate_W5 hN hw k)).symm
  have h5 : (rotOn N)^[5] x = x := by
    show rotOn N (rotOn N (rotOn N (rotOn N (rotOn N x)))) = x
    exact rotOn_ord hN x
  fin_cases j <;> simp only [qOn, orbIdx, ZMod.val] <;>
    [exact step 0; exact step 1; exact step 2; exact step 3;
     · rw [step 4, h5]; rfl]

/-- **`eq:w5cyc` on the orbit.** `q 3 * N + N^2 = x.1 x.2`. -/
theorem rot3_orbit {N : ℕ} (hN : 0 < N) {x : ℕ × ℕ} (hw : W5 N x.1 x.2) :
    qOn N x 3 * N + N ^ 2 = x.1 * x.2 := by
  have hlt : N ^ 2 < x.1 * x.2 := hw.2.2.1
  obtain ⟨e, he⟩ : ∃ e, x.1 * x.2 = N ^ 2 + e := ⟨x.1 * x.2 - N ^ 2, by omega⟩
  have hepos : 0 < e := by omega
  have h2 : (rotPair N x).2 * e = N ^ 2 * (x.1 + N) := by
    have h := rotPair_step hw
    simp only [RotStep] at h
    rwa [show x.1 * x.2 - N ^ 2 = e from by omega] at h
  have hw1 : W5 N (rotPair N x).1 (rotPair N x).2 := W5_rotPair hN hw
  have h3 : RotStep N x.2 (rotPair N x).2 (rotPair N (rotPair N x)).2 := by
    have h := rotPair_step hw1
    simpa [rotPair] using h
  have hq3 : qOn N x 3 = (rotPair N (rotPair N x)).2 := by
    have e1 : (rotOn N)^[3] x = rotPair N (rotPair N (rotPair N x)) := by
      have s0 : rotOn N x = rotPair N x := by simp only [rotOn]; exact if_pos hw
      have s1 : rotOn N (rotPair N x) = rotPair N (rotPair N x) := by
        simp only [rotOn]; exact if_pos hw1
      have s2 : rotOn N (rotPair N (rotPair N x))
          = rotPair N (rotPair N (rotPair N x)) := by
        simp only [rotOn]; exact if_pos (W5_rotPair hN hw1)
      show rotOn N (rotOn N (rotOn N x)) = _
      rw [s0, s1, s2]
    simp only [qOn, orbIdx, show (3 : ZMod 5).val = 3 from rfl]
    rw [show (rotOn N)^[3] x = rotPair N (rotPair N (rotPair N x)) from e1]
    simp [rotPair]
  rw [hq3, rot3_fst hN he hepos h2 h3, he]; ring

/-- Iterating the rotation depends only on the exponent mod five. -/
theorem rotOn_iterate_mod {N : ℕ} (hN : 0 < N) (x : ℕ × ℕ) (m : ℕ) :
    (rotOn N)^[m] x = (rotOn N)^[m % 5] x := by
  have h5 : ∀ y, (rotOn N)^[5] y = y := by
    intro y
    show rotOn N (rotOn N (rotOn N (rotOn N (rotOn N y)))) = y
    exact rotOn_ord hN y
  have hmul : ∀ c y, (rotOn N)^[5 * c] y = y := by
    intro c
    induction c with
    | zero => intro y; rfl
    | succ d ih =>
      intro y
      rw [show 5 * (d + 1) = 5 * d + 5 from by ring, Function.iterate_add_apply, h5, ih]
  conv_lhs => rw [show m = 5 * (m / 5) + m % 5 from by omega]
  rw [Function.iterate_add_apply, hmul]

/-- The quiddity of a rotated pair is the quiddity shifted. -/
theorem qOn_orbIdx {N : ℕ} (hN : 0 < N) (x : ℕ × ℕ) (j k : ZMod 5) :
    qOn N (orbIdx (rotOn N) x j) k = qOn N x (j + k) := by
  simp only [qOn, orbIdx]
  rw [← Function.iterate_add_apply]
  rw [rotOn_iterate_mod hN x (k.val + j.val), rotOn_iterate_mod hN x (j + k).val]
  congr 2
  have : (j + k).val = (j.val + k.val) % 5 := by
    simp [ZMod.val_add]
  omega

/-- **`eq:w5cyc` along the orbit.** -/
theorem qOn_rel {N : ℕ} (hN : 0 < N) {x : ℕ × ℕ} (hw : W5 N x.1 x.2) (j : ZMod 5) :
    qOn N x j * qOn N x (j + 1) = N * (qOn N x (j + 3) + N) := by
  have hWj : W5 N (orbIdx (rotOn N) x j).1 (orbIdx (rotOn N) x j).2 := by
    simpa [orbIdx] using rotOn_iterate_W5 hN hw j.val
  have h3 := rot3_orbit hN hWj
  rw [qOn_orbIdx hN x j 3] at h3
  have hfst : (orbIdx (rotOn N) x j).1 = qOn N x j := rfl
  have hsnd : (orbIdx (rotOn N) x j).2 = qOn N x (j + 1) := qOn_succ hN hw j
  rw [hfst, hsnd] at h3
  rw [Nat.mul_add, ← h3]; ring

/-- Every entry along the orbit is positive. -/
theorem qOn_pos {N : ℕ} (hN : 0 < N) {x : ℕ × ℕ} (hw : W5 N x.1 x.2) (j : ZMod 5) :
    0 < qOn N x j :=
  (rotOn_iterate_W5 hN hw j.val).1

/-- **`IsMp` at step `j` says `g j = q (j+3)`.** -/
theorem isMp_iff {N : ℕ} (hN : 0 < N) {x : ℕ × ℕ} (hw : W5 N x.1 x.2) (j : ZMod 5) :
    IsMp N (orbIdx (rotOn N) x j)
      ↔ Nat.gcd (qOn N x j + N) (qOn N x (j + 1) + N) = qOn N x (j + 3) := by
  have hWj : W5 N (orbIdx (rotOn N) x j).1 (orbIdx (rotOn N) x j).2 := by
    simpa [orbIdx] using rotOn_iterate_W5 hN hw j.val
  have h3 := rot3_orbit hN hWj
  rw [qOn_orbIdx hN x j 3] at h3
  have hfst : (orbIdx (rotOn N) x j).1 = qOn N x j := rfl
  have hsnd : (orbIdx (rotOn N) x j).2 = qOn N x (j + 1) := qOn_succ hN hw j
  rw [hfst, hsnd] at h3
  have hsub : qOn N x j * qOn N x (j + 1) - N ^ 2 = qOn N x (j + 3) * N := by omega
  simp only [IsMp, hfst, hsnd, hsub]
  exact Nat.mul_left_inj hN.ne'

/-- **The exceptional orbit is the Conway--Coxeter one.** If every entry along the orbit is
divisible by `N`, the pair lies in the orbit of `(3N, N)`. This is `orbit_split`'s `hnotall`,
discharged. -/
theorem notall_of_not_orb {N : ℕ} (hN : N.Prime) {x : ℕ × ℕ} (hw : W5 N x.1 x.2)
    (hx : x ∉ orb (rotOn N) (3 * N, N)) :
    (Finset.univ.filter (fun j : ZMod 5 => N ∣ qOn N x j)).card ≠ 5 := by
  classical
  have hN0 : 0 < N := hN.pos
  intro hc
  set P : ZMod 5 → ℤ := fun j => (qOn N x j : ℤ) with hP
  have hpZ : Prime ((N : ℤ)) := Nat.prime_iff_prime_int.mp hN
  have hpos : ∀ j, 0 < P j := fun j => by
    simp only [hP]; exact_mod_cast qOn_pos hN0 hw j
  have hrel : ∀ j, P j * P (j + 1) = (N : ℤ) * (P (j + 3) + (N : ℤ)) := fun j => by
    simp only [hP]; exact_mod_cast qOn_rel hN0 hw j
  have hc5 : (divSet N P).card = 5 := by
    simpa [divSet, hP, Int.natCast_dvd_natCast] using hc
  have hfive : ∃ (k : ZMod 5) (a : ZMod 5 → ℕ), (∀ j, P j = (N : ℤ) * a j) ∧
      a k = 3 ∧ a (k + 1) = 1 ∧ a (k + 2) = 2 ∧ a (k + 3) = 2 ∧ a (k + 4) = 1 :=
    intcount_five hN hpos hrel hc5
  obtain ⟨k, a, hval, hk0, hk1, -, -, -⟩ := hfive
  have e1 : qOn N x k = 3 * N := by
    have h := hval k; rw [hk0] at h; simp only [hP] at h
    have : ((qOn N x k : ℕ) : ℤ) = ((3 * N : ℕ) : ℤ) := by push_cast; push_cast at h; linarith
    exact_mod_cast this
  have e2 : qOn N x (k + 1) = N := by
    have h := hval (k + 1); rw [hk1] at h; simp only [hP] at h
    have : ((qOn N x (k + 1) : ℕ) : ℤ) = ((N : ℕ) : ℤ) := by push_cast; push_cast at h; linarith
    exact_mod_cast this
  have hidx : orbIdx (rotOn N) x k = (3 * N, N) := by
    have hfst : (orbIdx (rotOn N) x k).1 = qOn N x k := rfl
    have hsnd : (orbIdx (rotOn N) x k).2 = qOn N x (k + 1) := qOn_succ hN0 hw k
    exact Prod.ext (by rw [hfst, e1]) (by rw [hsnd, e2])
  exact hx (orb_symm (rotOn_ord hN0) (hidx ▸ orbIdx_mem_orb (rotOn N) x k))

/-- Abbreviation for the gcd appearing as `g` along the orbit. -/
noncomputable def gOn (N : ℕ) (x : ℕ × ℕ) (j : ZMod 5) : ℕ :=
  Nat.gcd (qOn N x j + N) (qOn N x (j + 1) + N)

/-- **The dichotomy at a single `W5` pair.** The gcd is either `q3` or `q3/N`, according to
`M = N` or `M = N^2`. This is `orbit_split`'s `hdich`, discharged. -/
theorem dich_pair {N : ℕ} (hN : N.Prime) {y : ℕ × ℕ} (hw : W5 N y.1 y.2)
    {q3 : ℕ} (hq3 : q3 * N + N ^ 2 = y.1 * y.2) :
    Nat.gcd (y.1 + N) (y.2 + N) = q3 ∨ N * Nat.gcd (y.1 + N) (y.2 + N) = q3 := by
  have hN0 : 0 < N := hN.pos
  obtain ⟨z, hz, hzy⟩ := mkv_surjOn hN0 (show y ∈ W5Set N from hw)
  obtain ⟨hMrel, hMdvd, hNdvd, hcop, hlt1, hlt2⟩ := hz
  have hy1 : y.1 = z.1 * z.2.1 - N := by rw [← hzy]; rfl
  have hy2 : y.2 = z.1 * z.2.2.1 - N := by rw [← hzy]; rfl
  have hgu : z.1 * z.2.1 = y.1 + N := by omega
  have hgv : z.1 * z.2.2.1 = y.2 + N := by omega
  have hgpos : 0 < z.1 := by
    rcases Nat.eq_zero_or_pos z.1 with h | h
    · exfalso; rw [h] at hlt1; simp at hlt1
    · exact h
  have hgcd : Nat.gcd (y.1 + N) (y.2 + N) = z.1 := by
    rw [← hgu, ← hgv, Nat.gcd_mul_left, hcop, Nat.mul_one]
  have hM : z.2.2.2 + N * (z.2.1 + z.2.2.1) = z.1 * z.2.1 * z.2.2.1 := by omega
  have hMg : z.2.2.2 * z.1 = N * q3 := M_gcd_q3 hgu hgv hM hq3
  rw [hgcd]
  exact dich_of_M hN0 hgpos hMg
    (MarkovSet_M_cases hN ⟨hMrel, hMdvd, hNdvd, hcop, hlt1, hlt2⟩)

/-- **The per-orbit count, from `orbit_split`.** A non-fixed `W5` orbit over a prime `N`
that is not the all-integral one has exactly two positions with `M = N`. -/
theorem orb_IsMp_card {N : ℕ} (hN : N.Prime) {x : ℕ × ℕ} (hw : W5 N x.1 x.2)
    (hfix : rotOn N x ≠ x) (hnotall : x ∉ orb (rotOn N) (3 * N, N)) :
    ((orb (rotOn N) x).filter (IsMp N)).card = 2 := by
  classical
  have hN0 : 0 < N := hN.pos
  have hdich : ∀ j : ZMod 5,
      gOn N x j = qOn N x (j + 3) ∨ N * gOn N x j = qOn N x (j + 3) := by
    intro j
    have hWj : W5 N (orbIdx (rotOn N) x j).1 (orbIdx (rotOn N) x j).2 := by
      simpa [orbIdx] using rotOn_iterate_W5 hN0 hw j.val
    have h3 := rot3_orbit hN0 hWj
    rw [qOn_orbIdx hN0 x j 3] at h3
    have hfst : (orbIdx (rotOn N) x j).1 = qOn N x j := rfl
    have hsnd : (orbIdx (rotOn N) x j).2 = qOn N x (j + 1) := qOn_succ hN0 hw j
    have := dich_pair hN hWj h3
    rw [hfst, hsnd] at this
    simpa [gOn] using this
  set q : ZMod 5 → ℤ := fun j => (qOn N x j : ℤ) with hq
  set g : ZMod 5 → ℤ := fun j => (gOn N x j : ℤ) with hg
  have hpZ : Prime ((N : ℤ)) := Nat.prime_iff_prime_int.mp hN
  have hpos : ∀ j, 0 < q j := fun j => by
    simp only [hq]; exact_mod_cast qOn_pos hN0 hw j
  have hrel : ∀ j, q j * q (j + 1) = (N : ℤ) * (q (j + 3) + (N : ℤ)) := fun j => by
    simp only [hq]; exact_mod_cast qOn_rel hN0 hw j
  have hgl : ∀ j, g j ∣ q j + (N : ℤ) := fun j => by
    simp only [hq, hg, gOn]
    exact_mod_cast Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have hgr : ∀ j, g j ∣ q (j + 1) + (N : ℤ) := fun j => by
    simp only [hq, hg, gOn]
    exact_mod_cast Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
  have hdichZ : ∀ j, g j = q (j + 3) ∨ (N : ℤ) * g j = q (j + 3) := fun j =>
    (hdich j).imp (fun h => by simp only [hq, hg]; exact_mod_cast h)
      (fun h => by simp only [hq, hg]; exact_mod_cast h)
  have hnotallZ : (Finset.univ.filter (fun j : ZMod 5 => (N : ℤ) ∣ q j)).card ≠ 5 := by
    simpa [hq, Int.natCast_dvd_natCast] using notall_of_not_orb hN hw hnotall
  have hsplit := orbit_split hpZ q g hpos hrel hgl hgr hdichZ hnotallZ
  rw [orb_filter_card (rotOn_ord hN0) hfix, ← hsplit]
  congr 1
  apply Finset.filter_congr
  intro j _
  rw [isMp_iff hN0 hw j]
  simp only [hq, hg, gOn]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩


/-! ## The exceptional orbit

The Conway--Coxeter cycle `(3,1,2,2,1)` scaled by `N`. Its five pairs all have `M = N`,
which is what makes it the one orbit contributing five rather than two.
-/

/-- A pair of the form `(aN, bN)` is a `W5` pair when `ab > 1` and `ab-1` divides both
`a+1` and `b+1`. -/
theorem W5_scaled {N a b : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) (hab : 1 < a * b)
    (h1 : (a * b - 1) ∣ (a + 1)) (h2 : (a * b - 1) ∣ (b + 1)) : W5 N (a * N) (b * N) := by
  have hprod : a * N * (b * N) = a * b * N ^ 2 := by ring
  have hsub : a * N * (b * N) - N ^ 2 = N ^ 2 * (a * b - 1) := by
    rw [hprod, Nat.mul_sub, Nat.mul_one]; ring_nf
  refine ⟨Nat.mul_pos ha hN, Nat.mul_pos hb hN, ?_, ⟨a * b * N, by rw [hprod]; ring⟩, ?_, ?_⟩
  · rw [hprod]; nlinarith [hN, Nat.one_le_iff_ne_zero.mpr hN.ne']
  · obtain ⟨k, hk⟩ := h1
    exact hsub ▸ ⟨N * k, by rw [show a * N + N = N * (a + 1) from by ring, hk]; ring⟩
  · obtain ⟨k, hk⟩ := h2
    exact hsub ▸ ⟨N * k, by rw [show b * N + N = N * (b + 1) from by ring, hk]; ring⟩

/-- The rotation in scaled form: `(aN, bN) ↦ (bN, cN)` when `c(ab-1) = a+1`. -/
theorem rotPair_scaled {N a b c : ℕ} (hN : 0 < N) (hab : 1 < a * b)
    (hc : c * (a * b - 1) = a + 1) :
    rotPair N (a * N, b * N) = (b * N, c * N) := by
  have hsub : a * N * (b * N) - N ^ 2 = N ^ 2 * (a * b - 1) := by
    rw [show a * N * (b * N) = a * b * N ^ 2 from by ring, Nat.mul_sub, Nat.mul_one]; ring_nf
  have hpos : 0 < N ^ 2 * (a * b - 1) := Nat.mul_pos (Nat.pos_pow_of_pos 2 hN) (by omega)
  simp only [rotPair, hsub]
  refine Prod.ext rfl ?_
  show N ^ 2 * (a * N + N) / (N ^ 2 * (a * b - 1)) = c * N
  rw [show N ^ 2 * (a * N + N) = (N ^ 2 * (a * b - 1)) * (c * N) from by
    rw [show a * N + N = (a + 1) * N from by ring, ← hc]; ring]
  exact Nat.mul_div_cancel_left _ hpos

/-- The exceptional orbit, computed. -/
theorem exc_orb {N : ℕ} (hN : 0 < N) :
    orb (rotOn N) (3 * N, N)
      = {(3 * N, N), (N, 2 * N), (2 * N, 2 * N), (2 * N, N), (N, 3 * N)} := by
  have step : ∀ a b c : ℕ, 0 < a → 0 < b → 1 < a * b → (a * b - 1) ∣ (a + 1) →
      (a * b - 1) ∣ (b + 1) → c * (a * b - 1) = a + 1 →
      rotOn N (a * N, b * N) = (b * N, c * N) := by
    intro a b c ha hb hab h1 h2 hc
    have hw := W5_scaled hN ha hb hab h1 h2
    rw [show rotOn N (a * N, b * N) = rotPair N (a * N, b * N) from by
      simp only [rotOn]; exact if_pos hw]
    exact rotPair_scaled hN hab hc
  have s1 : rotOn N (3 * N, N) = (N, 2 * N) := by
    simpa using step 3 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have s2 : rotOn N (N, 2 * N) = (2 * N, 2 * N) := by
    simpa using step 1 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have s3 : rotOn N (2 * N, 2 * N) = (2 * N, N) := by
    simpa using step 2 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have s4 : rotOn N (2 * N, N) = (N, 3 * N) := by
    simpa using step 2 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  simp only [orb, s1, s2, s3, s4]

/-- The exceptional pair is in the box. -/
theorem exc_mem {N : ℕ} (hN : 0 < N) : (3 * N, N) ∈ W5box N := by
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · simp only [box5, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ⟨by omega, by nlinarith⟩⟩
    nlinarith
  simpa using W5_scaled hN (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a := 3) (b := 1)

/-- **All five positions of the exceptional orbit have `M = N`.** -/
theorem exc_filter {N : ℕ} (hN : 0 < N) (hfix : rotOn N (3 * N, N) ≠ (3 * N, N)) :
    ((orb (rotOn N) (3 * N, N)).filter (IsMp N)).card = 5 := by
  have hall : ∀ y ∈ orb (rotOn N) (3 * N, N), IsMp N y := by
    intro y hy
    rw [exc_orb hN] at hy
    have hg : ∀ u v : ℕ, Nat.gcd (u * N) (v * N) = Nat.gcd u v * N := fun u v =>
      Nat.gcd_mul_right u N v
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [IsMp]
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · rw [show 3 * N + N = 4 * N from by ring, show N + N = 2 * N from by ring, hg]
      norm_num
      rw [show 3 * N * N = 2 * N * N + N ^ 2 from by ring, Nat.add_sub_cancel]
    · rw [show N + N = 2 * N from by ring, show 2 * N + N = 3 * N from by ring, hg]
      norm_num
      rw [show N * (2 * N) = N * N + N ^ 2 from by ring, Nat.add_sub_cancel]
    · rw [show 2 * N + N = 3 * N from by ring, hg]
      norm_num
      rw [show 2 * N * (2 * N) = 3 * N * N + N ^ 2 from by ring, Nat.add_sub_cancel]
    · rw [show 2 * N + N = 3 * N from by ring, show N + N = 2 * N from by ring, hg]
      norm_num
      rw [show 2 * N * N = N * N + N ^ 2 from by ring, Nat.add_sub_cancel]
    · rw [show N + N = 2 * N from by ring, show 3 * N + N = 4 * N from by ring, hg]
      norm_num
      rw [show N * (3 * N) = 2 * N * N + N ^ 2 from by ring, Nat.add_sub_cancel]
  rw [Finset.filter_true_of_mem hall, card_orb (rotOn_ord hN) hfix]

/-- **The `M = N` count over the whole box.** Every non-exceptional orbit contributes two,
the exceptional one contributes five, and there are `(T5 N - 5)/5` of the former. -/
theorem W5box_IsMp_count {N : ℕ} (hN : N.Prime) :
    5 * ((W5box N).filter (IsMp N)).card = 2 * (T5 N - 5) + 25 := by
  have hN0 : 0 < N := hN.pos
  have he : (3 * N, N) ∈ W5box N := exc_mem hN0
  refine rot_orbit_count hN0 (3 * N, N) he ?_ (exc_filter hN0 (rotOn_free hN0 _ he))
  intro x hx
  rw [Finset.mem_sdiff] at hx
  exact orb_IsMp_card hN (Finset.mem_filter.mp hx.1).2 (rotOn_free hN0 x hx.1) hx.2

/-! ## The `M = N` pairs are `ASet` -/

/-- **`M = N` is `IsMp` on the pair.** Under `mkv`, the quadruple's `M` equals `N` exactly
when the pair satisfies `IsMp`. -/
theorem isMp_iff_M {N : ℕ} (hN : 0 < N) {z : ℕ × ℕ × ℕ × ℕ} (hz : z ∈ MarkovSet N) :
    IsMp N (mkv N z) ↔ z.2.2.2 = N := by
  obtain ⟨hMrel, hMdvd, hNdvd, hcop, hlt1, hlt2⟩ := hz
  have hy1 : (mkv N z).1 = z.1 * z.2.1 - N := rfl
  have hy2 : (mkv N z).2 = z.1 * z.2.2.1 - N := rfl
  have hgu : z.1 * z.2.1 = (mkv N z).1 + N := by omega
  have hgv : z.1 * z.2.2.1 = (mkv N z).2 + N := by omega
  have hgpos : 0 < z.1 := by
    rcases Nat.eq_zero_or_pos z.1 with h | h
    · exfalso; rw [h] at hlt1; simp at hlt1
    · exact h
  have hgcd : Nat.gcd ((mkv N z).1 + N) ((mkv N z).2 + N) = z.1 := by
    rw [← hgu, ← hgv, Nat.gcd_mul_left, hcop, Nat.mul_one]
  have hM : z.2.2.2 + N * (z.2.1 + z.2.2.1) = z.1 * z.2.1 * z.2.2.1 := by omega
  have hid := M_gcd_identity hgu hgv hM
  have hc : z.1 * N = N * z.1 := by ring
  simp only [IsMp, hgcd]
  constructor
  · intro h
    have hmm : z.2.2.2 * z.1 = N * z.1 := by omega
    exact Nat.eq_of_mul_eq_mul_right hgpos hmm
  · intro h; rw [h] at hid; omega

/-- **The `M = N` pairs of the box are exactly `ASet N`.** -/
theorem IsMp_card_eq_ASet {N : ℕ} (hN : N.Prime) (h5 : 5 ≤ N) :
    ((W5box N).filter (IsMp N)).card = (ASet N).card := by
  have hN0 : 0 < N := hN.pos
  have hbox : (W5Set N) = ↑(W5box N) := W5_setOf_eq_box N hN0
  have himg : (↑((W5box N).filter (IsMp N)) : Set (ℕ × ℕ)) = mkv N '' (MarkovAt N N) := by
    ext x
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hxb, hxm⟩
      obtain ⟨z, hz, rfl⟩ := mkv_surjOn hN0 (show x ∈ W5Set N from by rw [hbox]; exact hxb)
      exact ⟨z, ⟨hz, (isMp_iff_M hN0 hz).mp hxm⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hM⟩, rfl⟩
      refine ⟨?_, (isMp_iff_M hN0 hz).mpr hM⟩
      have := mkv_mapsTo hN0 hz
      rw [hbox] at this
      exact this
  have hinj : Set.InjOn (mkv N) (MarkovAt N N) :=
    (mkv_injOn (N := N)).mono (fun z hz => hz.1)
  rw [← MarkovAt_p_ncard hN h5, ← Set.ncard_coe_Finset, himg,
    Set.ncard_image_of_injOn hinj]

/-! ## The main count -/

/-- The exceptional orbit sits inside the box, so the box has at least five elements. -/
theorem five_le_T5 {N : ℕ} (hN : 0 < N) : 5 ≤ T5 N := by
  rw [← W5box_card]
  calc 5 = (orb (rotOn N) (3 * N, N)).card :=
        (card_orb (rotOn_ord hN) (rotOn_free hN _ (exc_mem hN))).symm
    _ ≤ (W5box N).card :=
        Finset.card_le_card (orb_subset (rotOn_maps hN) (exc_mem hN))

/-- **The main theorem.** For a prime `p ≥ 5`, the number of positive rational frieze
patterns of width five over `(1/p)ℤ` is `5 + 5 C(p)`, where `C(p)` counts the triples
`(a, u, v)` with `a u v = p + u + v`. -/
theorem T5_eq_five_add_five_mul {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    T5 p = 5 + 5 * (cubicTriples p).card := by
  have hcount := W5box_IsMp_count hp
  rw [IsMp_card_eq_ASet hp h5, acount_eq hp h5] at hcount
  have hge := five_le_T5 hp.pos
  omega

/-- **The main theorem, over the paper's own definition of a frieze.** Composing with
`paper_count`, which identifies `T5` with the count of width-5 friezes satisfying
Definition `def:frieze` over `(1/p)ℤ`, with periodicity derived and not assumed. -/
theorem paper_frieze5_count {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    {F | PaperFrieze5 p F}.ncard = 5 + 5 * (cubicTriples p).card := by
  rw [paper_count hp.pos, T5_eq_five_add_five_mul hp h5]

end VicoEnum
