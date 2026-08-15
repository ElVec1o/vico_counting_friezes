/-
  VicoEnum/Frieze.lean

  Positive rational friezes of arbitrary width, and the continuant parameterisation.

  Everything else in this development works with the arithmetic predicates that the
  reduction produces (`W5`, `W6`, and the cubic). Those predicates are tied to friezes by
  Proposition `prop:param`, which until now was the one unformalised link in every count.
  This file supplies the missing definition and proves the link.

  A frieze is recorded as `m : ℕ → ℤ → ℚ`, the entry `m r j` sitting in row `r` and column
  `j`, with rows `0` and `n` vanishing, rows `1` and `n-1` constant `1`, and the diamond
  rule in the cleared form

      m (r-2) (j+1) * m r j = m (r-1) j * m (r-1) (j+1) - 1.

  Columns are indexed by `ℤ` with periodicity `n` imposed separately, which keeps the
  continuant recursion free of modular casts.

  The main theorem is `entry_eq_continuant`: every entry is the continuant of the quiddity
  window beginning at its column,

      m r j = K_{r-1}(a_j, …, a_{j+r-2}),      a_j = m 2 j,

  from which the three closing identities of Proposition `prop:param` follow by reading the
  conditions on rows `n-1` and `n`.
-/
import VicoEnum.GeneralWidth
import VicoEnum.Count

namespace VicoEnum

/-! ## Friezes -/

/-- A rational frieze of width `n`, in the cleared form of the diamond rule. -/
structure IsFrieze (n : ℕ) (m : ℕ → ℤ → ℚ) : Prop where
  /-- the array is `n`-periodic along each row -/
  periodic : ∀ r j, m r (j + n) = m r j
  /-- row `0` vanishes -/
  row_zero : ∀ j, m 0 j = 0
  /-- row `1` is constant `1` -/
  row_one : ∀ j, m 1 j = 1
  /-- row `n-1` is constant `1` -/
  row_top_one : ∀ j, m (n - 1) j = 1
  /-- row `n` vanishes -/
  row_top_zero : ∀ j, m n j = 0
  /-- the diamond rule, cleared of denominators -/
  diamond : ∀ r j, 2 ≤ r → r ≤ n →
    m (r - 2) (j + 1) * m r j = m (r - 1) j * m (r - 1) (j + 1) - 1

/-- The frieze is positive if every interior entry is. -/
def IsPositiveFrieze (n : ℕ) (m : ℕ → ℤ → ℚ) : Prop :=
  IsFrieze n m ∧ ∀ r j, 0 < r → r < n → 0 < m r j

/-- The quiddity cycle: row `2`. -/
def quiddity (m : ℕ → ℤ → ℚ) (j : ℤ) : ℚ := m 2 j

/-! ## Continuants

`Kc a j k` is `K_k(a_j, …, a_{j+k-1})`, the continuant of the length-`k` window of `a`
beginning at `j`, with `K_0 = 1` and `K_k = a_{j+k-1}K_{k-1} - K_{k-2}`. -/

/-- The frieze continuant of the window of length `k` starting at column `j`. -/
def Kc (a : ℤ → ℚ) (j : ℤ) : ℕ → ℚ
  | 0 => 1
  | 1 => a j
  | (k + 2) => a (j + k + 1) * Kc a j (k + 1) - Kc a j k

@[simp] theorem Kc_zero (a : ℤ → ℚ) (j : ℤ) : Kc a j 0 = 1 := rfl
@[simp] theorem Kc_one (a : ℤ → ℚ) (j : ℤ) : Kc a j 1 = a j := rfl

theorem Kc_succ_succ (a : ℤ → ℚ) (j : ℤ) (k : ℕ) :
    Kc a j (k + 2) = a (j + k + 1) * Kc a j (k + 1) - Kc a j k := rfl

/-- **The continuant identity.** Two adjacent windows of the same length differ by exactly
`-1` in the Desnanot--Jacobi combination. This is Lemma `lem:dj` at `N = 1`, and it is what
makes the diamond rule and the continuant recursion the same statement. -/
theorem Kc_identity (a : ℤ → ℚ) (j : ℤ) (k : ℕ) :
    Kc a j (k + 2) * Kc a (j + 1) k - Kc a j (k + 1) * Kc a (j + 1) (k + 1) = -1 := by
  induction k with
  | zero =>
    have h2 : Kc a j 2 = a (j + 1) * a j - 1 := by
      rw [Kc_succ_succ a j 0]; norm_num
    show Kc a j 2 * Kc a (j + 1) 0 - Kc a j 1 * Kc a (j + 1) 1 = -1
    rw [h2, Kc_zero, Kc_one, Kc_one]
    ring
  | succ p ih =>
    have e1 : Kc a j (p + 3) = a (j + p + 2) * Kc a j (p + 2) - Kc a j (p + 1) := by
      have := Kc_succ_succ a j (p + 1)
      rw [this]; push_cast; ring_nf
    have e2 : Kc a (j + 1) (p + 2) = a (j + p + 2) * Kc a (j + 1) (p + 1) - Kc a (j + 1) p := by
      have := Kc_succ_succ a (j + 1) p
      rw [this]; push_cast; ring_nf
    calc Kc a j (p + 1 + 2) * Kc a (j + 1) (p + 1)
          - Kc a j (p + 1 + 1) * Kc a (j + 1) (p + 1 + 1)
        = Kc a j (p + 3) * Kc a (j + 1) (p + 1) - Kc a j (p + 2) * Kc a (j + 1) (p + 2) := by
          norm_num
      _ = Kc a j (p + 2) * Kc a (j + 1) p - Kc a j (p + 1) * Kc a (j + 1) (p + 1) := by
          rw [e1, e2]; ring
      _ = -1 := ih

/-! ## The parameterisation -/

/-- **Every entry is a continuant of the quiddity.** For `1 ≤ r ≤ n`,
`m r j = K_{r-1}(a_j, …, a_{j+r-2})` with `a = quiddity m`. This is the statement that
Proposition `prop:param` asserts and that every count in the paper passes through. -/
theorem entry_eq_continuant {n : ℕ} {m : ℕ → ℤ → ℚ} (hm : IsFrieze n m)
    (hpos : ∀ r j, 0 < r → r < n → 0 < m r j) :
    ∀ r, 1 ≤ r → r ≤ n → ∀ j, m r j = Kc (quiddity m) j (r - 1) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro h1 hn j
    match r, h1 with
    | 1, _ => simpa using hm.row_one j
    | 2, _ => simp [quiddity]
    | (k + 3), _ =>
      have hk1 : k + 1 ≤ n := by omega
      have hk2 : k + 2 ≤ n := by omega
      have hkpos : 0 < k + 1 := by omega
      have hne : m (k + 1) (j + 1) ≠ 0 := by
        rcases Nat.lt_or_ge (k + 1) n with hlt | hge
        · exact (hpos (k + 1) (j + 1) hkpos hlt).ne'
        · exfalso; omega
      have hd := hm.diamond (k + 3) j (by omega) hn
      have e1 : m (k + 1) (j + 1) = Kc (quiddity m) (j + 1) k := by
        have := ih (k + 1) (by omega) (by omega) hk1 (j + 1)
        simpa using this
      have e2 : m (k + 2) j = Kc (quiddity m) j (k + 1) := by
        have := ih (k + 2) (by omega) (by omega) hk2 j
        simpa using this
      have e3 : m (k + 2) (j + 1) = Kc (quiddity m) (j + 1) (k + 1) := by
        have := ih (k + 2) (by omega) (by omega) hk2 (j + 1)
        simpa using this
      have hid := Kc_identity (quiddity m) j k
      have hsimp : m (k + 3 - 2) (j + 1) * m (k + 3) j
          = m (k + 3 - 1) j * m (k + 3 - 1) (j + 1) - 1 := hd
      simp only [show k + 3 - 2 = k + 1 from rfl, show k + 3 - 1 = k + 2 from rfl] at hsimp
      rw [e1, e2, e3] at hsimp
      have hgoal : Kc (quiddity m) (j + 1) k * m (k + 3) j
          = Kc (quiddity m) (j + 1) k * Kc (quiddity m) j (k + 2) := by
        rw [hsimp]; linarith [hid]
      have hne' : Kc (quiddity m) (j + 1) k ≠ 0 := by rw [← e1]; exact hne
      have := mul_left_cancel₀ hne' hgoal
      simpa using this

/-- **The closing conditions, read through the continuant.** Row `n-1` constant `1` says
every window of length `n-2` has continuant `1`, and row `n` vanishing says every window of
length `n-1` has continuant `0`. These are the equations Proposition `prop:param` solves for
the last three quiddity entries. -/
theorem closing_conditions {n : ℕ} {m : ℕ → ℤ → ℚ} (hm : IsFrieze n m)
    (hpos : ∀ r j, 0 < r → r < n → 0 < m r j) (hn : 3 ≤ n) :
    (∀ j, Kc (quiddity m) j (n - 2) = 1) ∧ (∀ j, Kc (quiddity m) j (n - 1) = 0) := by
  constructor
  · intro j
    have h := entry_eq_continuant hm hpos (n - 1) (by omega) (by omega) j
    have hs : n - 1 - 1 = n - 2 := by omega
    rw [hs] at h
    rw [← h, hm.row_top_one j]
  · intro j
    have := entry_eq_continuant hm hpos n (by omega) (le_refl n) j
    rw [← this, hm.row_top_zero j]

/-- **The quiddity determines the frieze.** Two positive friezes of width `n` whose quiddity
cycles agree agree at every entry. Reducing the hypothesis from the whole quiddity to its
first `n-3` entries, which is what Proposition `prop:param` asserts, needs the formulas of
`param_formulas` inverted, and that is not done here. -/
theorem frieze_determined {n : ℕ} {m m' : ℕ → ℤ → ℚ} (hm : IsFrieze n m) (hm' : IsFrieze n m')
    (hp : ∀ r j, 0 < r → r < n → 0 < m r j) (hp' : ∀ r j, 0 < r → r < n → 0 < m' r j)
    (hq : ∀ j, quiddity m j = quiddity m' j) :
    ∀ r j, 1 ≤ r → r ≤ n → m r j = m' r j := by
  have hK : ∀ j k, Kc (quiddity m) j k = Kc (quiddity m') j k := by
    intro j k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      match k with
      | 0 => rfl
      | 1 => simpa using hq j
      | (p + 2) =>
        rw [Kc_succ_succ, Kc_succ_succ, hq (j + p + 1),
          ihk (p + 1) (by omega), ihk p (by omega)]
  intro r j h1 hn
  rw [entry_eq_continuant hm hp r h1 hn j, entry_eq_continuant hm' hp' r h1 hn j, hK]

/-! ## Proposition `prop:param`: the three closing formulas

Writing the width as `p + 5` makes the index arithmetic concrete: the last three quiddity
entries are `a_{p+2}`, `a_{p+3}`, `a_{p+4}`, and the two closing conditions are on windows of
length `p + 3` and `p + 4`. Expanding each by the continuant recursion once solves for them.
The formulas are stated multiplicatively, so no nonvanishing hypothesis is needed. -/

/-- **The three formulas of Proposition `prop:param`.** -/
theorem param_formulas {p : ℕ} {m : ℕ → ℤ → ℚ} (hm : IsFrieze (p + 5) m)
    (hpos : ∀ r j, 0 < r → r < p + 5 → 0 < m r j) :
    quiddity m ((p : ℤ) + 3) = Kc (quiddity m) 0 (p + 2) ∧
    quiddity m ((p : ℤ) + 2) * Kc (quiddity m) 0 (p + 2)
      = Kc (quiddity m) 0 (p + 1) + 1 ∧
    quiddity m ((p : ℤ) + 4) * Kc (quiddity m) 0 (p + 2)
      = Kc (quiddity m) 1 (p + 1) + 1 := by
  set a := quiddity m with ha
  obtain ⟨hone, hzero⟩ := closing_conditions hm hpos (by omega)
  have e3 : ∀ j : ℤ, Kc a j (p + 3) = 1 := by
    intro j; have := hone j; simpa using this
  have e4 : ∀ j : ℤ, Kc a j (p + 4) = 0 := by
    intro j; have := hzero j; simpa using this
  -- a_{p+3} from the length-(p+4) window at column 0
  have h1 : a ((p : ℤ) + 3) = Kc a 0 (p + 2) := by
    have hx : Kc a 0 (p + 2 + 2) = a (0 + (p + 2 : ℕ) + 1) * Kc a 0 (p + 3) - Kc a 0 (p + 2) :=
      Kc_succ_succ a 0 (p + 2)
    have hidx : ((0 : ℤ) + ((p + 2 : ℕ) : ℤ) + 1) = (p : ℤ) + 3 := by push_cast; ring
    rw [hidx, e3 0] at hx
    have : Kc a 0 (p + 4) = a ((p : ℤ) + 3) * 1 - Kc a 0 (p + 2) := by
      have hp : p + 2 + 2 = p + 4 := by omega
      rwa [hp] at hx
    rw [e4 0] at this; linarith
  -- a_{p+2} from the length-(p+3) window at column 0
  have h2 : a ((p : ℤ) + 2) * Kc a 0 (p + 2) = Kc a 0 (p + 1) + 1 := by
    have hx : Kc a 0 (p + 1 + 2) = a (0 + (p + 1 : ℕ) + 1) * Kc a 0 (p + 2) - Kc a 0 (p + 1) :=
      Kc_succ_succ a 0 (p + 1)
    have hidx : ((0 : ℤ) + ((p + 1 : ℕ) : ℤ) + 1) = (p : ℤ) + 2 := by push_cast; ring
    have hp : p + 1 + 2 = p + 3 := by omega
    rw [hidx, hp] at hx
    rw [e3 0] at hx; linarith
  -- a_{p+4} from the length-(p+4) window at column 1, then the length-(p+3) window there
  have h3 : a ((p : ℤ) + 4) = Kc a 1 (p + 2) := by
    have hx : Kc a 1 (p + 2 + 2) = a (1 + (p + 2 : ℕ) + 1) * Kc a 1 (p + 3) - Kc a 1 (p + 2) :=
      Kc_succ_succ a 1 (p + 2)
    have hidx : ((1 : ℤ) + ((p + 2 : ℕ) : ℤ) + 1) = (p : ℤ) + 4 := by push_cast; ring
    have hp : p + 2 + 2 = p + 4 := by omega
    rw [hidx, hp, e3 1, e4 1] at hx; linarith
  have h4 : a ((p : ℤ) + 3) * Kc a 1 (p + 2) = Kc a 1 (p + 1) + 1 := by
    have hx : Kc a 1 (p + 1 + 2) = a (1 + (p + 1 : ℕ) + 1) * Kc a 1 (p + 2) - Kc a 1 (p + 1) :=
      Kc_succ_succ a 1 (p + 1)
    have hidx : ((1 : ℤ) + ((p + 1 : ℕ) : ℤ) + 1) = (p : ℤ) + 3 := by push_cast; ring
    have hp : p + 1 + 2 = p + 3 := by omega
    rw [hidx, hp, e3 1] at hx; linarith
  refine ⟨h1, h2, ?_⟩
  rw [← h1, h3] at *
  linarith [h4]

/-- **Width five, from the definition.** At `n = 5` the formulas read
`a₃ = a₀a₁ - 1`, `a₂(a₀a₁-1) = a₀+1`, `a₄(a₀a₁-1) = a₁+1`, which is the parameterisation
that `Frieze5` and the predicate `W5` encode. This is the link between the frieze definition
and the arithmetic predicate the width-5 count is carried out with. -/
theorem width5_from_frieze {m : ℕ → ℤ → ℚ} (hm : IsFrieze 5 m)
    (hpos : ∀ r j, 0 < r → r < 5 → 0 < m r j) :
    quiddity m 3 = quiddity m 0 * quiddity m 1 - 1 ∧
    quiddity m 2 * (quiddity m 0 * quiddity m 1 - 1) = quiddity m 0 + 1 ∧
    quiddity m 4 * (quiddity m 0 * quiddity m 1 - 1) = quiddity m 1 + 1 := by
  have h := param_formulas (p := 0) (by simpa using hm) (by simpa using hpos)
  simp only [Nat.cast_zero, zero_add] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hK2 : Kc (quiddity m) 0 2 = quiddity m 1 * quiddity m 0 - 1 := by
    rw [Kc_succ_succ (quiddity m) 0 0]; norm_num
  have hK1 : Kc (quiddity m) 0 1 = quiddity m 0 := rfl
  have hK1' : Kc (quiddity m) 1 1 = quiddity m 1 := rfl
  rw [hK2] at h1 h2 h3
  rw [hK1] at h2
  rw [hK1'] at h3
  refine ⟨by linarith [h1], ?_, ?_⟩
  · nlinarith [h2]
  · nlinarith [h3]

/-! ## The lattice condition

`width5_from_frieze` is the algebraic half of the width-5 parameterisation. The other half is
that the entries lie in `(1/N)ℤ`, which is what makes the count a count over the lattice
rather than over `ℚ`. Writing the five quiddity entries as `p/N`, `q/N`, `c₂/N`, `d/N`,
`c₄/N`, the algebra forces `pq = N² + dN` and `c₂d = N(p+N)` and `c₄d = N(q+N)`, and those
three identities are exactly the conditions collected in `W5`.
-/

/-- **From a lattice frieze to the arithmetic predicate.** A positive width-5 frieze whose
quiddity entries all lie in `(1/N)ℤ`, recorded by their numerators, has those numerators
satisfying `W5`. The lattice hypotheses are stated multiplicatively, `N·aⱼ = numerator`, so
no division occurs anywhere in the proof. Together with `width5_from_frieze` this closes the
link between Definition `def:frieze` and the predicate the width-5 count is carried out
with. -/
theorem W5_of_frieze {N : ℕ} (hN : 0 < N) {m : ℕ → ℤ → ℚ} (hm : IsFrieze 5 m)
    (hpos : ∀ r j, 0 < r → r < 5 → 0 < m r j) {p q c₂ d c₄ : ℕ}
    (hp : (N : ℚ) * quiddity m 0 = p) (hq : (N : ℚ) * quiddity m 1 = q)
    (h2 : (N : ℚ) * quiddity m 2 = c₂) (hd : (N : ℚ) * quiddity m 3 = d)
    (h4 : (N : ℚ) * quiddity m 4 = c₄) :
    W5 N p q := by
  obtain ⟨e3, e2, e4⟩ := width5_from_frieze hm hpos
  have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  -- the quiddity entries are positive
  have hqpos : ∀ j : ℤ, 0 < quiddity m j := fun j => hpos 2 j (by omega) (by omega)
  have hdpos : 0 < d := by
    have : (0 : ℚ) < (d : ℚ) := by rw [← hd]; exact mul_pos hNQ (hqpos 3)
    exact_mod_cast this
  have hppos : 0 < p := by
    have : (0 : ℚ) < (p : ℚ) := by rw [← hp]; exact mul_pos hNQ (hqpos 0)
    exact_mod_cast this
  have hqpos' : 0 < q := by
    have : (0 : ℚ) < (q : ℚ) := by rw [← hq]; exact mul_pos hNQ (hqpos 1)
    exact_mod_cast this
  -- p q = N² + d N
  have keyQ : (p : ℚ) * q = (N : ℚ) ^ 2 + (d : ℚ) * N := by
    have h1 : (p : ℚ) * q = (N : ℚ) ^ 2 * (quiddity m 0 * quiddity m 1) := by
      rw [← hp, ← hq]; ring
    have h2' : quiddity m 0 * quiddity m 1 = quiddity m 3 + 1 := by linarith [e3]
    rw [h2', show (N : ℚ) ^ 2 * (quiddity m 3 + 1)
      = (N : ℚ) * ((N : ℚ) * quiddity m 3) + (N : ℚ) ^ 2 from by ring, hd] at h1
    linarith [h1]
  have key : p * q = N ^ 2 + d * N := by exact_mod_cast keyQ
  -- c₂ d = N (p + N)  and  c₄ d = N (q + N)
  have ha3 : quiddity m 2 * quiddity m 3 = quiddity m 0 + 1 := by rw [e3]; exact e2
  have ha4 : quiddity m 4 * quiddity m 3 = quiddity m 1 + 1 := by rw [e3]; exact e4
  have key2 : c₂ * d = N * (p + N) := by
    have h1 : (c₂ : ℚ) * d = ((N : ℚ) * quiddity m 2) * ((N : ℚ) * quiddity m 3) := by
      rw [h2, hd]
    rw [show ((N : ℚ) * quiddity m 2) * ((N : ℚ) * quiddity m 3)
      = (N : ℚ) ^ 2 * (quiddity m 2 * quiddity m 3) from by ring, ha3,
      show (N : ℚ) ^ 2 * (quiddity m 0 + 1)
      = (N : ℚ) * ((N : ℚ) * quiddity m 0) + (N : ℚ) ^ 2 from by ring, hp] at h1
    have : (c₂ : ℚ) * d = (N : ℚ) * ((p : ℚ) + N) := by linarith [h1]
    exact_mod_cast this
  have key4 : c₄ * d = N * (q + N) := by
    have h1 : (c₄ : ℚ) * d = ((N : ℚ) * quiddity m 4) * ((N : ℚ) * quiddity m 3) := by
      rw [h4, hd]
    rw [show ((N : ℚ) * quiddity m 4) * ((N : ℚ) * quiddity m 3)
      = (N : ℚ) ^ 2 * (quiddity m 4 * quiddity m 3) from by ring, ha4,
      show (N : ℚ) ^ 2 * (quiddity m 1 + 1)
      = (N : ℚ) * ((N : ℚ) * quiddity m 1) + (N : ℚ) ^ 2 from by ring, hq] at h1
    have : (c₄ : ℚ) * d = (N : ℚ) * ((q : ℚ) + N) := by linarith [h1]
    exact_mod_cast this
  have hlt : N ^ 2 < p * q := by
    have : 0 < d * N := by positivity
    omega
  have hsub : p * q - N ^ 2 = d * N := by omega
  refine ⟨hppos, hqpos', hlt, ⟨N + d, by rw [key]; ring⟩, ?_, ?_⟩
  · exact hsub ▸ ⟨c₂, by rw [show N ^ 2 * (p + N) = N * (N * (p + N)) from by ring, ← key2]; ring⟩
  · exact hsub ▸ ⟨c₄, by rw [show N ^ 2 * (q + N) = N * (N * (q + N)) from by ring, ← key4]; ring⟩

/-! ## Non-vacuity

A definition with no model proves nothing. The Conway--Coxeter frieze of width `5` with
quiddity `(1,3,1,2,2)` is exhibited here and shown to satisfy `IsFrieze 5`, so the results
above are not vacuous. Its row `3` is `(2,2,1,3,1)`, row `4` is constant `1` and row `5`
vanishes, which is what the closing conditions require.
-/

/-- The Conway--Coxeter frieze of width `5`, quiddity `(1,3,1,2,2)`. Row `3` is
`(2,2,1,3,1)`, row `4` is constant `1` and row `5` vanishes. Columns are reduced mod `5`
directly on `ℤ`, so every check below is an integer case split. -/
def cc5 (r : ℕ) (j : ℤ) : ℚ :=
  if r = 2 then
    (if j % 5 = 0 then 1 else if j % 5 = 1 then 3 else if j % 5 = 2 then 1
     else if j % 5 = 3 then 2 else 2)
  else if r = 3 then
    (if j % 5 = 0 then 2 else if j % 5 = 1 then 2 else if j % 5 = 2 then 1
     else if j % 5 = 3 then 3 else 1)
  else if r = 1 ∨ r = 4 then 1
  else 0

/-- **`IsFrieze` has a model.** Without this every theorem above would be vacuous. -/
theorem cc5_isFrieze : IsFrieze 5 cc5 := by
  refine ⟨?_, fun j => rfl, fun j => rfl, fun j => rfl, fun j => rfl, ?_⟩
  · intro r j
    have h : (j + (5 : ℕ) : ℤ) % 5 = j % 5 := by push_cast; omega
    simp only [cc5, h]
  · intro r j h2 h5
    rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4)
      with h | h | h | h | h
    · have h' : (j + 1) % 5 = 1 := by omega
      interval_cases r <;> norm_num [cc5, h, h']
    · have h' : (j + 1) % 5 = 2 := by omega
      interval_cases r <;> norm_num [cc5, h, h']
    · have h' : (j + 1) % 5 = 3 := by omega
      interval_cases r <;> norm_num [cc5, h, h']
    · have h' : (j + 1) % 5 = 4 := by omega
      interval_cases r <;> norm_num [cc5, h, h']
    · have h' : (j + 1) % 5 = 0 := by omega
      interval_cases r <;> norm_num [cc5, h, h']

/-- The model is positive, so `IsPositiveFrieze 5` is inhabited and the results above are
not vacuous. -/
theorem cc5_positive : IsPositiveFrieze 5 cc5 := by
  refine ⟨cc5_isFrieze, ?_⟩
  intro r j h0 h5
  rcases (by omega : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4)
    with h | h | h | h | h <;>
  · interval_cases r <;> norm_num [cc5, h]

/-! ## Width six

`param_formulas` at `p = 1`. Writing the six quiddity numerators as `p, q, r, c₃, e, c₅`,
the length-3 continuant `K_3(a_0,a_1,a_2) = a_2(a_1a_0-1) - a_0` is the fifth entry, and
clearing denominators turns the three formulas into `pqr = N²(e+p+r)`, `c₃e = pq` and
`c₅e = qr`. The first is the defining relation of `W6` and the other two are its first two
divisibilities. -/

/-- **Width six, from the definition.** A positive width-6 frieze whose quiddity entries lie
in `(1/N)ℤ` satisfies the defining relation of `W6` and two of its three divisibilities. The
remaining one, `e ∣ N(p+r)`, needs a lattice condition on a row other than the quiddity and
is not derived here. -/
theorem width6_from_frieze {N : ℕ} {m : ℕ → ℤ → ℚ} (hm : IsFrieze 6 m)
    (hpos : ∀ r j, 0 < r → r < 6 → 0 < m r j) {p q r c₃ e c₅ : ℕ}
    (h0 : (N : ℚ) * quiddity m 0 = p) (h1 : (N : ℚ) * quiddity m 1 = q)
    (h2 : (N : ℚ) * quiddity m 2 = r) (h3 : (N : ℚ) * quiddity m 3 = c₃)
    (h4 : (N : ℚ) * quiddity m 4 = e) (h5 : (N : ℚ) * quiddity m 5 = c₅) :
    p * q * r = N ^ 2 * (e + p + r) ∧ e ∣ p * q ∧ e ∣ q * r := by
  obtain ⟨eA, eB, eC⟩ := param_formulas (p := 1) (by simpa using hm) (by simpa using hpos)
  set a := quiddity m with ha
  norm_num at eA eB eC
  have hK2 : Kc a 0 2 = a 1 * a 0 - 1 := by rw [Kc_succ_succ a 0 0]; norm_num
  have hK3 : Kc a 0 3 = a 2 * (a 1 * a 0 - 1) - a 0 := by
    rw [Kc_succ_succ a 0 1, hK2]; norm_num
  have hK1' : Kc a 1 2 = a 2 * a 1 - 1 := by rw [Kc_succ_succ a 1 0]; norm_num
  rw [hK3] at eA eB eC
  rw [hK2] at eB
  rw [hK1'] at eC
  -- the defining relation
  have key : (p : ℚ) * q * r = (N : ℚ) ^ 2 * ((e : ℚ) + p + r) := by
    rw [← h0, ← h1, ← h2, ← h4, eA]; ring
  -- c₃ e = p q  and  c₅ e = q r
  have hpq : (c₃ : ℚ) * e = (p : ℚ) * q := by
    have : a 3 * (a 2 * (a 1 * a 0 - 1) - a 0) = a 1 * a 0 := by linarith [eB]
    rw [← h3, ← h4, eA, ← h0, ← h1]
    calc (N : ℚ) * a 3 * ((N : ℚ) * (a 2 * (a 1 * a 0 - 1) - a 0))
        = (N : ℚ) ^ 2 * (a 3 * (a 2 * (a 1 * a 0 - 1) - a 0)) := by ring
      _ = (N : ℚ) ^ 2 * (a 1 * a 0) := by rw [this]
      _ = (N : ℚ) * a 0 * ((N : ℚ) * a 1) := by ring
  have hqr : (c₅ : ℚ) * e = (q : ℚ) * r := by
    have : a 5 * (a 2 * (a 1 * a 0 - 1) - a 0) = a 2 * a 1 := by linarith [eC]
    rw [← h5, ← h4, eA, ← h1, ← h2]
    calc (N : ℚ) * a 5 * ((N : ℚ) * (a 2 * (a 1 * a 0 - 1) - a 0))
        = (N : ℚ) ^ 2 * (a 5 * (a 2 * (a 1 * a 0 - 1) - a 0)) := by ring
      _ = (N : ℚ) ^ 2 * (a 2 * a 1) := by rw [this]
      _ = (N : ℚ) * a 1 * ((N : ℚ) * a 2) := by ring
  refine ⟨by exact_mod_cast key, ⟨c₃, ?_⟩, ⟨c₅, ?_⟩⟩
  · have : (p : ℚ) * q = (e : ℚ) * c₃ := by linarith [hpq]
    exact_mod_cast this
  · have : (q : ℚ) * r = (e : ℚ) * c₅ := by linarith [hqr]
    exact_mod_cast this

end VicoEnum
