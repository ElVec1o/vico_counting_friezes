/-
  VicoEnum/Multiplicative.lean

  D7b: `Q` is multiplicative, with local values `Q(p^α) = ⌊3α/2⌋ + 1`.

  Together with `conv_eq` of `VicoEnum/Dirichlet.lean` (agreement at every prime
  power) this is what the Euler product turns into

        Σ Q(N) N^{-s} = ζ(s)² ζ(2s) / ζ(3s).
-/
import VicoEnum.Dirichlet

namespace VicoEnum

/-- `Q(n) = ∏_{p^α ‖ n} (⌊3α/2⌋ + 1)`. -/
def Qp (n : ℕ) : ℕ := n.factorization.prod fun _ α => 3 * α / 2 + 1

@[simp] theorem Qp_one : Qp 1 = 1 := by simp [Qp]

/-- **D7b.** `Q` is multiplicative: the prime supports of coprime numbers are
disjoint, so the defining product splits. -/
theorem Qp_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    Qp (m * n) = Qp m * Qp n := by
  unfold Qp
  rw [Nat.factorization_mul hm hn]
  refine Finsupp.prod_add_index_of_disjoint ?_ _
  rw [Nat.support_factorization, Nat.support_factorization]
  exact Nat.Coprime.disjoint_primeFactors h

/-- The local values: `Q(p^α) = ⌊3α/2⌋ + 1 = Qlocal α`. -/
theorem Qp_prime_pow {p : ℕ} (hp : p.Prime) (α : ℕ) : Qp (p ^ α) = Qlocal α := by
  unfold Qp Qlocal
  rw [Nat.Prime.factorization_pow hp]
  exact Finsupp.prod_single_index (by norm_num)

/-- The value at a prime is `2`. -/
theorem Qp_prime {p : ℕ} (hp : p.Prime) : Qp p = 2 := by
  simpa using Qp_prime_pow hp 1

/-! ## Assembling D7

`Qp` is multiplicative with local factor `Qlocal`, and `conv_eq` says the local
convolution of `Qlocal` against the cube indicator agrees with that of the divisor
function against the square indicator. Since a multiplicative function is
determined by its values at prime powers, the two global convolutions agree, which
is the coefficient form of

    (Σ Q(N)N^{-s}) · ζ(3s) = ζ(s)² · ζ(2s).
-/

/-- The local statement of D7 in the form used by the Euler product: at each prime
`p` and each exponent `n`, the cube-side and square-side convolutions of the local
factors agree. -/
theorem local_euler_factor {p : ℕ} (hp : p.Prime) (n : ℕ) :
    convL n = convR n ∧ Qp (p ^ n) = Qlocal n :=
  ⟨conv_eq n, Qp_prime_pow hp n⟩

end VicoEnum
