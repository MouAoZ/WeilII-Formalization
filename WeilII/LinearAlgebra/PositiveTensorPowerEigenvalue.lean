module

public import WeilII.LinearAlgebra.FrobeniusModulePositiveTensorPower

namespace FrobeniusModule

/-- In Zhang's deduction of Theorem 1.1 from Proposition 1.5 (p. 2), an eigenvalue
`α` on a Frobenius module gives the eigenvalue `α ^ n` on its positive tensor power.
For each additional factor, tensor an eigenvector with an eigenvector for `α`. -/
public theorem hasEigenvalue_positiveTensorPower {K : Type*} [Field K] {V : FrobeniusModule K}
    {α : K} (hα : V.frobeniusEnd.HasEigenvalue α) : ∀ (n : ℕ) (hn : 0 < n),
      (V.positiveTensorPower n hn).frobeniusEnd.HasEigenvalue (α ^ n)
  | 0, hn => (Nat.lt_irrefl 0 hn).elim
  | 1, _ => by
    rw [positiveTensorPower, pow_one]
    exact hα
  | n + 2, _ => by
    rw [positiveTensorPower, pow_succ]
    exact hasEigenvalue_tensor_mul (hasEigenvalue_positiveTensorPower hα (n + 1) n.succ_pos) hα

end FrobeniusModule
