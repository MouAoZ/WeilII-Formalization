module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Tensor

/-!
# Positive tensor powers of a Frobenius module

Zhang, *On an elementary proof of Weil II*, p. 2, uses the tensor power of compactly supported
cohomology as the source of the Frobenius-equivariant Künneth injection.
-/

namespace FrobeniusModule

universe u v

/-- The positive tensor power in Zhang's deduction of Theorem 1.1 from Proposition 1.5 (p. 2).
Degree one is `V`. Each further step tensors the preceding power with `V` on the right,
so Frobenius acts on every factor. -/
@[expose] public noncomputable def positiveTensorPower {K : Type v} [Field K]
    (V : FrobeniusModule.{u} K) : (n : ℕ) → 0 < n → FrobeniusModule.{u} K
  | 0, h => (Nat.not_lt_zero 0 h).elim
  | 1, _ => V
  | n + 2, _ => (positiveTensorPower V (n + 1) (Nat.zero_lt_succ n)).tensor V

end FrobeniusModule
