module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The polynomial of Zhang's chain section

In Construction 2.5 of *On an Elementary Proof of Weil II*, pp. 3–4, Zhang pulls back
a hyperplane along the graph of the sum of products of consecutive coordinates.
-/

namespace WeilII

open MvPolynomial

/-- The polynomial of the normalized hyperplane section in Zhang's Construction 2.5, p. 3.
The quadratic part sums over consecutive coordinates. Taking `a = 0` and `c = 0` gives
the phase polynomial in Lemma 2.6. -/
@[expose] public noncomputable def chainSectionPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (c : R) : MvPolynomial (Fin n) R :=
  let quadratic : MvPolynomial (Fin n) R := match n with
    | 0 => 0
    | m + 1 => ∑ i : Fin m, X i.castSucc * X i.succ
  quadratic + (∑ i, C (a i) * X i) + C c

end WeilII
