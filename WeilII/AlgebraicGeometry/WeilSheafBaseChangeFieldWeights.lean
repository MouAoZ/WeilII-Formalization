module

public import WeilConjectures.WeilSheaf.BaseChangeField.Restriction
public import WeilConjectures.WeilSheaf.Stalk
import WeilConjectures.WeilSheaf.BaseChangeField.Stalk
import WeilConjectures.WeilSheaf.UpperStarPointwise
import WeilII.AlgebraicGeometry.WeilSheafBaseChangeFieldStalkPower

/-!
# Pointwise upper weights after a finite extension of constants

Zhang, *On an elementary proof of Weil II*, defines the pointwise hypothesis after Theorem 1.1
on p. 1 and passes to finite extensions on p. 2. The proof of Proposition 1.5 on p. 4 uses
this hypothesis over the field of definition of the chosen hypersurface.
-/

open AlgebraicGeometry

namespace WeilII

universe u

/-- A finite extension of constants preserves the pointwise upper weight bound in Zhang,
*On an elementary proof of Weil II*, pp. 1–2, with the residue-field size at each closed point
of the base change.

Fix a closed point `x'` over `K` and let `x` be its image. The inclusion of residue fields
makes `κ(x)` finite, so `x` is closed. Write `d = [K : k]`, let `e'` and `e` be the degrees
of the two points over their respective base fields, and put `f = [κ(x') : κ(x)]`.
The two towers of residue fields give `d * e' = e * f` and `#κ(x') = (#κ(x))^f`.

Identify the geometric fibers using compatible algebraic closures. The Weil structure after
base change is the transport of the original structure iterated `d` times. Hence the stalk
at the chosen lift of `x'`, with Frobenius of degree `e'` over `K`, is equivariantly isomorphic
to the original stalk at the transported lift over `x`, with Frobenius of degree `d * e'` over
`k`. Comparing that lift with the chosen lift of `x` at degree `e` identifies the characteristic
polynomial of the new Frobenius with that of the `f`-th power of the original local Frobenius.
Over the algebraically closed coefficient field each new eigenvalue therefore has the form
`α^f` for an original eigenvalue `α`. Raising the input bound at `x` to the positive power `f`
gives `‖ι (α^f)‖ ≤ (#κ(x'))^(w/2)`. This holds at every closed point of the base change. -/
public theorem weilSheaf_hasWeightsAtMost_baseChangeField
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    {ι : PadicAlgCl ℓ →+* ℂ} {E : WeilSheaf k ℓ X} {w : ℝ}
    (hE : E.HasWeightsAtMost ι w) :
    letI : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
    ((WeilSheaf.baseChangeField K).obj E).HasWeightsAtMost ι w := by
  let : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
  intro y
  obtain ⟨hr, hcard, hpoly⟩ := weilSheaf_stalk_baseChangeField_power K E y
  rw [hcard]
  exact FrobeniusModule.HasWeightsAtMost.of_charpoly_eq_pow (hE _) hr hpoly

end WeilII
