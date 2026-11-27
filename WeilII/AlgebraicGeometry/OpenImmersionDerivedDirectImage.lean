module

public import WeilConjectures.WeilSheaf.LowerStar

/-!
# Derived direct image of a Weil sheaf restricted to an open subscheme

In Zhang, *On an elementary proof of Weil II*, p. 2, the third term of the localization
triangle preceding (†) is `Rj_* j^* G`. Lemmas 2.1 and 2.2 take its geometric compactly
supported cohomology with the induced Frobenius action.
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The Weil complex `Rj_* j^* G` in Zhang's sequence (†), p. 2. Restrict the constructible
Weil sheaf `G` to the open subscheme, place it in degree zero, and take its derived direct
image on `X`. -/
@[expose] public noncomputable def openImmersionDerivedDirectImageOfRestriction
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k))] [X.Over (Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (CommRingCat.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (G : WeilSheaf k ℓ X) : WeilComplex k ℓ X :=
  (WeilComplex.derivedLowerStar j).obj (WeilSheaf.toComplex.obj ((WeilSheaf.upperStar j).obj G))

end WeilII
