module

public import WeilII.AlgebraicGeometry.SemilinearChosenCompactification

/-! # Recognizing the chosen compactification comparison from its components -/

public section

open AlgebraicGeometry CategoryTheory Limits AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.NativePointShriek

universe u

variable {ℓ : ℕ} [Fact ℓ.Prime]

local notation "Λ" => Profinite.padicAlgClRingObj ℓ

/-- A comparison with the ambient components intertwines the chosen shriek base change
with the exchange on the specified semilinear compactification. -/
theorem chosenComparisonViaComponents {κ : Type u} [Field κ] [Fact (ringChar κ).Prime]
    [Fact (ringChar κ ≠ ℓ)] {U V : Over (Spec (.of κ))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (f : U ⟶ V) (e : Spec (.of κ) ≅ Spec (.of κ)) (x : U.left ⟶ U.left)
    (y : V.left ⟶ V.left) [WeaklyEtale y]
    (wx : x ≫ U.hom ≫ e.hom = U.hom) (wy : y ≫ V.hom ≫ e.hom = V.hom)
    (sq : IsPullback x f.left f.left y) (c : Compactification f.left) (r : c.Z ⟶ c.Z)
    [WeaklyEtale r] (hi : IsPullback c.i x r c.i) (hg : IsPullback r c.g c.g y)
    (J : boundedConstructibleLowerShriek ℓ f ⋙ (boundedConstructible (condensedRingObj Λ V.left)).ι ≅
      (boundedConstructible (condensedRingObj Λ U.left)).ι ⋙ CondensedRing.rightDerivedLowerShriekOfCompactification Λ c)
    (hJ : ∀ K, J.hom.app K =
      (ambientCompactificationComparison ℓ (f := f) (compactificationOverField f) c K).hom)
    (K : Dᵇc(U.left)⟦Λ⟧) :
    (CondensedRing.upperStar Λ y).leftDerivedFunctor.map (J.hom.app K) ≫
        (purityFieldCompactificationAmbientExchange ℓ f f c c hi hg).hom.app K.obj =
      ((purityFieldLowerShriekBaseChange ℓ f f sq).hom.app K).hom ≫
        J.hom.app ((boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U) x).obj K) := by
  rw [hJ K, hJ ((boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U) x).obj K)]
  exact semilinearChosenCompactification ℓ f e x y wx wy sq c r hi hg K

end WeilII.NativePointShriek
