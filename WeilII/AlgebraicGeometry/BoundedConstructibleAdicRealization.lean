module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence

/-! # Native adic realization of bounded constructible direct images -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Forget bounded constructibility and return to the native adic coefficient model. -/
public noncomputable abbrev boundedAdicRealization (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :=
  (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)).ι ⋙
    (adicSheafDerivedEquivCondensedMod ℓ X).inverse

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

/-- Realization sends the bounded constructible ordinary direct image to native derived pushforward. -/
public noncomputable def boundedStarAdicRealizationIso :
    boundedConstructibleLowerStar ℓ f ⋙ boundedAdicRealization ℓ Y.left ≅
      boundedAdicRealization ℓ X.left ⋙ (adicLowerStar ℓ f.left).rightDerivedFunctor :=
  Functor.isoWhiskerRight (boundedConstructibleLowerStarCompatibility ℓ f) _ ≪≫
    Functor.isoWhiskerLeft _ ((adicSheafDerivedEquivCondensedMod ℓ X.left).inverseCompIsoCompInverse
      (adicSheafDerivedEquivCondensedMod ℓ Y.left) (adicRightDerivedLowerStarCompIso ℓ _ f.left)).symm

/-- Realization sends the bounded constructible exceptional direct image to the native
extension by zero followed by the proper direct image for any specified compactification. -/
public noncomputable def boundedShriekAdicRealizationIso (c : Compactification f.left) :
    boundedConstructibleLowerShriek ℓ f ⋙ boundedAdicRealization ℓ Y.left ≅
      boundedAdicRealization ℓ X.left ⋙ (adicOpenImmersionLowerShriek ℓ c.i).mapDerivedCategory ⋙
        (adicLowerStar ℓ c.g).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ (compactificationOverField f) c)
    (boundedAdicRealization ℓ Y.left) ≪≫
  Functor.isoWhiskerRight (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c) _ ≪≫
    Functor.isoWhiskerLeft _ ((adicSheafDerivedEquivCondensedMod ℓ X.left).inverseCompIsoCompInverse
      (adicSheafDerivedEquivCondensedMod ℓ Y.left)
      (adicRightDerivedLowerShriekOfCompactificationCompIso ℓ _ c)).symm

end WeilII
