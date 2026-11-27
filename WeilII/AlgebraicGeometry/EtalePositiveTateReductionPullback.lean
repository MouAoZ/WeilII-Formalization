module

public import WeilII.AlgebraicGeometry.EtaleKummerTateObjectReduction
public import WeilII.AlgebraicGeometry.EtaleKummerPowerPullback
public import WeilII.AlgebraicGeometry.EtaleSingleModelReductionPullback
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.TwistPullback

/-! # Geometric pullback of the direct positive Tate comparison -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] {ρ : A →+* B}
  {X Y : Scheme.{u}} (f : X ⟶ Y) (hρ : Function.Surjective ρ)
  {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
  [NeZero (ringChar A)] [NeZero (ringChar B)] [HasInvertibleExponent A X] [HasInvertibleExponent B X]
  [HasInvertibleExponent A Y] [HasInvertibleExponent B Y] {d : ℕ} (hd : ringChar A = ringChar B * d)

/-- The Kummer power-map transpose on the degree-zero sheaves of roots. -/
noncomputable def etaleKummerRootsPowerTranspose :
    (derivedExtendScalars hρ ha X).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj (tateSheaf A X)) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj (tateSheaf B X) :=
  ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars X.smallEtaleTopology ρ)
    (derivedExtendScalarsAdjunction hρ ha X) (kummerRootsReduction ρ X hd)

/-- In the single-complex model, the direct comparison uses the same power map for every Kummer pullback. -/
theorem positiveTateObjectReduction_eq_rootsTranspose :
    (derivedExtendScalarsTateObjectIso hρ ha X 1).hom =
      (derivedExtendScalars hρ ha X).map (tateTwistObjectOneIso X A).hom ≫
        etaleKummerRootsPowerTranspose (X := X) hρ ha hd ≫ (tateTwistObjectOneIso X B).inv := by
  have h := positiveTateObjectReduction_eq_kummer (ρ := ρ) (𝟙 X.gmSheaf) hd hρ ha
  exact h

include hd in
/-- The positive Tate identification computed directly at each scheme commutes with pullback. -/
theorem positiveTateObjectReduction_pullback :
    (derivedExtendScalarsPullbackIso hρ ha f).hom.app _ ≫
        L((f)^*[ModuleCat.{u + 1} B]).map (derivedExtendScalarsTateObjectIso hρ ha Y 1).hom ≫
        (leftDerivedUpperStarTateObjectIso (Λ := B) f 1).hom =
      (derivedExtendScalars hρ ha X).map (leftDerivedUpperStarTateObjectIso (Λ := A) f 1).hom ≫
        (derivedExtendScalarsTateObjectIso hρ ha X 1).hom := by
  exact etaleReductionPullback_of_singleModels f hρ ha
    (M := (extendScalars A Y).obj (Y.rootsOfUnitySheaf (ringChar A)))
    (M' := (extendScalars A X).obj (X.rootsOfUnitySheaf (ringChar A)))
    (N := (extendScalars B Y).obj (Y.rootsOfUnitySheaf (ringChar B)))
    (N' := (extendScalars B X).obj (X.rootsOfUnitySheaf (ringChar B)))
    (kummerRootsReduction ρ Y hd) (kummerRootsReduction ρ X hd)
    ((upperStarExtendScalarsIso A f).hom.app (Y.rootsOfUnitySheaf (ringChar A)) ≫
      (extendScalars A X).map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar A) f))
    ((upperStarExtendScalarsIso B f).hom.app (Y.rootsOfUnitySheaf (ringChar B)) ≫
      (extendScalars B X).map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar B) f)) (kummerRootsReduction_pullback ρ f hd)
    (tateTwistObjectOneIso Y A) (tateTwistObjectOneIso Y B) (tateTwistObjectOneIso X A) (tateTwistObjectOneIso X B)
    (leftDerivedUpperStarTateTwistObjectIso A f 1).hom (leftDerivedUpperStarTateTwistObjectIso B f 1).hom
    (derivedExtendScalarsTateObjectIso hρ ha Y 1).hom (derivedExtendScalarsTateObjectIso hρ ha X 1).hom
    (positiveTateObjectReduction_eq_rootsTranspose (X := Y) hρ ha hd)
    (positiveTateObjectReduction_eq_rootsTranspose (X := X) hρ ha hd)
    (leftDerivedUpperStar_map_tateTwistObjectOneIso A f) (leftDerivedUpperStar_map_tateTwistObjectOneIso B f)

end WeilII
