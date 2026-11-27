module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateTwist
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.WeilSheaf.SmoothPurityShiftDatumSquare

/-! # Shifting a pullback square for reduction of Tate coefficients -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] {ρ : A →+* B}
  {X Y : Scheme.{u}} (f : X ⟶ Y) (hρ : Function.Surjective ρ) {a : A}
  (ha : RingHom.ker ρ = Ideal.span {a})

/-- The scalar pullback exchange commutes with the adjunction-induced shift on reduction. -/
theorem etaleDerivedExtendScalarsPullback_commShift :
    let := derivedExtendScalarsCommShift hρ ha X
    let := derivedExtendScalarsCommShift hρ ha Y
    NatTrans.CommShift (derivedExtendScalarsPullbackMap hρ ha f) ℤ := by
  let := derivedExtendScalarsCommShift hρ ha X
  let := derivedExtendScalarsCommShift hρ ha Y
  have := (derivedExtendScalarsAdjunction hρ ha X).commShift_of_rightAdjoint ℤ
  have := (derivedExtendScalarsAdjunction hρ ha Y).commShift_of_rightAdjoint ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarRestrictScalarsIso ρ f).hom ℤ := by
    dsimp only [leftDerivedUpperStarRestrictScalarsIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.mapDerivedCategorySquareIso]
    infer_instance
  dsimp only [derivedExtendScalarsPullbackMap, mateEquiv, Equiv.symm, Equiv.coe_fn_mk, TwoSquare.mk]
  infer_instance

variable [NeZero (ringChar A)] [NeZero (ringChar B)]
  [HasInvertibleExponent A X] [HasInvertibleExponent B X]
  [HasInvertibleExponent A Y] [HasInvertibleExponent B Y]

/-- Pullback compatibility for an unshifted twist implies the shifted comparison square. -/
theorem etaleTateReductionPullback_shift {m : ℤ}
    (h : (derivedExtendScalarsPullbackIso hρ ha f).hom.app _ ≫
        L((f)^*[ModuleCat.{u + 1} B]).map (derivedExtendScalarsTateObjectIso hρ ha Y m).hom ≫
          (leftDerivedUpperStarTateObjectIso (Λ := B) f m).hom =
      (derivedExtendScalars hρ ha X).map (leftDerivedUpperStarTateObjectIso (Λ := A) f m).hom ≫
        (derivedExtendScalarsTateObjectIso hρ ha X m).hom) :
    (derivedExtendScalarsPullbackIso hρ ha f).hom.app _ ≫
        L((f)^*[ModuleCat.{u + 1} B]).map (derivedExtendScalarsTateShiftIso hρ ha Y m).hom ≫
          (leftDerivedUpperStarTateShiftIso B f m).hom =
      (derivedExtendScalars hρ ha X).map (leftDerivedUpperStarTateShiftIso A f m).hom ≫
        (derivedExtendScalarsTateShiftIso hρ ha X m).hom := by
  let := derivedExtendScalarsCommShift hρ ha X
  let := derivedExtendScalarsCommShift hρ ha Y
  have := etaleDerivedExtendScalarsPullback_commShift f hρ ha
  exact purity_shift_datum_square (derivedExtendScalars hρ ha Y)
    L((f)^*[ModuleCat.{u + 1} B]) L((f)^*[ModuleCat.{u + 1} A]) (derivedExtendScalars hρ ha X)
    (derivedExtendScalarsPullbackMap hρ ha f) _ _ _ _ h (2 * m)

end WeilII
