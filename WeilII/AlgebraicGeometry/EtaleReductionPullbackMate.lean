module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsRestrictScalarsMate

/-! # The pullback exchange used by scalar reduction -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Etale

namespace WeilII

variable {A B : Type (u+1)} [CommRing A] [CommRing B]
  {ρ : A →+* B} (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
  {Z X : Scheme.{u}} (i : Z ⟶ X)


/-- The pullback exchange specified by scalar reduction is the inverse of the derived
sheaf-level pullback exchange. Under the scalar adjunctions both have the restriction-of-
scalars pullback comparison as mate, and taking a mate is bijective. -/
theorem etaleScalarReduction_pullbackIso_eq :
    derivedExtendScalarsPullbackIso hρ ha i = (leftDerivedUpperStarEtaleSheafExtendScalarsIso ρ i).symm := by
  apply Iso.ext
  apply (mateEquiv (derivedExtendScalarsAdjunction hρ ha X)
    (derivedExtendScalarsAdjunction hρ ha Z)).injective
  exact ((mateEquiv _ _).apply_symm_apply _).trans
    (mateEquiv_leftDerivedUpperStarEtaleSheafExtendScalarsIso_inv ρ i).symm

end WeilII
