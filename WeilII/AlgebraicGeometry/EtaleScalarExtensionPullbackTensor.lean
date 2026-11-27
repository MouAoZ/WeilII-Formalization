module

import WeilII.CategoryTheory.DerivedMonoidalPullbackSquare

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExact
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsRestrictScalarsMate
public import WeilConjectures.SixFunctors.Etale.ScalarExtension.Monoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-! # Tensor compatibility of scalar extension with étale pullback -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace WeilII

variable {A B : Type (u+1)} [CommRing A] [CommRing B] (ρ : A →+* B)
  {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- Derived étale pullback commutes monoidally with extension of scalars for arbitrary
coefficient homomorphisms. Both comparisons are computed using their left-derived counits. -/
theorem etaleScalarExtension_pullbackTensor :
    have : (sheafExtendScalars ρ X).PreservesFlat :=
      Sheaf.preservesFlat_extendScalars X.smallEtaleTopology (f := ρ)
    have : (sheafExtendScalars ρ Z).PreservesFlat :=
      Sheaf.preservesFlat_extendScalars Z.smallEtaleTopology (f := ρ)
    Adjunction.ComparisonCompatible (leftDerivedUpperStarEtaleSheafExtendScalarsIso ρ i)
      (Etale.upperStar (ModuleCat.{u+1} A) i).leftDerivedTensorComparison
      (Etale.upperStar (ModuleCat.{u+1} B) i).leftDerivedTensorComparison
      (asIso (sheafExtendScalars ρ Z).leftDerivedTensorComparison)
      (asIso (sheafExtendScalars ρ X).leftDerivedTensorComparison) := by
  let S := sheafExtendScalars ρ X
  let P := Etale.upperStar (ModuleCat.{u+1} B) i
  let U := Etale.upperStar (ModuleCat.{u+1} A) i
  let T := sheafExtendScalars ρ Z
  have : S.PreservesFlat := Sheaf.preservesFlat_extendScalars X.smallEtaleTopology (f := ρ)
  have : T.PreservesFlat := Sheaf.preservesFlat_extendScalars Z.smallEtaleTopology (f := ρ)
  have : (S ⋙ P).PreservesKFlatQuasiIso := Functor.preservesKFlatQuasiIso_comp_of_exact S P
  let α : U.leftDerivedFunctor ⋙ T.leftDerivedFunctor ≅ S.leftDerivedFunctor ⋙ P.leftDerivedFunctor := (leftDerivedUpperStarEtaleSheafExtendScalarsIso ρ i).symm
  have : NatTrans.IsMonoidal (sheafExtendScalarsCompUpperStarIso ρ i).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (sheafExtendScalarsCompUpperStarIso ρ i).inv)
  apply derivedMonoidalPullbackSquare S P U T (sheafExtendScalarsCompUpperStarIso ρ i).symm
    α (leftDerivedEtaleSheafExtendScalarsUpperStarCounit ρ i) (fun _ ↦ rfl)
  intro Y
  have hc := leftDerivedUpperStarEtaleSheafExtendScalarsIso_inv_app_comp_counit ρ i Y
  simp only [mapHomotopyCategoryEtaleSheafExtendScalarsCompUpperStarIso, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, Category.comp_id, Category.id_comp,
    leftDerivedEtaleSheafExtendScalarsUpperStarCounit, leftDerivedUpperStarEtaleSheafExtendScalarsCounit,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] at hc
  exact hc

end WeilII
