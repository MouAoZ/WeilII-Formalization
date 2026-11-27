module

public import WeilII.AlgebraicGeometry.EtaleTateSingleModelPullback
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateTwist

import WeilII.AlgebraicGeometry.EtaleTateRootReductionPullback
import WeilII.AlgebraicGeometry.TensorInverseNegativeComparison
import WeilConjectures.SixFunctors.Etale.ScalarExtension.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit

/-! # Geometric pullback of the negative Tate sheaf under scalar reduction -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

/-- Pullback commutes with direct reduction of the negative Tate sheaf. Apply the comparison
of tensor inverses to the coefficient square on the universal root lines, and transpose
back along the sheaf extension/restriction adjunction. -/
theorem etaleNegativeTateSheafReduction_pullback
    {A B : Type (u+1)} [CommRing A] [CommRing B] [NeZero (ringChar A)] [NeZero (ringChar B)]
    (ρ : A →+* B) {Z X : Scheme.{u}} [HasInvertibleExponent A Z] [HasInvertibleExponent B Z]
    [HasInvertibleExponent A X] [HasInvertibleExponent B X] (i : Z ⟶ X) :
    let g (T : Scheme.{u}) [HasInvertibleExponent A T] [HasInvertibleExponent B T] :=
      (Sheaf.extendScalarsAdjunction T.smallEtaleTopology ρ).homEquiv _ _
        (sheafExtendScalarsTateTwistSheafIso ρ T (-1)).hom
    (i)^*[ModuleCat.{u+1} A].map (g X) ≫ (upperStarRestrictScalarsIso ρ i).hom.app _ ≫
        (Sheaf.restrictScalars _ ρ).map (etaleTateSheafPullbackIso B i (-1)).hom =
      (etaleTateSheafPullbackIso A i (-1)).hom ≫ g Z := by
  let H := (i)^*[ModuleCat.{u+1} B]
  let P := (i)^*[ModuleCat.{u+1} A]
  let U := (toInvertibleExponentBase (Λ := A) X)^*[ModuleCat.{u+1} A]
  let V := (toInvertibleExponentBase (Λ := B) X)^*[ModuleCat.{u+1} B]
  let U' := (toInvertibleExponentBase (Λ := A) Z)^*[ModuleCat.{u+1} A]
  let V' := (toInvertibleExponentBase (Λ := B) Z)^*[ModuleCat.{u+1} B]
  let E := Sheaf.extendScalars X.smallEtaleTopology ρ
  let E' := Sheaf.extendScalars Z.smallEtaleTopology ρ
  let : E.Monoidal := Sheaf.monoidal_extendScalars X.smallEtaleTopology ρ
  let : E'.Monoidal := Sheaf.monoidal_extendScalars Z.smallEtaleTopology ρ
  let : E.LaxMonoidal := (Sheaf.monoidal_extendScalars X.smallEtaleTopology ρ).toLaxMonoidal
  let : E'.LaxMonoidal := (Sheaf.monoidal_extendScalars Z.smallEtaleTopology ρ).toLaxMonoidal
  let j : U' ≅ U ⋙ P := upperStarComp _ i _ _ (comp_toInvertibleExponentBase (Λ := A) i).symm
  let k : V' ≅ V ⋙ H := upperStarComp _ i _ _ (comp_toInvertibleExponentBase (Λ := B) i).symm
  let ex : E ⋙ H ≅ P ⋙ E' := sheafExtendScalarsCompUpperStarIso ρ i
  let s : (U ⋙ E) ⋙ H ≅ U' ⋙ E' :=
    U.associator E H ≪≫ Functor.isoWhiskerLeft U ex ≪≫ (U.associator P E').symm ≪≫
      Functor.isoWhiskerRight j.symm E'
  have : NatTrans.IsMonoidal j.hom := isMonoidal_upperStarComp_hom i _ _ _
  have : NatTrans.IsMonoidal k.hom := isMonoidal_upperStarComp_hom i _ _ _
  have : NatTrans.IsMonoidal k.symm.hom := inferInstanceAs (NatTrans.IsMonoidal k.inv)
  have : NatTrans.IsMonoidal ex.hom := isMonoidal_sheafExtendScalarsCompUpperStarIso_hom ρ i
  have : NatTrans.IsMonoidal s.hom := by
    dsimp only [s, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
    infer_instance
  have hs (T) : s.hom.app T = ex.hom.app (U.obj T) ≫ E'.map (j.inv.app T) := by
    dsimp only [s, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom]
    simp
  have h := tensorInverse_negativeComparison_naturality (tateSheafTensorInverse A) (tateSheafTensorInverse B)
    (U ⋙ E) V H (U' ⋙ E') V' s k.symm (sheafExtendScalarsUpperStarTateSheafIso ρ X)
    (sheafExtendScalarsUpperStarTateSheafIso ρ Z) (by
      rw [hs, Category.assoc]
      exact etaleUniversalRootReduction_pullback ρ i)
  apply (etaleSheafScalarSquare_iff ρ i (sheafExtendScalarsTateTwistSheafIso ρ X (-1)).hom
    (sheafExtendScalarsTateTwistSheafIso ρ Z (-1)).hom (etaleTateSheafPullbackIso A i (-1)).hom
    (etaleTateSheafPullbackIso B i (-1)).hom).mpr
  exact h.trans ((reassoc_of% hs _) _)

end WeilII
