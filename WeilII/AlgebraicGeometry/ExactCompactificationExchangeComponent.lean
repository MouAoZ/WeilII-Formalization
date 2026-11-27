module

public import WeilConjectures.WeilSheaf.CondensedModelBaseChange
import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp

/-! # Components of exact compactification base change -/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilII.NativePointShriek

universe u

private theorem compExchange_app {A B D : Type*} [Category A] [Category B] [Category D]
    (J : A ⥤ B) (R : B ⥤ D) {X : A ⥤ A} {Z : B ⥤ B} {Y : D ⥤ D}
    (o : J ⋙ Z ≅ X ⋙ J) (p : R ⋙ Y ≅ Z ⋙ R)
    (e : (J ⋙ R) ⋙ Y ≅ X ⋙ (J ⋙ R)) (he : e = Adjunction.compForgetIso o p) (K : A) :
    e.hom.app K = p.hom.app (J.obj K) ≫ R.map (o.hom.app K) := by
  subst e
  simp only [Adjunction.compForgetIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Evaluate compactification base change by applying proper base change to the extended
complex, then pushing forward the component of open base change. -/
theorem exactCompactificationExchange_app {U V : Scheme.{u}} {f : U ⟶ V}
    (d : Compactification f) {x : U ⟶ U} {z : d.Z ⟶ d.Z} {y : V ⟶ V}
    [WeaklyEtale z] [WeaklyEtale y] (hi : IsPullback d.i x z d.i) (hg : IsPullback z d.g d.g y)
    (K : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u+1}) (condensedRingObj Λ U))) :
    let J := (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory
    let R := (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor
    (rightDerivedLowerShriekOfCompactificationBaseChangeIso Λ d d hi hg).hom.app K =
      (rightDerivedLowerStarBaseChangeIso Λ hg).hom.app (J.obj K) ≫
        R.map ((openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ hi).hom.app K) := by
  intro J R
  exact compExchange_app J R (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ hi)
    (rightDerivedLowerStarBaseChangeIso Λ hg)
    (rightDerivedLowerShriekOfCompactificationBaseChangeIso Λ d d hi hg) rfl K

end WeilII.NativePointShriek
