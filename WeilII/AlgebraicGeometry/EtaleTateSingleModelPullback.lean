module

public import WeilConjectures.EtaleCohomology.TateTwist.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle

/-! # Pullback of the degree-zero models for integer Tate twists -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

/-- Pullback on Tate sheaves is the inverse of the composition comparison for the two
structure morphisms to the base on which the coefficient exponent is invertible. -/
noncomputable def etaleTateSheafPullbackIso (R : Type (u+1)) [CommRing R] [NeZero (ringChar R)]
    {Z X : Scheme.{u}} [HasInvertibleExponent R Z] [HasInvertibleExponent R X] (i : Z ⟶ X)
    (m : ℤ) : (i)^*[ModuleCat.{u+1} R].obj (tateTwistSheaf R X m) ≅ tateTwistSheaf R Z m :=
  ((upperStarComp _ i _ _ (comp_toInvertibleExponentBase (Λ := R) i).symm).app
    ((tateSheafTensorInverse R).zpow m)).symm

private theorem pasteSingle {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {U P Q Y : C} {T P' Q' Z J : D} (e : U ≅ P) (e' : T ≅ P')
    (s : P ⟶ Q) (t : Q ⟶ Y) (s' : P' ⟶ Q') (t' : Q' ⟶ Z)
    (a : F.obj P ⟶ P') (b : F.obj Q ⟶ Q') (c : F.obj Y ⟶ J) (v : J ⟶ Z)
    (n : F.map s ≫ b = a ≫ s') (h : F.map t ≫ c ≫ v = b ≫ t') :
    F.map (e.hom ≫ s ≫ t) ≫ c ≫ v = (F.map e.hom ≫ a ≫ e'.inv) ≫ e'.hom ≫ s' ≫ t' := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, h, reassoc_of% n]

/-- The degree-zero model of an integer Tate twist intertwines the derived and ordinary
pullbacks. This is the composition law for pullback on a single complex, applied to
the integer tensor power on the universal base. -/
theorem etaleTateSingleModel_pullback (R : Type (u+1)) [CommRing R] [NeZero (ringChar R)]
    {Z X : Scheme.{u}} [HasInvertibleExponent R Z] [HasInvertibleExponent R X] (i : Z ⟶ X)
    (m : ℤ) :
    L((i)^*[ModuleCat.{u+1} R]).map (tateTwistObjectIsoSingleFunctor R X m).hom ≫
      (singleFunctorCompLeftDerivedUpperStarIso _ i).hom.app _ ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map (etaleTateSheafPullbackIso R i m).hom =
    (leftDerivedUpperStarTateTwistObjectIso R i m).hom ≫
      (tateTwistObjectIsoSingleFunctor R Z m).hom := by
  let hπ := (comp_toInvertibleExponentBase (Λ := R) i).symm
  let W := (tateSheafTensorInverse R).zpow m
  have hG := leftDerivedUpperStar_map_singleFunctor_comp (ModuleCat.{u+1} R) i _ _ hπ W
    (𝟙 _) (𝟙 _) (etaleTateSheafPullbackIso R i m).hom (by
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
      exact (upperStarComp (ModuleCat.{u+1} R) i _ _ hπ).hom_inv_id_app W)
  have n := (leftDerivedUpperStarComp (ModuleCat.{u+1} R) i _ _ hπ).inv.naturality
    ((tateSheafTensorInverse R).zpowSingleFunctorIso m).hom
  simp only [CategoryTheory.Functor.map_id] at hG
  erw [Category.comp_id, Category.comp_id] at hG
  exact pasteSingle L((i)^*[ModuleCat.{u+1} R])
    (eqToIso (congrFun (tateTwistObject_eq R X) m))
    (eqToIso (congrFun (tateTwistObject_eq R Z) m))
    _ _ _ _ _ _ _ _ n hG

end WeilII
