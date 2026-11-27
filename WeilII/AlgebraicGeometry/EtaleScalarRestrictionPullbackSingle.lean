module

-- Use the commutative-ring module category instance of the scalar adjunction.
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Restriction of coefficients and geometric pullback on a single complex -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

open CategoryTheory.Limits in
private theorem exactSquare_single
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : A ⥤ B) (P : B ⥤ D) (H : A ⥤ C) (V : C ⥤ D)
    [U.Additive] [P.Additive] [H.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (s : U ⋙ P ≅ H ⋙ V) (M : A) :
    (Functor.mapDerivedCategorySquareIso s).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      V.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (H.obj M) =
    P.mapDerivedCategory.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (P.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
      (DerivedCategory.singleFunctor D 0).map (s.hom.app M) := by
  unfold Functor.mapDerivedCategorySquareIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U P).inv.app
    ((DerivedCategory.singleFunctor A 0).obj M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  erw [reassoc_of% (Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor U P M)]

-- Normalize the two exact single squares and the full derived-limit cone equation.

private theorem pasteExact {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : D ⥤ E) {P L : C ⥤ E} (e : L ≅ P)
    {M N : C} {A B Z : D} {T W : E} (b : A ≅ B) (t : B ⟶ Z) (v : F.obj Z ⟶ T)
    (u : M ⟶ N) (q : P.obj M ⟶ F.obj B) (a : P.obj N ⟶ W) (x : W ⟶ T)
    (sq : q ≫ F.map t ≫ v = P.map u ≫ a ≫ x) :
    (e.hom.app M ≫ q ≫ F.map b.inv) ≫ F.map (b.hom ≫ t) ≫ v =
        L.map u ≫ (e.hom.app N ≫ a) ≫ x := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc, b.inv_hom_id, F.map_id, Category.id_comp, sq, e.hom.naturality_assoc]

open CategoryTheory.Limits in
private theorem exactPullSingle
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : A ⥤ B) (P : B ⥤ D) (H : A ⥤ C) (V : C ⥤ D)
    [U.Additive] [P.Additive] [H.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (s : U ⋙ P ≅ H ⋙ V)
    {LP : _root_.DerivedCategory B ⥤ _root_.DerivedCategory D}
    {LH : _root_.DerivedCategory A ⥤ _root_.DerivedCategory C}
    (p : LP ≅ P.mapDerivedCategory) (h : LH ≅ H.mapDerivedCategory) (M : A) :
    (Functor.isoWhiskerLeft U.mapDerivedCategory p ≪≫ Functor.mapDerivedCategorySquareIso s ≪≫
        Functor.isoWhiskerRight h.symm V.mapDerivedCategory).hom.app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ≫
      V.mapDerivedCategory.map ((Functor.isoWhiskerLeft (_root_.DerivedCategory.singleFunctor _ 0) h ≪≫
        H.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app (H.obj M) =
      LP.map ((U.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (Functor.isoWhiskerLeft (_root_.DerivedCategory.singleFunctor _ 0) p ≪≫
          P.mapDerivedCategorySingleFunctor 0).hom.app (U.obj M) ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map (s.hom.app M) := by
  exact pasteExact V.mapDerivedCategory p (h.app _)
    ((H.mapDerivedCategorySingleFunctor 0).hom.app M) _ ((U.mapDerivedCategorySingleFunctor 0).hom.app M)
    _ _ _ (exactSquare_single U P H V s M)
variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (ρ : A →+* B)
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- On a sheaf in degree zero, the derived exchange for restriction of scalars
is the degree-zero image of the ordinary exchange. -/
theorem etaleRestrictScalarsPullback_single (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (leftDerivedUpperStarRestrictScalarsIso ρ f).hom.app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj N) ≫
        (Sheaf.derivedRestrictScalars _ ρ).map
          ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} B) f).hom.app N) ≫
        ((Sheaf.restrictScalars _ ρ).mapDerivedCategorySingleFunctor 0).hom.app _ =
      (L((f)^*[ModuleCat.{u + 1} A])).map
          (((Sheaf.restrictScalars _ ρ).mapDerivedCategorySingleFunctor 0).hom.app N) ≫
        (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).hom.app _ ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map ((upperStarRestrictScalarsIso ρ f).hom.app N) := exactPullSingle (Sheaf.restrictScalars _ ρ) ((f)^*[ModuleCat.{u + 1} A])
      ((f)^*[ModuleCat.{u + 1} B]) (Sheaf.restrictScalars _ ρ) (upperStarRestrictScalarsIso ρ f)
      (leftDerivedUpperStarIsoMapDerivedCategory _ f) (leftDerivedUpperStarIsoMapDerivedCategory _ f) N

end WeilII
