module

public import WeilConjectures.CategoryTheory.DerivedCategory.FreeComparisonMapDerivedCategory
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedStrSingleShift

/-! # Computing the change-of-model forgetful comparison on single complexes -/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

namespace WeilII.ExternalProduct

/-- On a single Weil object the derived change-of-model forgetful comparison followed
by the native single charts equals the single charts in the transported model.
The ordinary forgetful square commutes definitionally. -/
theorem forgetComparison_single
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {F : C ⥤ C} {G : D ⥤ D} [F.Additive] [G.Additive] [F.IsEquivalence] [G.IsEquivalence]
    {E : C ⥤ D} [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory (IsoAlgebra F)] [HasDerivedCategory (IsoAlgebra G)]
    (e : E ⋙ G ≅ F ⋙ E) (I : IsoAlgebra F) :
    let T := IsoAlgebra.mapOfNatIso e
    let V := IsoAlgebra.forget F
    let W := IsoAlgebra.forget G
    let c := IsoAlgebra.mapOfNatIsoCompForgetIso e
    let x := (DerivedCategory.singleFunctor _ 0).obj I
    (Functor.mapDerivedCategoryCompForgetIso c).hom.app x ≫
        E.mapDerivedCategory.map ((V.mapDerivedCategorySingleFunctor 0).hom.app I) ≫
        (E.mapDerivedCategorySingleFunctor 0).hom.app I.carrier =
      W.mapDerivedCategory.map ((T.mapDerivedCategorySingleFunctor 0).hom.app I) ≫
        (W.mapDerivedCategorySingleFunctor 0).hom.app (T.obj I) := by
  intro T V W c x
  let _ := comp_preservesFiniteLimits T W
  let _ := comp_preservesFiniteColimits T W
  have hv := Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor V E (T ⋙ W) c I
  have hw := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor T W I
  let α := (Functor.mapDerivedCategoryCompIso T W).app x
  change (α.hom ≫ (Functor.mapDerivedCategoryNatIso c).hom.app x ≫
    (Functor.mapDerivedCategoryCompIso V E).inv.app x) ≫ _ ≫ _ = _
  simp only [Category.assoc]
  erw [hv]
  change _ ≫ _ ≫ (DerivedCategory.singleFunctor D 0).map (𝟙 _) = _
  erw [(DerivedCategory.singleFunctor D 0).map_id, Category.comp_id, ← hw]
  exact α.hom_inv_id_assoc _

end WeilII.ExternalProduct
