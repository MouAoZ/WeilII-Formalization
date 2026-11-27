module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Comparing a single morphism in the two presentations of the derived category -/

open CategoryTheory CategoryTheory.Limits DerivedCategory

namespace WeilII

/-- The comparison from a single complex to its image through the homotopy category
intertwines the exact functor's single comparison with its factorization through Qh. -/
public theorem derivedSingleHomotopyDatum
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (P : C ⥤ D) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] {A : C} {B : D} (v : P.obj A ⟶ B) :
    let K := (HomologicalComplex.single C (.up ℤ) 0).obj A
    let M := (HomologicalComplex.single D (.up ℤ) 0).obj B
    P.mapDerivedCategory.map ((quotientCompQhIso C).inv.app K) ≫
      P.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) ≫
      Qh.map (Functor.mapHomotopyCategorySingleHom P v) =
    (P.mapDerivedCategorySingleFunctor 0).hom.app A ≫ (singleFunctor D 0).map v ≫
      (quotientCompQhIso D).inv.app M := by
  intro K M
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, Functor.mapHomotopyCategorySingleHom,
    Qh.map_comp]
  simp only [Category.assoc, ← P.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    P.mapDerivedCategory.map_id, Category.id_comp, ← Qh.map_comp_assoc]
  dsimp only [K]
  erw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    ← quotientCompQhIso_inv_naturality]
  rw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
  simp only [Category.assoc, Functor.map_comp]
  rfl

end WeilII
