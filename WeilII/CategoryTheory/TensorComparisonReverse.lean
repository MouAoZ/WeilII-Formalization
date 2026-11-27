module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import Mathlib.CategoryTheory.Monoidal.Category

/-! # Reversing the isomorphisms in a pullback tensor comparison -/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Functor

namespace WeilII

/-- Move the three components of a pullback isomorphism across a tensor comparison square. -/
theorem tensorComparisonCompatible_of_reverse
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
    {U : D ⥤ C} {P : D' ⥤ C'} {S : D ⥤ D'} {T : C ⥤ C'} (α : U ⋙ T ≅ S ⋙ P)
    (φ : (postcompose₂.obj U).obj (curriedTensor D) ⟶
      (((whiskeringLeft₂ C).obj U).obj U).obj (curriedTensor C))
    (φ' : (postcompose₂.obj P).obj (curriedTensor D') ⟶
      (((whiskeringLeft₂ C').obj P).obj P).obj (curriedTensor C'))
    (d : (postcompose₂.obj T).obj (curriedTensor C) ≅
      (((whiskeringLeft₂ C').obj T).obj T).obj (curriedTensor C'))
    (d' : (postcompose₂.obj S).obj (curriedTensor D) ≅
      (((whiskeringLeft₂ D').obj S).obj S).obj (curriedTensor D'))
    (h : ∀ K M, P.map ((d'.hom.app K).app M) ≫ (φ'.app (S.obj K)).app (S.obj M) =
      α.inv.app (K ⊗ M) ≫ T.map ((φ.app K).app M) ≫ (d.hom.app (U.obj K)).app (U.obj M) ≫
        (α.hom.app K ⊗ₘ α.hom.app M)) :
    Adjunction.ComparisonCompatible α.symm φ φ' d d' := by
  intro K M
  simp only [Iso.symm_inv, Iso.symm_hom, curriedTensor_obj_obj, curriedTensor_map_app,
    curriedTensor_obj_map, ← tensorHom_def]
  rw [← Category.assoc (P.map _), h]
  simp [Category.assoc, tensorHom_comp_tensorHom]

end WeilII
