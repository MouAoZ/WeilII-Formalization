module

public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange

/-! # Transport of projection base change through pushforward isomorphisms -/

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace WeilII

/-- A componentwise projection square on two pushforwards gives the projection square on
isomorphic pushforwards. Move the target isomorphism through the two coefficient maps by
naturality, use the given square, then move the source isomorphism through comultiplication. -/
public theorem transportProjectionBaseChange
    {X Y X' Y' : Type*} [Category* X] [Category* Y] [Category* X'] [Category* Y']
    [MonoidalCategory X] [MonoidalCategory Y] [MonoidalCategory X'] [MonoidalCategory Y']
    {f g : X ⥤ Y} {f' g' : X' ⥤ Y'} {t : Y ⥤ X} {t' : Y' ⥤ X'}
    (q : Y ⥤ Y') [q.Monoidal] (w : X ⥤ X') [w.Monoidal]
    (c : f ≅ g) (b : g' ≅ f') (E : g ⋙ q ≅ w ⋙ g') (D : q ⋙ t' ≅ t ⋙ w)
    (P : curriedTensorInsertFunctor₁ f ⟶ curriedTensorPost f ⋙ (Functor.whiskeringLeft _ _ _).obj t)
    (P' : curriedTensorInsertFunctor₁ f' ⟶ curriedTensorPost f' ⋙ (Functor.whiskeringLeft _ _ _).obj t')
    (C : curriedTensorInsertFunctor₁ g ⟶ curriedTensorPost g ⋙ (Functor.whiskeringLeft _ _ _).obj t)
    (C' : curriedTensorInsertFunctor₁ g' ⟶ curriedTensorPost g' ⋙ (Functor.whiskeringLeft _ _ _).obj t')
    (hc : ∀ A B, c.hom.app A ▷ B ≫ (C.app A).app B = (P.app A).app B ≫ c.hom.app (A ⊗ t.obj B))
    (hb : ∀ A B, b.hom.app A ▷ B ≫ (P'.app A).app B = (C'.app A).app B ≫ b.hom.app (A ⊗ t'.obj B))
    (h : ProjectionBaseChange.PFBaseChange q w E.hom D C C') :
    ProjectionBaseChange.PFBaseChange q w
      (Functor.isoWhiskerRight c q ≪≫ E ≪≫ Functor.isoWhiskerLeft w b).hom D P P' := by
  intro A B
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    comp_whiskerRight, Category.assoc]
  rw [← b.hom.naturality_assoc, ← b.hom.naturality,
    ← q.map_comp_assoc, ← hc, q.map_comp_assoc, hb (w.obj A) (q.obj B)]
  rw [reassoc_of% (h A B), Functor.OplaxMonoidal.δ_natural_left_assoc]
  rfl

end WeilII
