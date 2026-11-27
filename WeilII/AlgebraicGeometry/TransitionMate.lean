module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Naturality of evaluation mates along a transition -/

public section

open CategoryTheory

namespace WeilII

/-- For two evaluations of an adjunction, compatibility of a transition with the
left adjoints implies compatibility with the evaluation and restriction mates of
the right adjoints. This is the counit form of the pasting rule for mates. -/
theorem transition_mate_of_left_square
    {C D S₀ S₁ T₀ T₁ : Type*}
    [Category* C] [Category* D] [Category* S₀] [Category* S₁] [Category* T₀] [Category* T₁]
    {F : C ⥤ D} {R : D ⥤ C} {F₀ : S₀ ⥤ T₀} {R₀ : T₀ ⥤ S₀}
    {F₁ : S₁ ⥤ T₁} {R₁ : T₁ ⥤ S₁}
    (adj : F ⊣ R) (adj₀ : F₀ ⊣ R₀) (adj₁ : F₁ ⊣ R₁)
    {A₀ : C ⥤ S₀} {A₁ : C ⥤ S₁} {B₀ : D ⥤ T₀} {B₁ : D ⥤ T₁}
    {P : S₀ ⥤ S₁} {Q : T₀ ⥤ T₁}
    (v₀ : A₀ ⋙ F₀ ⟶ F ⋙ B₀) (v₁ : A₁ ⋙ F₁ ⟶ F ⋙ B₁)
    (w : P ⋙ F₁ ⟶ F₀ ⋙ Q) (s : A₁ ⟶ A₀ ⋙ P) (t : B₁ ⟶ B₀ ⋙ Q)
    (hs : ∀ X, F₁.map (s.app X) ≫ w.app (A₀.obj X) ≫ Q.map (v₀.app X) =
      v₁.app X ≫ t.app (F.obj X)) (Y : D) :
    s.app (R.obj Y) ≫ P.map ((mateEquiv adj adj₀ v₀).app Y) ≫
        (mateEquiv adj₀ adj₁ w).app (B₀.obj Y) =
      (mateEquiv adj adj₁ v₁).app Y ≫ R₁.map (t.app Y) := by
  apply (adj₁.homEquiv _ _).symm.injective
  have h₀ := mateEquiv_counit adj adj₀ v₀ Y
  have h₁ := mateEquiv_counit adj adj₁ v₁ Y
  have hw := mateEquiv_counit adj₀ adj₁ w (B₀.obj Y)
  have hn := w.naturality ((mateEquiv adj adj₀ v₀).app Y)
  have ht := t.naturality (adj.counit.app Y)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj] at h₀ h₁ hw hn ht
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.counit_naturality]
  rw [hw, reassoc_of% hn, ← Q.map_comp, h₀, Q.map_comp, reassoc_of% (hs (R.obj Y)),
    reassoc_of% h₁, ht]

end WeilII
