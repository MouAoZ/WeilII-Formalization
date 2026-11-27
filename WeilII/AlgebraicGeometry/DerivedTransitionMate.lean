module

public import WeilII.AlgebraicGeometry.DerivedTransitionSquare
public import WeilII.AlgebraicGeometry.TransitionMate

/-! # Naturality of derived evaluation and restriction mates -/

public section
open CategoryTheory Limits

namespace WeilII

/-- The equation obtained by comparing the localized transitions under the three adjunctions. -/
def DerivedTransitionMateEquation
    {C D S₀ S₁ T₀ T₁ : Type*}
    [Category C] [Category D] [Category S₀] [Category S₁] [Category T₀] [Category T₁]
    [Abelian C] [Abelian D] [Abelian S₀] [Abelian S₁] [Abelian T₀] [Abelian T₁]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory S₀] [HasDerivedCategory S₁] [HasDerivedCategory T₀] [HasDerivedCategory T₁]
    {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A₀ : C ⥤ S₀} [A₀.Additive] [PreservesFiniteLimits A₀] [PreservesFiniteColimits A₀]
    {A₁ : C ⥤ S₁} [A₁.Additive] [PreservesFiniteLimits A₁] [PreservesFiniteColimits A₁]
    {B₀ : D ⥤ T₀} [B₀.Additive] [PreservesFiniteLimits B₀] [PreservesFiniteColimits B₀]
    {B₁ : D ⥤ T₁} [B₁.Additive] [PreservesFiniteLimits B₁] [PreservesFiniteColimits B₁]
    {F₀ : S₀ ⥤ T₀} [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    {F₁ : S₁ ⥤ T₁} [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    {P : S₀ ⥤ S₁} [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {Q : T₀ ⥤ T₁} [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (v₀ : F ⋙ B₀ ≅ A₀ ⋙ F₀) (v₁ : F ⋙ B₁ ≅ A₁ ⋙ F₁)
    (w : P ⋙ F₁ ≅ F₀ ⋙ Q) (s : A₁ ⟶ A₀ ⋙ P) (t : B₁ ⟶ B₀ ⋙ Q)
    {R : DerivedCategory D ⥤ DerivedCategory C}
    {R₀ : DerivedCategory T₀ ⥤ DerivedCategory S₀} {R₁ : DerivedCategory T₁ ⥤ DerivedCategory S₁}
    (adj : F.mapDerivedCategory ⊣ R) (adj₀ : F₀.mapDerivedCategory ⊣ R₀)
    (adj₁ : F₁.mapDerivedCategory ⊣ R₁) (Y : DerivedCategory D) : Prop :=
    let ea := mateEquiv adj adj₀ (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso v₀).inv)
    let eb := mateEquiv adj adj₁ (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso v₁).inv)
    let k := mateEquiv adj₀ adj₁ (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso w).hom)
    (Functor.mapDerivedCategoryNatTrans s ≫ (Functor.mapDerivedCategoryCompIso A₀ P).inv).app (R.obj Y) ≫
        P.mapDerivedCategory.map (ea.app Y) ≫ k.app (B₀.mapDerivedCategory.obj Y) =
      eb.app Y ≫ R₁.map ((Functor.mapDerivedCategoryNatTrans t ≫
        (Functor.mapDerivedCategoryCompIso B₀ Q).inv).app Y)

/-- A commuting square of ordinary transitions satisfies the equation on derived right adjoints. -/
theorem derivedTransition_mate_of_commutative_square
    {C D S₀ S₁ T₀ T₁ : Type*}
    [Category C] [Category D] [Category S₀] [Category S₁] [Category T₀] [Category T₁]
    [Abelian C] [Abelian D] [Abelian S₀] [Abelian S₁] [Abelian T₀] [Abelian T₁]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory S₀] [HasDerivedCategory S₁] [HasDerivedCategory T₀] [HasDerivedCategory T₁]
    {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A₀ : C ⥤ S₀} [A₀.Additive] [PreservesFiniteLimits A₀] [PreservesFiniteColimits A₀]
    {A₁ : C ⥤ S₁} [A₁.Additive] [PreservesFiniteLimits A₁] [PreservesFiniteColimits A₁]
    {B₀ : D ⥤ T₀} [B₀.Additive] [PreservesFiniteLimits B₀] [PreservesFiniteColimits B₀]
    {B₁ : D ⥤ T₁} [B₁.Additive] [PreservesFiniteLimits B₁] [PreservesFiniteColimits B₁]
    {F₀ : S₀ ⥤ T₀} [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    {F₁ : S₁ ⥤ T₁} [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    {P : S₀ ⥤ S₁} [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    {Q : T₀ ⥤ T₁} [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (v₀ : F ⋙ B₀ ≅ A₀ ⋙ F₀) (v₁ : F ⋙ B₁ ≅ A₁ ⋙ F₁)
    (w : P ⋙ F₁ ≅ F₀ ⋙ Q) (s : A₁ ⟶ A₀ ⋙ P) (t : B₁ ⟶ B₀ ⋙ Q)
    (hs : ∀ X, v₁.hom.app X ≫ F₁.map (s.app X) ≫ w.hom.app (A₀.obj X) =
      t.app (F.obj X) ≫ Q.map (v₀.hom.app X))
    {R : DerivedCategory D ⥤ DerivedCategory C}
    {R₀ : DerivedCategory T₀ ⥤ DerivedCategory S₀} {R₁ : DerivedCategory T₁ ⥤ DerivedCategory S₁}
    (adj : F.mapDerivedCategory ⊣ R) (adj₀ : F₀.mapDerivedCategory ⊣ R₀)
    (adj₁ : F₁.mapDerivedCategory ⊣ R₁) (Y : DerivedCategory D) :
    DerivedTransitionMateEquation v₀ v₁ w s t adj adj₀ adj₁ Y :=
  transition_mate_of_left_square adj adj₀ adj₁ (Functor.mapDerivedCategorySquareIso v₀).inv
    (Functor.mapDerivedCategorySquareIso v₁).inv (Functor.mapDerivedCategorySquareIso w).hom
    (Functor.mapDerivedCategoryNatTrans s ≫ (Functor.mapDerivedCategoryCompIso A₀ P).inv)
    (Functor.mapDerivedCategoryNatTrans t ≫ (Functor.mapDerivedCategoryCompIso B₀ Q).inv)
    (mapDerivedCategory_transition_square v₀ v₁ w s t hs) Y

end WeilII
