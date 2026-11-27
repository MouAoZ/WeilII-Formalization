module

public import WeilII.AlgebraicGeometry.DerivedTransitionMate
import all WeilII.AlgebraicGeometry.DerivedTransitionMate

/-! # Components of the derived transition mate equation -/

public section

open CategoryTheory Limits

namespace WeilII

/-- The two paths from the upper source evaluation to the upper target right adjoint,
formed from the two transitions and the three comparison maps at `N`. -/
structure TransitionComponentEquation {C D A B A' B' : Type*}
    [Category* C] [Category* D] [Category* A] [Category* B] [Category* A'] [Category* B']
    (R : D ⥤ C) (R₀ : B ⥤ A) (R₁ : B' ⥤ A') (e₀ : C ⥤ A) (e₁ : C ⥤ A')
    (f₀ : D ⥤ B) (f₁ : D ⥤ B') (P : A ⥤ A') (Q : B ⥤ B')
    (s : e₁ ⟶ e₀ ⋙ P) (t : f₁ ⟶ f₀ ⋙ Q)
    (i : R ⋙ e₀ ⟶ f₀ ⋙ R₀) (j : R ⋙ e₁ ⟶ f₁ ⋙ R₁)
    (k : R₀ ⋙ P ⟶ Q ⋙ R₁) (N : D) : Prop where
  eq : s.app (R.obj N) ≫ P.map (i.app N) ≫ k.app (f₀.obj N) = j.app N ≫ R₁.map (t.app N)

/-- The derived mate equation gives the component equation for the localized transitions
and the evaluation and restriction mates. -/
theorem DerivedTransitionMateEquation.components
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
    (adj₁ : F₁.mapDerivedCategory ⊣ R₁) (Y : DerivedCategory D)
    (h : DerivedTransitionMateEquation v₀ v₁ w s t adj adj₀ adj₁ Y) :
    TransitionComponentEquation R R₀ R₁ A₀.mapDerivedCategory A₁.mapDerivedCategory
      B₀.mapDerivedCategory B₁.mapDerivedCategory P.mapDerivedCategory Q.mapDerivedCategory
      (Functor.mapDerivedCategoryNatTrans s ≫ (Functor.mapDerivedCategoryCompIso A₀ P).inv)
      (Functor.mapDerivedCategoryNatTrans t ≫ (Functor.mapDerivedCategoryCompIso B₀ Q).inv)
      (mateEquiv adj adj₀ (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso v₀).inv))
      (mateEquiv adj adj₁ (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso v₁).inv))
      (mateEquiv adj₀ adj₁ (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso w).hom))
      Y := ⟨h⟩


end WeilII
