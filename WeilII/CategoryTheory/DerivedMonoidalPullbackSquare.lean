module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalOfIso
import WeilII.CategoryTheory.TensorComparisonReverse

/-! # Monoidal compatibility of a square with left-derived composite counit -/

@[expose] public section

universe u u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Functor
open MonoidalCategory DerivedCategory

namespace WeilII

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {D' : Type u₃} [Category.{u + 1} D'] [Abelian D'] [IsGrothendieckAbelian.{u + 1} D']
  [MonoidalCategory D'] [MonoidalPreadditive D'] [MonoidalClosed D'] [BraidedCategory D']
  [HasFunctorialFlatResolution D']
  {E : Type u₄} [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [HasFunctorialFlatResolution E]

/-- If one composite represents its total left derived functor, a monoidal exchange
compatible with the composite counits commutes with the derived tensor comparisons.
Both scalar functors may be nonexact. -/
theorem derivedMonoidalPullbackSquare
    (F₁ : C ⥤ D) [F₁.Additive] [F₁.PreservesKFlatQuasiIso] [F₁.PreservesFlat]
    [F₁.IsLeftAdjoint] [F₁.Monoidal]
    (F₂ : D ⥤ E) [F₂.Additive] [F₂.PreservesKFlatQuasiIso] [F₂.PreservesFlat]
    [F₂.IsLeftAdjoint] [F₂.Monoidal]
    (G₁ : C ⥤ D') [G₁.Additive] [G₁.PreservesKFlatQuasiIso] [G₁.PreservesFlat]
    [G₁.IsLeftAdjoint] [G₁.Monoidal]
    (G₂ : D' ⥤ E) [G₂.Additive] [G₂.PreservesKFlatQuasiIso] [G₂.PreservesFlat]
    [G₂.IsLeftAdjoint] [G₂.Monoidal] [(F₁ ⋙ F₂).PreservesKFlatQuasiIso]
    (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) [NatTrans.IsMonoidal τ.hom]
    (α : G₁.leftDerivedFunctor ⋙ G₂.leftDerivedFunctor ≅
      F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor)
    (ξ : Qh ⋙ F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor ⟶
      F₁.mapHomotopyCategory (.up ℤ) ⋙ F₂.mapHomotopyCategory (.up ℤ) ⋙ Qh)
    [(F₁.leftDerivedFunctor ⋙ F₂.leftDerivedFunctor).IsLeftDerivedFunctor ξ
      (HomotopyCategory.quasiIso _ (.up ℤ))]
    (hξ : ∀ Y, ξ.app Y = F₂.leftDerivedFunctor.map (F₁.leftDerivedFunctorCounit.app Y) ≫
      F₂.leftDerivedFunctorCounit.app ((F₁.mapHomotopyCategory (.up ℤ)).obj Y))
    (hα : ∀ X, α.hom.app (Qh.obj X) ≫
        F₂.leftDerivedFunctor.map (F₁.leftDerivedFunctorCounit.app X) ≫
          F₂.leftDerivedFunctorCounit.app ((F₁.mapHomotopyCategory (.up ℤ)).obj X) =
      G₂.leftDerivedFunctor.map (G₁.leftDerivedFunctorCounit.app X) ≫
        G₂.leftDerivedFunctorCounit.app ((G₁.mapHomotopyCategory (.up ℤ)).obj X) ≫
          Qh.map ((NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app X)) :
    Adjunction.ComparisonCompatible α.symm G₁.leftDerivedTensorComparison
      F₂.leftDerivedTensorComparison (asIso G₂.leftDerivedTensorComparison)
      (asIso F₁.leftDerivedTensorComparison) := by
  let v := mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)
  let β := leftDerivedNatIso _ (F₁ ⋙ F₂).leftDerivedFunctor ξ (F₁ ⋙ F₂).leftDerivedFunctorCounit
    (HomotopyCategory.quasiIso _ (.up ℤ)) (isoWhiskerRight v Qh)
  apply tensorComparisonCompatible_of_reverse α
  intro K M
  apply map_leftDerivedTensorComparison_comp_eq_of_counit_of_iso F₁ F₂ G₁ G₂ τ α β.hom hα
  intro Y
  have hc := leftDerivedNatTrans_app _ (F₁ ⋙ F₂).leftDerivedFunctor ξ
    (F₁ ⋙ F₂).leftDerivedFunctorCounit (HomotopyCategory.quasiIso _ (.up ℤ))
    (whiskerRight v.hom Qh) Y
  rw [hξ, Category.assoc] at hc
  exact hc

end WeilII
