module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # The oplax tensor comparison of a left derived functor -/

@[expose] public section

universe u u₁ u₂

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace WeilII

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]

/-- The oplax tensor transformation of a derived monoidal functor is the canonical
derived comparison of tensor bifunctors. -/
theorem leftDerivedFunctorMonoidal_tensor (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] :
    letI := F.leftDerivedFunctorMonoidal
    Functor.OplaxMonoidal.δNatTrans F.leftDerivedFunctor = F.leftDerivedTensorComparison := by
  ext K M
  exact F.leftDerivedFunctorMonoidal_δ K M

end WeilII
