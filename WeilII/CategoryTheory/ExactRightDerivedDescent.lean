module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # Right-derived comparison for a composite of exact functors

The comparison in WeilConjectures' `RightDerivedFunctor.MapDerivedComp` is invertible when
both functors are exact. This applies to evaluation followed by a finite étale-site direct image.
-/

public section

namespace WeilII

open CategoryTheory CategoryTheory.Limits

/-- For exact functors `U` and `G`, the descent from the right derived composite to
`D(U) ⋙ RG` is an isomorphism. The unit for `RG` is invertible by exactness of `G`.
Consequently every factor in `mapDerivedCategoryCompRightDerivedFunctorUnit` is invertible.
An invertible factorization through localization exhibits a right derived functor, and
uniqueness gives the claim for the specified descent map. Source: WeilConjectures,
`RightDerivedFunctor.MapDerivedCategory`, `RightDerivedFunctor.MapDerivedComp`, and Mathlib,
`Functor.isRightDerivedFunctor_of_inverts`. -/
theorem isIso_rightDerivedDesc_of_exact
    {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (U : C ⥤ D) (G : D ⥤ E) [U.Additive] [G.Additive] [PreservesFiniteLimits U]
    [PreservesFiniteColimits U] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    IsIso ((U ⋙ G).rightDerivedFunctor.rightDerivedDesc (U ⋙ G).rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (.up ℤ)) _ (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit U G)) := by
  let η := Functor.mapDerivedCategoryCompRightDerivedFunctorUnit U G
  have : IsIso η := by
    dsimp only [η, Functor.mapDerivedCategoryCompRightDerivedFunctorUnit]
    infer_instance
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ η).1
    (Functor.isRightDerivedFunctor_of_inverts _ _ (asIso η).symm)

end WeilII
