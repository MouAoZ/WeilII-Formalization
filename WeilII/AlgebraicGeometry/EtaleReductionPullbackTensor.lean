module

public import WeilII.AlgebraicGeometry.EtaleReductionTensorComparison
import WeilII.AlgebraicGeometry.EtaleReductionPullbackMate
import WeilII.AlgebraicGeometry.EtaleScalarExtensionPullbackTensor
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison

/-! # Scalar reduction preserves the tensor comparison of étale pullback -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace WeilII

variable {A B : Type (u+1)} [CommRing A] [CommRing B]
  {ρ : A →+* B} (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
  {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- The pullback exchange for scalar reduction intertwines the two derived tensor comparisons. -/
theorem etaleScalarReduction_pullbackTensor :
    letI := derivedExtendScalarsMonoidal hρ ha Z
    letI := derivedExtendScalarsMonoidal hρ ha X
    Adjunction.ComparisonCompatible (derivedExtendScalarsPullbackIso hρ ha i).symm
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u+1} A) i)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u+1} B) i)
      (asIso (Functor.OplaxMonoidal.δNatTrans (derivedExtendScalars hρ ha Z)))
      (asIso (Functor.OplaxMonoidal.δNatTrans (derivedExtendScalars hρ ha X))) := by
  rw [etaleScalarReduction_pullbackIso_eq hρ ha i,
    leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison (ModuleCat.{u+1} A) i,
    leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison (ModuleCat.{u+1} B) i,
    etaleScalarReduction_tensorComparison_eq hρ ha Z, etaleScalarReduction_tensorComparison_eq hρ ha X]
  exact etaleScalarExtension_pullbackTensor ρ i

end WeilII
