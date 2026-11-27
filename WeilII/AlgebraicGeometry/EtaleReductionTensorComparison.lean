module

import WeilII.CategoryTheory.DerivedOplaxTensorComparison
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsDerived
public import WeilConjectures.SixFunctors.Etale.ScalarExtension.Monoidal

/-! # Tensor compatibility of the derived scalar extension -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace WeilII

variable {A B : Type (u+1)} [CommRing A] [CommRing B]
  {ρ : A →+* B} (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
  (X : Scheme.{u})

/-- The scalar reduction tensorator, as a transformation of bifunctors, is the canonical
left-derived comparison of scalar extension. Both use the monoidal structure on the
same extension functor. -/
theorem etaleScalarReduction_tensorComparison_eq :
    letI := derivedExtendScalarsMonoidal hρ ha X
    have := preservesKFlatQuasiIso_extendScalars hρ ha X
    have : (sheafExtendScalars ρ X).PreservesFlat :=
      Sheaf.preservesFlat_extendScalars X.smallEtaleTopology (f := ρ)
    asIso (Functor.OplaxMonoidal.δNatTrans (derivedExtendScalars hρ ha X)) =
      asIso (sheafExtendScalars ρ X).leftDerivedTensorComparison := by
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  have : (sheafExtendScalars ρ X).PreservesFlat :=
    Sheaf.preservesFlat_extendScalars X.smallEtaleTopology (f := ρ)
  apply Iso.ext
  exact leftDerivedFunctorMonoidal_tensor (Sheaf.extendScalars X.smallEtaleTopology ρ)

end WeilII
