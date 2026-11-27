module

public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided

/-! # The bounded exceptional projection for a specified compactification -/

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilII

universe u

/-- Bundle the exceptional projection for a specified compactification using its naturality
in the complex and the coefficient. -/
@[expose] public noncomputable def compactifiedExceptionalProjection
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
    [Fact (ringChar Ω ≠ ℓ)] {U V : Over (Spec (.of Ω))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (f : U ⟶ V) (c : Compactification f.left) :
    curriedTensorInsertFunctor₁ (boundedConstructibleLowerShriekOfCompactification ℓ c) ⟶
      curriedTensorPost (boundedConstructibleLowerShriekOfCompactification ℓ c) ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f) where
  app A := {
    app B := ObjectProperty.homMk
      (exceptionalProjectionMorphismOfCompactification (Profinite.padicAlgClRingObj ℓ) c A.obj B.obj)
    naturality _ _ h := boundedConstructibleExceptionalProjectionMorphismOfCompactification_natural_right ℓ f c A h }
  naturality _ _ h := NatTrans.ext <| funext fun B ↦
    boundedConstructibleExceptionalProjectionMorphismOfCompactification_natural_left ℓ f c h B

end WeilII
