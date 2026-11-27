module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Braiding of bounded constructible pullback along a map of underlying schemes -/

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

attribute [local instance] boundedConstructibleBraiding

/-- The tensor comparison for pullback along an underlying scheme map respects braiding,
even when the two schemes are presented over different fields. Both the pullback and its
tensor comparison restrict the ambient ones, as do the two Koszul braidings. Thus the
ambient braided pullback equality in the pinned `BoundedConstructibleMonoidalComp.lean`
gives the result by faithfulness of the full-subcategory inclusion. -/
public theorem boundedConstructibleUpperStarOfMap_braiding
    {k₁ k₂ : Type u} [Field k₁] [Field k₂] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
    [Fact (ringChar k₂ ≠ ℓ)] (X : Over (Spec (.of k₁))) (Y : Over (Spec (.of k₂)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (t : Y.left ⟶ X.left) (A B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    let F := boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := Y) t
    F.map (β_ A B).hom ≫ Functor.OplaxMonoidal.δ F B A =
      Functor.OplaxMonoidal.δ F A B ≫ (β_ (F.obj A) (F.obj B)).hom := by
  intro F
  apply ObjectProperty.hom_ext (P := boundedConstructible _)
  simp only [ObjectProperty.FullSubcategory.comp_hom, F, boundedConstructibleUpperStarOfMap_map,
    boundedConstructible_braiding_hom_hom]
  simp only [boundedConstructibleUpperStarOfMap, ObjectProperty.monoidalLift_δ_hom,
    ObjectProperty.lift_obj_obj, Functor.comp_obj, ObjectProperty.ι_obj]
  exact leftDerivedUpperStar_map_braiding_hom_δ (Profinite.padicAlgClRingObj ℓ) t A.obj B.obj

end WeilII
