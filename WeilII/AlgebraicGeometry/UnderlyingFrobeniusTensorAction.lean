module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceInputs
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # The ambient component of a bounded pullback tensor action -/

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct

universe u

/-- On underlying objects the bounded pullback tensor constraint, followed by two tensor
morphisms, is the corresponding composition in the ambient derived category. -/
public theorem boundedPullbackTensorAction_hom
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (P : Over (Spec (.of k))) [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (v : P.left ⟶ P.left) (U V I J : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (d : (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P) v).obj U ⟶ I)
    (e : (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P) v).obj V ⟶ J)
    (c : I ⟶ U) (c' : J ⟶ V) :
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ) P).toMonoidalCategoryStruct
    letI : L((v)^*⟦Profinite.padicAlgClRingObj ℓ⟧).Monoidal := monoidal_leftDerivedUpperStar _ _
    (Functor.OplaxMonoidal.δ (boundedConstructibleUpperStarOfMap ℓ (X := P) (Y := P) v) U V ≫
      (d ⊗ₘ e) ≫ (c ⊗ₘ c')).hom =
      Functor.OplaxMonoidal.δ L((v)^*⟦Profinite.padicAlgClRingObj ℓ⟧) U.obj V.obj ≫
        (d.hom ⊗ₘ e.hom) ≫ (c.hom ⊗ₘ c'.hom) := by
  rfl

end WeilII.ExternalProduct
