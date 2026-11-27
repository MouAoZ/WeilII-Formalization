module

public import WeilII.AlgebraicGeometry.WeilSingleFrobenius

/-! # Frobenius pullback of a degree-zero condensed module -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct
open CompactSupportClasses

universe u
variable {ℓ : ℕ} [Fact ℓ.Prime]
set_option quotPrecheck false
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "U" => CondensedRing.upperStar Λ
local notation "S" X => DerivedCategory.singleFunctor (Coeff ℓ X) 0
local notation "λ₀" f => (U f).singleFunctorCompLeftDerivedFunctorIso.hom

private theorem whiskerChange {C D : Type*} [Category* C] [Category* D]
    (J : C ⥤ D) {H F G : D ⥤ D} {V₀ R : C ⥤ C} (d : H ≅ F) (t : F ≅ G)
    (c : J ⋙ G ≅ R ⋙ J) (b : J ⋙ F ≅ V₀ ⋙ J) (v : V₀ ≅ R) (x : C)
    (ht : t.hom.app (J.obj x) ≫ c.hom.app x = b.hom.app x ≫ J.map (v.hom.app x)) :
    (Functor.isoWhiskerLeft J (d ≪≫ t) ≪≫ c).hom.app x =
      (Functor.isoWhiskerLeft J d ≪≫ b).hom.app x ≫ J.map (v.hom.app x) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc, ht]

/-- On a degree-zero coefficient module, the comparison with inverse pushforward
is the exact pullback comparison followed by the ordinary upper-to-lower isomorphism. -/
theorem singleLowerStarIso_hom_app {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (x : Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) :
    let γ := (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
    (singleLowerStarIso (k := k) (X := X)).hom.app x =
      (λ₀ γ.hom).app x ≫ (S (X ↘ Spec (.of k)).geometricFiber).map
        ((CondensedRing.upperStarIsoLowerStarInv Λ γ).hom.app x) := by
  intro γ
  let t := CondensedRing.upperStarIsoLowerStarInv Λ γ
  let R := CondensedRing.lowerStar Λ γ.inv
  exact whiskerChange _ (U γ.hom).leftDerivedFunctorIsoMapDerivedCategory
    (Functor.mapDerivedCategoryNatIso t) (R.mapDerivedCategorySingleFunctor 0)
    ((U γ.hom).mapDerivedCategorySingleFunctor 0) t x
    (Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor t x)

end WeilII.ExternalProduct
