module

public import WeilII.AlgebraicGeometry.NativeSingleFrobeniusChart

/-! # Tensor generators of an equivariant single chart -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Endofunctor AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct

open CompactSupportClasses AlgebraicGeometry.ProEtale.CondensedRing

universe u

/-- Equivariance in the native single chart gives the required equality on tensor generators. -/
theorem actsOnTensorGenerators_of_square {k : Type u} [Field k] [Finite k]
    {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (F G : ProEtaleWeilSheaf k ℓ X) :
    let T := ProEtaleWeilSheaf.tensor k ℓ X G F
    let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
    let H := pull (ℓ := ℓ) (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
    ∀ {V} (a : V ≅ S.obj (E.obj T.carrier)) (g : H.obj V ⟶ V),
      H.map a.hom ≫ singleFrobenius T = g ≫ a.hom → ActsOnTensorGenerators F G a g := by
  intro T E S H V a g h
  let b := nativeSinglePullIso (k := k) (X := X) T.carrier
  have hs := (congrArg (H.map a.hom ≫ ·) (singleFrobenius_eq_native T)).symm.trans h
  have eq := (nativeChartMap_eq_iff (E ⋙ S) H a b g T.str.hom).2 hs
  unfold ActsOnTensorGenerators
  dsimp only
  rw [eq]
  exact (ProEtaleWeilSheaf.tensorπ_str F G).symm

end WeilII.ExternalProduct
