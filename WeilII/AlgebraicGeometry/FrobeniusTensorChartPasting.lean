module

public import WeilII.AlgebraicGeometry.NativeTensorGeneratorsOfEquivariance
import WeilII.CategoryTheory.TensorEquivariantChartPasting
public import WeilII.AlgebraicGeometry.SingleRelativeTensorFrobenius

/-! # Pasting Frobenius squares in the single chart of a relative tensor -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Endofunctor AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct

open CompactSupportClasses AlgebraicGeometry.ProEtale.CondensedRing

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The two factor charts determine the action on the generators of their tensor chart. -/
theorem generators_of_factor_charts (F G : WeilSheaf k ℓ X) (hF : F.IsLisse) :
    let H := pull (ℓ := ℓ) (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
    letI : H.Monoidal := CondensedRing.monoidal_leftDerivedUpperStar _ _
    let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
    let flatTensor := (IsAdicLisseSheaf.isLocallyFree hF).singleFunctorTensorObjIso
      (E.obj G.obj.carrier) 0
    ∀ {U V I J : DerivedCategory (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber)}
      (a : U ≅ S.obj (E.obj F.obj.carrier)) (b : V ≅ S.obj (E.obj G.obj.carrier))
      (d : H.obj U ⟶ I) (e : H.obj V ⟶ J) (c : I ⟶ U) (c' : J ⟶ V)
      (z : U ⊗ V ≅ S.obj (E.obj ((Mod.tensorLeft G.obj.carrier).obj F.obj.carrier)))
      (w : H.obj (U ⊗ V) ⟶ U ⊗ V),
      z = tensorIso a b ≪≫ flatTensor ≪≫
        S.mapIso (condensedRelativeTensorIso ℓ _ F.obj.carrier G.obj.carrier).symm →
      H.map a.hom ≫ singleFrobenius F.obj = d ≫ c ≫ a.hom →
      H.map b.hom ≫ singleFrobenius G.obj = e ≫ c' ≫ b.hom →
      w = Functor.OplaxMonoidal.δ H U V ≫ (d ⊗ₘ e) ≫ (c ⊗ₘ c') →
      ActsOnTensorGenerators F.obj G.obj z w := by
  intro H E S flatTensor U V I J a b d e c c' z w hz hp hs hw
  subst z
  let _ : H.Monoidal := CondensedRing.monoidal_leftDerivedUpperStar _ _
  let T := ProEtaleWeilSheaf.tensor k ℓ X G.obj F.obj
  let i := (condensedRelativeTensorIso ℓ _ F.obj.carrier G.obj.carrier).symm
  let m := flatTensor.hom ≫ S.map i.hom
  have ht := singleRelativeTensor_frobenius F G hF
  have pasted := pasteTensorActions H (A := U) (B := V) (A' := S.obj (E.obj F.obj.carrier))
    (B' := S.obj (E.obj G.obj.carrier)) (T := S.obj (E.obj T.carrier)) (P := I) (Q := J)
    a.hom b.hom m (singleFrobenius T) (singleFrobenius F.obj) (singleFrobenius G.obj)
    d e c c' ht hp hs
  apply actsOnTensorGenerators_of_square
  subst w
  exact pasted

end WeilII.ExternalProduct
