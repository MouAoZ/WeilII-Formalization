module

import WeilConjectures.Tactic.TransportExact

import WeilII.AlgebraicGeometry.CondensedFlatSingleTensorPullback
import WeilII.AlgebraicGeometry.CondensedRelativeTensorWeilSquare
import WeilII.AlgebraicGeometry.SingleFrobeniusUpperStar
import WeilII.CategoryTheory.TensorActionInSingle

public import WeilII.AlgebraicGeometry.WeilSingleFrobenius
public import WeilConjectures.WeilSheaf.Native.Projection.AdicSheafTensorSquare
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseLocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor

/-! # Frobenius on the degree-zero relative tensor of two Weil sheaves -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Endofunctor AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct

open CompactSupportClasses AlgebraicGeometry.ProEtale.CondensedRing

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Frobenius on the condensed single of the native relative tensor, in the locally free
tensor chart. Sources are `adicUpperStar_condensedRelativeTensor_square`,
`ProEtaleWeilSheaf.tensorπ_str`, and `leftDerivedUpperStarTensor_laxSquare`.

Proof. In the ordinary coefficient category apply the relative tensor square to the
geometric Frobenius automorphism. Identify its pullback with inverse pushforward using
`adicUpperStarCompCondensedModIso_inv_of_iso`. Compose with the two structure maps.
After the tensor quotient projection this is precisely `tensorπ_str`, so epimorphy
identifies the result with the structure map of the native relative tensor. Apply the
single functor to this equality. Compute the derived tensor constraint on the two
single complexes by `leftDerivedUpperStarTensor_laxSquare`. The left single and its
pullback are K-flat by local freeness, hence the localization tensor comparisons are
invertible, as are the exact pullback counits. Cancel these comparisons on the two
sides. The tensor map of the single complexes has its only nonzero bidegree at (0,0),
where it is the ordinary tensor constraint. This gives the displayed composite with
the same single-complex and relative tensor comparisons used to define the chart. -/
theorem singleRelativeTensor_frobenius (F G : WeilSheaf k ℓ X) (hF : F.IsLisse) :
    let E := (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    let S := DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
    let H := pull (ℓ := ℓ) (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
    letI : H.Monoidal := CondensedRing.monoidal_leftDerivedUpperStar _ _
    let T := ProEtaleWeilSheaf.tensor k ℓ X G.obj F.obj
    let m := ((IsAdicLisseSheaf.isLocallyFree hF).singleFunctorTensorObjIso
      (E.obj G.obj.carrier) 0).hom ≫
        S.map (condensedRelativeTensorIso ℓ _ F.obj.carrier G.obj.carrier).inv
    H.map m ≫ singleFrobenius T =
      Functor.OplaxMonoidal.δ H (S.obj (E.obj F.obj.carrier)) (S.obj (E.obj G.obj.carrier)) ≫
        (singleFrobenius F.obj ⊗ₘ singleFrobenius G.obj) ≫ m := by
  dsimp only
  have leftAction := singleFrobenius_upperStar F.obj
  have rightAction := singleFrobenius_upperStar G.obj
  have tensorAction := singleFrobenius_upperStar (ProEtaleWeilSheaf.tensor k ℓ X G.obj F.obj)
  have ordinarySquare := condensedRelativeTensorWeilSquare F.obj G.obj
  dsimp only at ordinarySquare
  have pullbackSquare := flatSingleTensorPullback (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom
    _ ((adicSheafEquivCondensedMod ℓ _).functor.obj G.obj.carrier)
    (IsAdicLisseSheaf.isLocallyFree hF)
  have chartNaturality := flatSingleTensor_naturality
    (((ProEtaleWeilSheaf.toCondensedUpperStar k ℓ X).obj F.obj).str.hom)
    (((ProEtaleWeilSheaf.toCondensedUpperStar k ℓ X).obj G.obj).str.hom)
    ((IsAdicLisseSheaf.isLocallyFree hF).upperStar (Profinite.padicAlgClRingObj ℓ)
      (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom)
    (IsAdicLisseSheaf.isLocallyFree hF)
  fo_apply (tensorActionInSingle _ _ _
    (pullTensor := (CondensedRing.monoidal_leftDerivedUpperStar (Profinite.padicAlgClRingObj ℓ)
      (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom).toOplaxMonoidal)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso.hom).singleFunctorCompLeftDerivedFunctorIso.hom)
    using leftAction, rightAction, tensorAction, ordinarySquare, pullbackSquare, chartNaturality

end WeilII.ExternalProduct
