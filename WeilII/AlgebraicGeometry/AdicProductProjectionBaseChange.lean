module

public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedExchangeComparison
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
import WeilConjectures.SixFunctors.ProEtale.Adic.BoundedConstructibleCondensedComparison
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstructibleStructure
import WeilII.CategoryTheory.ExchangePastingIso
import WeilII.AlgebraicGeometry.AdicBaseChangeReflectIso
import WeilConjectures.TraceFormula.GenericBaseChangePullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj

universe u

/-- Ordinary base change for the first projection of a product over a field of positive
characteristic. SGA 4½, Théorèmes de finitude 1.9 over the point. Interchanging factors
in the bounded constructible product theorem and comparing the specified exchange arrows
gives the result for a constructible native sheaf in degree zero. -/
public theorem isIso_adicProductProjectionBaseChange (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))} (T : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (h : X ⟶ Y) (K : AdicSheaf ℓ X.left) (hK : IsAdicConstructibleSheaf K) :
    IsIso ((adicDerivedBaseChange ℓ ((IsPullback.of_prod_fst_with_id h T).map
      (Over.forget _)).toCommSq).app ((DerivedCategory.singleFunctor _ 0).obj K)) := by
  classical
  let sq := IsPullback.of_prod_fst_with_id h T
  let s : CommSq (prod.braiding X T).hom (prod.map h (𝟙 T)) (prod.map (𝟙 T) h)
      (prod.braiding Y T).hom := ⟨by apply prod.hom_ext <;> simp⟩
  have hl := isIso_boundedConstructibleBaseChange_of_isIso ℓ s
  have hr := isIso_boundedConstructibleBaseChange_prodMap ℓ (X := T) h
  have hb : IsIso (boundedConstructibleBaseChange ℓ sq.toCommSq) := by
    rw [boundedConstructibleBaseChange_eq_pfBaseChange] at hl hr ⊢
    let E := boundedConstructibleExchangeFormalism ℓ k
    exact isIso_pfBaseChange_paste_horiz E (SepFinType.homMk (prod.braiding X T).hom)
      (SepFinType.homMk (prod.snd : T ⨯ X ⟶ X)) (SepFinType.homMk (prod.map h (𝟙 T)))
      (SepFinType.homMk (prod.map (𝟙 T) h)) (SepFinType.homMk h)
      (SepFinType.homMk (prod.braiding Y T).hom) (SepFinType.homMk (prod.snd : T ⨯ Y ⟶ Y))
      (SepFinType.homMk (prod.fst : X ⨯ T ⟶ X)) (SepFinType.homMk (prod.fst : Y ⨯ T ⟶ Y))
      (SepFinType.homMk_comp_homMk s.w) (SepFinType.homMk_comp_homMk (commSq_prodMap_snd h).w)
      (ObjectProperty.hom_ext _ (by simp)) (ObjectProperty.hom_ext _ (by simp))
      (SepFinType.homMk_comp_homMk sq.w) hl hr
  let Λ := Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ)
  let M := (DerivedCategory.singleFunctor _ 0).obj K
  let enc := nativeExchangeEncodingAt ℓ Λ rfl X.left
  have : enc.IsEquivalence := nativeExchangeEncodingAt_isEquivalence ..
  have : enc.Additive := nativeExchangeEncodingAt_additive ..
  let E := adicSheafEquivCondensedMod ℓ X.left
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  let B : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj (E.functor.obj K),
      (boundedConstructible_singleFunctor_obj_zero_iff _ _).2 hK.isConstructibleModuleObject⟩
  let e : enc.obj K ≅ E.functor.obj K := by
    simpa only [enc, Λ, nativeExchangeEncodingAt, nativeExchangeEncoding] using
      (forgetAbCompComapNativeModuleCoefficientIso ℓ X.left).app K
  let eM : enc.mapDerivedCategory.obj M ≅ B.obj :=
    (enc.mapDerivedCategorySingleFunctor 0).app K ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e
  exact isIso_adicBaseChange_of_condensed ℓ k Λ rfl sq M B eM hb

end WeilII
