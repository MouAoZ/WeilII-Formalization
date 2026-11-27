module

public import WeilII.AlgebraicGeometry.EtalePositiveTateReductionPullback
public import WeilII.AlgebraicGeometry.EtaleTateReductionShiftPullback

/-! # The positive Tate comparison in supported coefficient reduction -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

/-- The positive Tate comparison in the supported change of coefficients is the
shift by two of the roots-of-unity power map in the first Kummer component. -/
theorem etaleDivisorPositiveTatePowerComparison {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {ρ : A →+* B} (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    [Finite A] [Finite B] [NeZero (ringChar A)] [NeZero (ringChar B)] {V : Scheme.{u}}
    [HasInvertibleExponent A V] [HasInvertibleExponent B V]
    {C : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : C ⟶ V.gmSheaf)
    {d : ℕ} (hd : ringChar A = ringChar B * d) :
    letI := derivedExtendScalarsCommShift hρ ha V
    let Ψ := derivedExtendScalars hρ ha V
    let Φ := reductionSupportedCoefficientChange hρ ha (reductionTateShiftData hρ ha)
    (Φ.tateShiftIso V 1).hom =
      (Ψ.commShiftIso (2 : ℤ)).hom.app _ ≫
        (Ψ.map (tateTwistObjectOneIso V A).hom ≫
          ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
            (derivedExtendScalarsAdjunction hρ ha V) (kummerSequenceReductionMap ρ φ hd).τ₁ ≫
          (tateTwistObjectOneIso V B).inv)⟦(2 : ℤ)⟧' := by
  let := derivedExtendScalarsCommShift hρ ha V
  let S := invertibleExponentBase.{u} A
  let t := toInvertibleExponentBase (Λ := A) V
  have : HasInvertibleExponent B S := HasInvertibleExponent.of_ringHom ρ S
  have h := etaleTateReductionPullback_shift t hρ ha (positiveTateObjectReduction_pullback t hρ ha hd)
  let Ψ := derivedExtendScalars hρ ha V
  let T := leftDerivedUpperStarTateShiftIso A t 1
  let E := (derivedExtendScalarsTateShiftIso hρ ha V 1).hom
  let K := (derivedExtendScalarsPullbackIso hρ ha t).hom.app ((tateObject A S 1)⟦(2 : ℤ)⟧) ≫
    L((t)^*[ModuleCat.{u + 1} B]).map (derivedExtendScalarsTateShiftIso hρ ha S 1).hom ≫
      (leftDerivedUpperStarTateShiftIso B t 1).hom
  have h' : K = Ψ.map T.hom ≫ E := h
  change Ψ.map T.inv ≫ K = _
  rw [h', ← Ψ.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun z ↦ (Ψ.commShiftIso (2 : ℤ)).hom.app (tateObject A V 1) ≫
    (shiftFunctor _ (2 : ℤ)).map z) (positiveTateObjectReduction_eq_kummer φ hd hρ ha)

end WeilII
