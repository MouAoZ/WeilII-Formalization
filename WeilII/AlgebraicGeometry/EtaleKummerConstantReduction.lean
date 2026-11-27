module

public import WeilII.AlgebraicGeometry.EtaleSingleModelReductionPullback
public import WeilII.AlgebraicGeometry.EtaleKummerPowerPullback
import WeilII.AlgebraicGeometry.EtaleKummerSupportedUnit
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.TwistPullback
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerClass

/-! # The constant coefficient in the reduced Kummer sequence -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

variable {A B : Type (u+1)} [CommRing A] [CommRing B] {ρ : A →+* B}
  (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})

/-- The free coefficient sheaf on the integral constant sheaf is flat since it is the unit. -/
theorem etaleKummer_flatConstantInt (A : Type (u+1)) [CommRing A] (X : Scheme.{u}) :
    ObjectProperty.flat ((extendScalars A X).obj X.constantSheafInt) :=
  ObjectProperty.prop_of_iso ObjectProperty.flat (extendScalarsConstantZModIso X (Λ := A) (n := 0) (by simp)).symm
    (ObjectProperty.flat_of_tensorIso (MonoidalCategory.leftUnitor _))

/-- On the free rank-one term the derived transpose is transitivity of ordinary scalar extension
in the flat single model. -/
theorem etaleKummer_constantTranspose_flat (X : Scheme.{u}) :
    letI := preservesKFlatQuasiIso_extendScalars hρ ha X
    ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
        (derivedExtendScalarsAdjunction hρ ha X) ((extendScalarsToRestrictScalars ρ X).app X.constantSheafInt) =
      ((Sheaf.extendScalars _ ρ).leftDerivedFunctorSingleFunctorIsoOfFlat (etaleKummer_flatConstantInt A X)).hom ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map ((extendScalarsCompSheafExtendScalarsIso ρ X).hom.app _) := by
  let := preservesKFlatQuasiIso_extendScalars hρ ha X
  let adj := Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ
  have h := adj.singleTranspose_derivedAdjunctionMapDerivedCategory (etaleKummer_flatConstantInt A X)
    ((extendScalarsToRestrictScalars ρ X).app X.constantSheafInt)
  have e : (adj.homEquiv _ _).symm ((extendScalarsToRestrictScalars ρ X).app X.constantSheafInt) =
      (extendScalarsCompSheafExtendScalarsIso ρ X).hom.app X.constantSheafInt := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    simp [extendScalarsToRestrictScalars]
    rfl
  exact h.trans (congrArg (fun z ↦
    ((Sheaf.extendScalars _ ρ).leftDerivedFunctorSingleFunctorIsoOfFlat (etaleKummer_flatConstantInt A X)).hom ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map z) e)

variable [NeZero (ringChar A)] [NeZero (ringChar B)]

/-- Compare the two constant complexes via scalar extension on their free integral sheaf presentations. -/
noncomputable def etaleKummerFreeConstantMap
    (T : Scheme.{u}) [HasInvertibleExponent A T] [HasInvertibleExponent B T] :
    (derivedExtendScalars hρ ha T).obj (constantComplex A T) ⟶ constantComplex B T :=
  (derivedExtendScalars hρ ha T).map (constantComplexIsoSingleFunctorExtendScalarsInt T A).hom ≫
    ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ) (derivedExtendScalarsAdjunction hρ ha T)
      ((extendScalarsToRestrictScalars ρ T).app T.constantSheafInt) ≫
      (constantComplexIsoSingleFunctorExtendScalarsInt T B).inv

/-- SGA 4, XVI, 3.8, pp. 229–230, and the free-sheaf comparisons of
`TateTwist/KummerClass/Basic.lean`. At the universal invertible-exponent base,
represent the two constant complexes by the free rank-one sheaves in degree zero.
The upper presentation is the pullback of the free generator along the identity of
the base. The lower presentation restricts the lower free generator along the
structural map to its exponent base. Each generator is the image of the integer 1.
The terminal-scheme comparison restricts multiplication of coefficients to this base
and carries the upper generator to the lower generator. In the flat models the scalar
extension transitivity morphism takes 1 ⊗ (1 ⊗ 1) to 1 ⊗ 1. The two maps thus agree
on a generator of the free rank-one sheaf, hence agree in the single complexes. -/
theorem etaleKummerConstantReduction_base :
    let S := invertibleExponentBase.{u} A
    letI : HasInvertibleExponent B S := HasInvertibleExponent.of_ringHom ρ S
    etaleKummerFreeConstantMap hρ ha S = (derivedExtendScalarsConstantComplexIso hρ ha S).hom := by
  let S := invertibleExponentBase.{u} A
  letI : HasInvertibleExponent B S := HasInvertibleExponent.of_ringHom ρ S
  change etaleKummerFreeConstantMap hρ ha S = _
  unfold etaleKummerFreeConstantMap
  rw [etaleKummer_presentation_eq_ofUnit A S, etaleKummer_presentation_eq_ofUnit B S]
  exact (etaleKummer_supported_freePresentation hρ ha S).symm

omit [NeZero (ringChar A)] [NeZero (ringChar B)] in
private theorem kummerFreeConstantMap_descend
    {X S : Scheme.{u}} [HasInvertibleExponent A X] [HasInvertibleExponent B X]
    [HasInvertibleExponent A S] [HasInvertibleExponent B S] (f : X ⟶ S)
    (hS : etaleKummerFreeConstantMap hρ ha S = (derivedExtendScalarsConstantComplexIso hρ ha S).hom) :
    (derivedExtendScalars hρ ha X).map (constantComplexIsoSingleFunctorExtendScalarsInt X A).hom ≫
        ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
          (derivedExtendScalarsAdjunction hρ ha X) ((extendScalarsToRestrictScalars ρ X).app X.constantSheafInt) =
      (derivedExtendScalarsConstantComplexIso hρ ha X).hom ≫ (constantComplexIsoSingleFunctorExtendScalarsInt X B).hom := by
  let α (T : Scheme.{u}) := (extendScalarsToRestrictScalars ρ T).app T.constantSheafInt
  let v : (f)^*[AddCommGrpCat.{u+1}].obj S.constantSheafInt ⟶ X.constantSheafInt :=
    (upperStarConstantSheafIso AddCommGrpCat.{u+1} f).hom.app
    (AddCommGrpCat.of (ULift.{u+1} (ZMod 0)))
  let q (R : Type (u+1)) [CommRing R] :
      (f)^*[ModuleCat.{u+1} R].obj ((extendScalars R S).obj S.constantSheafInt) ⟶
        (extendScalars R X).obj X.constantSheafInt :=
    (upperStarExtendScalarsIso R f).hom.app S.constantSheafInt ≫ (extendScalars R X).map v
  have hs := freeSheafReduction_pullback ρ f S.constantSheafInt
  have hn := (extendScalarsToRestrictScalars ρ X).naturality v
  dsimp only [Functor.comp_map] at hn
  have hsheaf : (f)^*[ModuleCat.{u+1} A].map (α S) ≫ (upperStarRestrictScalarsIso ρ f).hom.app _ ≫
      (Sheaf.restrictScalars _ ρ).map (q B) = q A ≫ α X := by
    dsimp only [q]
    rw [Functor.map_comp, reassoc_of% hs, Category.assoc, hn]
  have h := etaleReductionPullback_of_singleModels (A := A) (B := B) (ρ := ρ) f hρ ha
    (T := constantComplex A S) (U := constantComplex B S) (T' := constantComplex A X) (U' := constantComplex B X)
    (M := (extendScalars A S).obj S.constantSheafInt) (M' := (extendScalars A X).obj X.constantSheafInt)
    (N := (extendScalars B S).obj S.constantSheafInt) (N' := (extendScalars B X).obj X.constantSheafInt)
    (α S) (α X) (q A) (q B) hsheaf
    (constantComplexIsoSingleFunctorExtendScalarsInt S A) (constantComplexIsoSingleFunctorExtendScalarsInt S B)
    (constantComplexIsoSingleFunctorExtendScalarsInt X A) (constantComplexIsoSingleFunctorExtendScalarsInt X B)
    (leftDerivedUpperStarConstantComplexIso A f).hom (leftDerivedUpperStarConstantComplexIso B f).hom
    (derivedExtendScalarsConstantComplexIso hρ ha S).hom (etaleKummerFreeConstantMap hρ ha X) hS.symm rfl
    (leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt A f)
    (leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt B f)
  have ht := derivedExtendScalarsConstantComplexIso_hom_pullback hρ ha f
  let e := (derivedExtendScalars hρ ha X).mapIso (leftDerivedUpperStarConstantComplexIso A f)
  have hb : etaleKummerFreeConstantMap hρ ha X = (derivedExtendScalarsConstantComplexIso hρ ha X).hom :=
    (cancel_epi e.hom).mp (h.symm.trans ht.symm)
  unfold etaleKummerFreeConstantMap at hb
  rw [← Category.assoc, Iso.comp_inv_eq] at hb
  exact hb

/-- The normalization on the exponent base determines the comparison of the constant Kummer
terms on every scheme by geometric pullback. -/
theorem etaleKummerConstantReduction
    (X : Scheme.{u}) [HasInvertibleExponent A X] [HasInvertibleExponent B X] :
    (derivedExtendScalars hρ ha X).map (constantComplexIsoSingleFunctorExtendScalarsInt X A).hom ≫
        ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
          (derivedExtendScalarsAdjunction hρ ha X)
          ((extendScalarsToRestrictScalars ρ X).app X.constantSheafInt) =
      (derivedExtendScalarsConstantComplexIso hρ ha X).hom ≫
        (constantComplexIsoSingleFunctorExtendScalarsInt X B).hom := by
  let S := invertibleExponentBase.{u} A
  have : HasInvertibleExponent B S := HasInvertibleExponent.of_ringHom ρ S
  exact kummerFreeConstantMap_descend hρ ha (toInvertibleExponentBase (Λ := A) X)
    (etaleKummerConstantReduction_base hρ ha)

end WeilII
