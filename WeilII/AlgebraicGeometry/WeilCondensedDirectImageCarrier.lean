module

public import WeilConjectures.WeilSheaf.CondensedWeilUpperShriekTrace
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.CategoryTheory.WeilLiftAdjunction
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree

/-! # Frobenius on the condensed carrier of a Weil direct image -/

open CategoryTheory Endofunctor AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Limits

namespace WeilII.WeilCondensedCarrier

universe u

variable (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
variable (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The underlying condensed geometric complex of a Weil complex. -/
public noncomputable abbrev carrier :=
  WeilComplex.forget (k₀ := k) (l := ℓ) (X := X) ⋙
    (adicSheafDerivedEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor

/-- The Frobenius structure on the carrier, natural in the Weil complex. -/
@[expose] public noncomputable def datum :
    carrier k ℓ X ⋙ (WeilComplex.condensedFrobenius k ℓ X).mapDerivedCategory ⟶ carrier k ℓ X where
  app M := transportWeilDatum
    (adicSheafDerivedEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
    (IsoAlgebra.derivedExactCommIso (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ X)).symm
    ((IsoAlgebra.derivedStrIso _).hom.app M.obj)
  naturality _ _ f := IsWeilEquivariant.map _
    (IsoAlgebra.derivedExactCommIso (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ X)).symm
    (show IsWeilEquivariant _ _ _ _ from (IsoAlgebra.derivedStrIso _).hom.naturality f.hom)

variable {X} {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
variable (f : Z ⟶ X) [f.IsOver (Spec (.of k))]

private noncomputable abbrev exchange :=
  CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso (Profinite.padicAlgClRingObj ℓ)
    f (comp_over f (Spec (.of k)))

private noncomputable abbrev carrierIso (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :=
  IsoAlgebra.derivedExactForgetCommIso (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ Y)

variable [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]

/-- Forgetting a Weil direct image gives the derived geometric direct image. Change the Weil
model, use the derived forgetful comparison, and change the geometric carrier back at source. -/
public noncomputable def rightDerivedDirectImageIso :
    WeilComplex.derivedLowerStar f ⋙ carrier k ℓ X ≅ carrier k ℓ Z ⋙
      (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
        (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (.of k))))).rightDerivedFunctor := by
  let c := ProEtaleWeilSheaf.rightDerivedLowerStarCompToCondensedIso k ℓ f
  let L := CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
    (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (.of k))))
  let F := (IsoAlgebra.forget (WeilComplex.condensedFrobenius k ℓ X)).mapDerivedCategory
  let W := (ProEtaleWeilSheaf.derivedEquivCondensed k ℓ Z).functor
  let T := (ProEtaleWeilSheaf.lowerStar k ℓ f).rightDerivedFunctor
  exact Functor.isoWhiskerLeft (WeilComplex.objectProperty k ℓ Z).ι
    (Functor.isoWhiskerLeft T (carrierIso k ℓ X).symm ≪≫ Functor.isoWhiskerRight c F ≪≫
      Functor.isoWhiskerLeft W (IsoAlgebra.derivedForgetCommIso (exchange k ℓ f)) ≪≫
      Functor.isoWhiskerRight (carrierIso k ℓ Z) L.rightDerivedFunctor)

/-- If geometric direct image is exact, there is a natural identification with termwise
direct image carrying Frobenius to the derived exact exchange. Use the geometric Weil-model
comparison before forgetting the actions. Compare the derived pushforward of condensed Weil
sheaves with its exact realization, then apply the exact forgetful Frobenius square. -/
public theorem exists_exactDirectImageIso
    [PreservesFiniteColimits (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (.of k)))))] :
    ∃ κ : WeilComplex.derivedLowerStar f ⋙ carrier k ℓ X ≅ carrier k ℓ Z ⋙
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
          (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (.of k))))).mapDerivedCategory,
      IsWeilLift (datum k ℓ Z) (datum k ℓ X)
        (IsoAlgebra.derivedExactCommIso (CondensedRing.lowerStarGeometricFiberMapCompFrobeniusIso
          (Profinite.padicAlgClRingObj ℓ) f (comp_over f (Spec (.of k))))) κ := by
  let e := exchange k ℓ f
  let L := CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
    (Scheme.Hom.geometricFiberMap f (comp_over f (Spec (.of k))))
  let F := (IsoAlgebra.forget (WeilComplex.condensedFrobenius k ℓ X)).mapDerivedCategory
  let W := (ProEtaleWeilSheaf.derivedEquivCondensed k ℓ Z).functor
  let T := (ProEtaleWeilSheaf.lowerStar k ℓ f).rightDerivedFunctor
  let c := ProEtaleWeilSheaf.rightDerivedLowerStarCompToCondensedIso k ℓ f ≪≫
    Functor.isoWhiskerLeft W (IsoAlgebra.mapOfNatIso e).rightDerivedFunctorIsoMapDerivedCategory
  let κ := Functor.isoWhiskerLeft (WeilComplex.objectProperty k ℓ Z).ι
    (Functor.isoWhiskerLeft T (carrierIso k ℓ X).symm ≪≫ Functor.isoWhiskerRight c F ≪≫
      Functor.isoWhiskerLeft W (IsoAlgebra.derivedExactForgetCommIso e) ≪≫
      Functor.isoWhiskerRight (carrierIso k ℓ Z) L.mapDerivedCategory)
  refine ⟨κ, fun M ↦ ?_⟩
  let Xcmp := ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ X
  let Zcmp := ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ Z
  let G := (WeilComplex.condensedFrobenius k ℓ X).mapDerivedCategory
  have h₁ := IsWeilEquivariant.inv G ((carrierIso k ℓ X).app (T.obj M.obj))
    (IsoAlgebra.isWeilEquivariant_derivedExactForgetCommIso_hom_app Xcmp (T.obj M.obj))
  have h₂ : IsWeilEquivariant G _ _ (F.map (c.hom.app M.obj)) :=
    (IsoAlgebra.derivedStrIso _).hom.naturality (c.hom.app M.obj)
  have h₃ := IsoAlgebra.isWeilEquivariant_derivedExactForgetCommIso_hom_app e (W.obj M.obj)
  have h₄ := IsWeilEquivariant.map L.mapDerivedCategory (IsoAlgebra.derivedExactCommIso e).symm
    (IsoAlgebra.isWeilEquivariant_derivedExactForgetCommIso_hom_app Zcmp M.obj)
  exact (h₁.comp (h₂.comp (h₃.comp h₄))).symm

end WeilII.WeilCondensedCarrier
