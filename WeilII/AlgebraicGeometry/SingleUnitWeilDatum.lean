module

public import WeilConjectures.WeilSheaf.SmoothPurityConstantWeilDatum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedExactLift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullCounit
import WeilConjectures.WeilSheaf.SmoothPurityCoefficientPullShift
import WeilII.CategoryTheory.DerivedSingleHomotopyDatum
import WeilII.CategoryTheory.SingleWeilDatum
meta import WeilII.AlgebraicGeometry.CompactificationComponentTransport

/-! # The shifted regular module under a scheme automorphism -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Endofunctor
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 10
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace WeilII

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] {T : Scheme.{u}}
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "Aₜ" => CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab) (condensedRingObj Λ T)

/-- On the single of the ordinary regular module the exact pushforward along the
inverse automorphism has the left-derived pullback unit datum. This uses the
degree-zero single comparison, the factorization of the left-derived counit,
and the ordinary comparison from pullback to inverse pushforward. -/
theorem condensedSingleUnitWeilDatum (σ : T ≅ T) :
    let H := CondensedRing.lowerStar Λ σ.inv
    let j := CondensedRing.upperStarIsoLowerStarInv Λ σ
    let t := leftDerivedUpperStarIsoMapDerivedCategory Λ σ.hom ≪≫ Functor.mapDerivedCategoryNatIso j
    IsWeilEquivariant H.mapDerivedCategory
      ((H.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ _) ≫
        (DerivedCategory.singleFunctor _ 0).map (j.inv.app _ ≫ tateUnitDatum ℓ σ.hom))
      (t.inv.app _ ≫ (leftDerivedUpperStarUnitIso Λ σ.hom).hom)
      ((DerivedCategory.quotientCompQhIso Aₜ).inv.app (𝟙_ (CochainComplex Aₜ ℤ))) := by
  intro H j t
  let P := CondensedRing.upperStar Λ σ.hom
  apply singleWeilDatum_changeFunctor j
  rw [leftDerivedUpperStarUnitIso_hom_eq]
  erw [reassoc_of% (leftDerivedUpperStarIsoMapDerivedCategory_inv_app_comp_counit σ.hom Λ
    (𝟙_ _))]
  have h := derivedSingleHomotopyDatum P (Functor.Monoidal.εIso P).inv
  transport_compactification_component h

/-- In every degree, realization of the single adic regular module as a shifted
condensed unit is equivariant for a scheme automorphism. -/
theorem singleUnitWeilDatum (σ : T ≅ T) (i : ℤ) :
    let F := adicLowerStar ℓ σ.inv
    let H := CondensedRing.lowerStar Λ σ.inv
    let E := (adicSheafEquivCondensedMod ℓ T).functor
    let U := AdicSheaf.unit ℓ T
    let e := (adicLowerStarCompCondensedModIso ℓ σ.inv).symm
    let u := (F.mapDerivedCategorySingleFunctor i).app U ≪≫
      (DerivedCategory.singleFunctor _ i).mapIso (adicLowerStarUnitIso ℓ σ.symm)
    let w := leftDerivedUpperStarIsoMapDerivedCategory Λ σ.hom
    let j := CondensedRing.upperStarIsoLowerStarInv Λ σ
    let t := w ≪≫ Functor.mapDerivedCategoryNatIso j
    let s := (E.mapDerivedCategorySingleFunctor i).app U ≪≫
      (DerivedCategory.singleFunctor _ i).mapIso (adicSheafEquivCondensedModTensorUnitIso ℓ T) ≪≫
      (((DerivedCategory.singleFunctors _).shiftIso (-i) i 0 (by lia)).app _).symm ≪≫
      (shiftFunctor _ (-i)).mapIso
        ((DerivedCategory.quotientCompQhIso Aₜ).symm.app (𝟙_ (CochainComplex Aₜ ℤ)))
    IsWeilEquivariant H.mapDerivedCategory
      (transportWeilDatum E.mapDerivedCategory (IsoAlgebra.derivedExactCommIso e).symm u.hom)
      (t.inv.app _ ≫ ((CondensedRing.upperStar Λ σ.hom).leftDerivedFunctor.commShiftIso (-i)).hom.app (𝟙_ _) ≫
        (shiftFunctor _ (-i)).map (leftDerivedUpperStarUnitIso Λ σ.hom).hom) s.hom := by
  intro F H E U e u w j t s
  let r := adicSheafEquivCondensedModTensorUnitIso ℓ T
  let b := j.inv.app (𝟙_ _) ≫ tateUnitDatum ℓ σ.hom
  have hb := purity_adicLowerStarUnit_condensed ℓ σ
  have h : H.map r.hom ≫ b =
      e.hom.app U ≫ E.map (adicLowerStarUnitIso ℓ σ.symm).hom ≫ r.hom := by
    rw [← cancel_epi (H.map r.inv), ← H.map_comp_assoc, r.inv_hom_id, H.map_id, Category.id_comp]
    exact hb.symm
  have h₁ := singleWeilDatum F H E e (adicLowerStarUnitIso ℓ σ.symm).hom b r.hom h i
  let q := (DerivedCategory.quotientCompQhIso Aₜ).inv.app (𝟙_ (CochainComplex Aₜ ℤ))
  have h₀ := condensedSingleUnitWeilDatum ℓ σ
  have h₂ := singleWeilDatum_shift H b (t.inv.app _ ≫ (leftDerivedUpperStarUnitIso Λ σ.hom).hom)
    q h₀ i
  have : t.inv.CommShift ℤ := by
    dsimp only [t, Iso.trans_inv, w]
    infer_instance
  rw [shiftedDatum_changeFunctor] at h₂
  have result := h₁.comp h₂
  dsimp only [s, u, r, U, q, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom] at result ⊢
  simp only [Category.assoc] at result
  transport_compactification_component result

end WeilII
