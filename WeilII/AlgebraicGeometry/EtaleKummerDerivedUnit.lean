module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

import all Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalIso

/-! # The derived coefficient unit on a flat single complex -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open _root_.DerivedCategory

/-- On the tensor unit in degree zero, the derived counit is computed by the flat single
comparison and the underived counit. -/
theorem leftDerived_unit_flatSingle {C D : Type*} [Category.{u+1} C] [Abelian C]
    [IsGrothendieckAbelian.{u+1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    [Category.{u+1} D] [Abelian D] [IsGrothendieckAbelian.{u+1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] :
    letI := F.leftDerivedFunctorMonoidal
    L(F).map (_root_.DerivedCategory.singleFunctorObjUnitIso C).hom ≫ η L(F) ≫
        (_root_.DerivedCategory.singleFunctorObjUnitIso D).inv = (F.leftDerivedFunctorSingleFunctorIsoOfFlat
      (ObjectProperty.flat_of_tensorIso (λ_ (𝟙_ C)))).hom ≫ (singleFunctor D 0).map (η F) := by
  let := F.leftDerivedFunctorMonoidal
  have eC : ε (Qh (C := C)) = 𝟙 _ := rfl
  have eD : ε (Qh (C := D)) = 𝟙 _ := rfl
  have hm := F.leftDerivedFunctorMonoidal_η
  change η L(F) ≫ ε Qh = _ at hm
  erw [eC, eD, F.leftDerivedFunctor.map_id, Category.comp_id, Category.id_comp] at hm
  rw [hm, Functor.mapHomotopyCategory_η, Functor.mapCochainComplex_η]
  have qC : ∀ K, (quotientCompQhIso C).inv.app K = 𝟙 _ := fun _ ↦ rfl
  have qD : ∀ K, (quotientCompQhIso D).hom.app K = 𝟙 _ := fun _ ↦ rfl
  have eC' : η (HomotopyCategory.quotient C (.up ℤ)) = 𝟙 _ := rfl
  have eD' : (Functor.Monoidal.εIso (HomotopyCategory.quotient D (.up ℤ))).hom = 𝟙 _ := rfl
  have eCinv : (asIso (ε (Qh (C := C)))).inv = 𝟙 _ := by
    have h := (asIso (ε (Qh (C := C)))).inv_hom_id
    change _ ≫ ε (Qh (C := C)) = _ at h
    exact (Category.comp_id _).symm.trans ((congrArg ((asIso (ε (Qh (C := C)))).inv ≫ ·) eC.symm).trans h)
  have hc : ∀ K, (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := fun _ ↦ rfl
  simp only [Functor.leftDerivedFunctorSingleFunctorIsoOfFlat, Functor.mapCochainComplexεIso,
    Functor.Monoidal.εIso_inv, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, asIso_hom,
    _root_.DerivedCategory.singleFunctorObjUnitIso, singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Functor.map_comp,
    hc, qC, qD, eC', eD', eD, eCinv, Category.assoc, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  repeat first | erw [CategoryTheory.Functor.map_id] | erw [Category.id_comp] | erw [Category.comp_id]
  rfl

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

private theorem etaleSingleUnit (C : Type*) [Category.{u+1} C] [Abelian C]
    [IsGrothendieckAbelian.{u+1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C] (X : Scheme.{u}) :
    AlgebraicGeometry.Etale.singleFunctorObjUnitIso C X =
      _root_.DerivedCategory.singleFunctorObjUnitIso (Sheaf X.smallEtaleTopology C) := by
  unfold AlgebraicGeometry.Etale.singleFunctorObjUnitIso singleFunctorObjIsoQh
    _root_.DerivedCategory.singleFunctorObjUnitIso
  rw [Iso.trans_assoc]

private theorem changeUnitModels {K L : Type*} [Category* K] [Category* L] (P : K ⥤ L)
      {m n : K} {r s : L} (i i' : m ≅ n) (j j' : r ≅ s) (e : P.obj n ⟶ s)
      (hi : i = i') (hj : j = j') :
      P.map i.hom ≫ e ≫ j.inv = P.map i'.hom ≫ e ≫ j'.inv := by rw [hi, hj]

/-- In degree zero the derived coefficient unit is the transpose of the ordinary restriction
of coefficients on the unit sheaves. -/
theorem etaleKummer_singleTranspose_unit {A B : Type (u+1)} [CommRing A] [CommRing B]
    {ρ : A →+* B} (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    (X : Scheme.{u}) :
    (derivedExtendScalars hρ ha X).map
        (AlgebraicGeometry.Etale.singleFunctorObjUnitIso (ModuleCat.{u+1} A) X).hom ≫
      (derivedExtendScalarsConstantComplexEtaIso hρ ha X).hom ≫
        (AlgebraicGeometry.Etale.singleFunctorObjUnitIso (ModuleCat.{u+1} B) X).inv =
      ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars _ ρ)
        (derivedExtendScalarsAdjunction hρ ha X) (ε (Sheaf.restrictScalars _ ρ)) := by
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A)
  let D := Sheaf X.smallEtaleTopology (ModuleCat.{u+1} B)
  let F := Sheaf.extendScalars X.smallEtaleTopology ρ
  let G := Sheaf.restrictScalars X.smallEtaleTopology ρ
  let adj := Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ
  let := preservesKFlatQuasiIso_extendScalars hρ ha X
  have hU : ObjectProperty.flat (𝟙_ C) := ObjectProperty.flat_of_tensorIso (λ_ _)
  have h := adj.singleTranspose_derivedAdjunctionMapDerivedCategory hU (ε G)
  have hu : (adj.homEquiv _ _).symm (ε G) = η F := rfl
  rw [hu] at h
  have hl := leftDerived_unit_flatSingle F
  have huA := etaleSingleUnit (ModuleCat.{u+1} A) X
  have huB := etaleSingleUnit (ModuleCat.{u+1} B) X
  exact (changeUnitModels (derivedExtendScalars hρ ha X) _ _ _ _
    (derivedExtendScalarsConstantComplexEtaIso hρ ha X).hom huA huB).trans (hl.trans h.symm)

end WeilII
