module

public import WeilII.AlgebraicGeometry.WeilSingleFrobenius
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
import all WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
import all WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal

/-! # Pullback of the tensor of two degree-zero condensed modules -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
open WeilII.CompactSupportClasses

namespace WeilII.ExternalProduct

universe u

variable {ℓ : ℕ} [Fact ℓ.Prime] {X Y : Scheme.{u}}
set_option quotPrecheck false
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "U" => CondensedRing.upperStar Λ
local notation "S" X => DerivedCategory.singleFunctor (Coeff ℓ X) 0
local notation "sg" X => HomologicalComplex.single (Coeff ℓ X) (.up ℤ) 0
local notation "q" X => HomotopyCategory.quotient (Coeff ℓ X) (.up ℤ)
local notation "λ₀" f => (U f).singleFunctorCompLeftDerivedFunctorIso.hom

local instance (v : X ⟶ Y) : (pull (ℓ := ℓ) v).Monoidal :=
  CondensedRing.monoidal_leftDerivedUpperStar _ _

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
local instance (Z : Scheme.{u}) : SymmetricCategory (Coeff ℓ Z) :=
  @Mod.symmetricCategory _ _ _ _ _ _ _ _ _ (isCommMonObj_condensedRingObj Λ Z)
local instance (Z : Scheme.{u}) : MonoidalClosed (Coeff ℓ Z) :=
  @Mod.monoidalClosed _ _ _ _ _ _ _ _ _ (isCommMonObj_condensedRingObj Λ Z)

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def singleQh (X : Scheme.{u}) :
    (S X) ≅ (sg X) ⋙ (q X) ⋙ DerivedCategory.Qh :=
  DerivedCategory.singleFunctorIsoCompQ _ 0 ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _).symm

private lemma flatSingleFactor {A : Coeff ℓ X} (B : Coeff ℓ X)
    (hA : IsLocallyFree (condensedRingObj Λ X) A) :
    (hA.singleFunctorTensorObjIso B 0).hom =
      ((singleQh X).hom.app A ⊗ₘ (singleQh X).hom.app B) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh ((q X).obj ((sg X).obj A))
          ((q X).obj ((sg X).obj B)) ≫
        DerivedCategory.Qh.map ((q X).map (Etale.singleCochainTensorIso A B).hom) ≫
        (singleQh X).inv.app (A ⊗ B) := by
  simp only [IsLocallyFree.singleFunctorTensorObjIso, Iso.trans_hom, tensorIso_hom,
    Functor.mapIso_hom, Iso.symm_hom, Etale.singleCochainTensorIso, singleQh,
    Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, DerivedCategory.flat_comparison, Iso.app_hom, Iso.app_inv]
  simp only [Functor.LaxMonoidal.transport_μ, Functor.LaxMonoidal.comp_μ,
    Category.assoc, DerivedCategory.singleFunctorIsoCompQ, NatTrans.id_app, Iso.refl_hom,
    Iso.refl_inv, Category.id_comp, id_tensorHom_id]
  apply congrArg (_ ≫ ·)
  apply congrArg (_ ≫ ·)
  let a := (sg X).obj A
  let b := (sg X).obj B
  let t := (Etale.singleCochainTensorIso A B).hom
  have hq : DerivedCategory.Qh.map (Functor.LaxMonoidal.μ (q X) a b) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  have hn := (DerivedCategory.quotientCompQhIso_hom_naturality t).symm
  erw [hq, Category.id_comp, Category.comp_id, Category.comp_id]
  simpa only [t, Etale.singleCochainTensorIso, Iso.trans_hom, Iso.app_hom, Iso.symm_inv] using hn

private lemma singleCounit (v : X ⟶ Y) (M : Coeff ℓ Y) :
    (pull v).map ((singleQh Y).hom.app M) ≫
      (U v).leftDerivedFunctorCounit.app ((q Y).obj ((sg Y).obj M)) ≫
        DerivedCategory.Qh.map ((q X).map
          ((HomologicalComplex.singleMapHomologicalComplex (U v) (.up ℤ) 0).hom.app M)) =
    (λ₀ v).app M ≫ (singleQh X).hom.app ((U v).obj M) := by
  rw [← Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  erw [(U v).leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc ((singleQh Y).hom.app M)]
  simp only [Functor.comp_obj, singleQh, Iso.trans_hom,
    Iso.symm_hom, Functor.map_comp, Functor.mapHomotopyCategory_obj,
    Functor.mapDerivedCategoryFactorsh_hom_app, DerivedCategory.Q_obj_single_obj,
    Category.assoc, Functor.singleFunctorCompLeftDerivedFunctorIso, Functor.mapDerivedCategorySingleFunctor,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Iso.inv_hom_id_app_assoc, NatIso.cancel_natIso_hom_left]
  erw [← (U v).mapDerivedCategory.map_comp_assoc
    ((DerivedCategory.quotientCompQhIso (Coeff ℓ Y)).inv.app _)
    ((DerivedCategory.quotientCompQhIso (Coeff ℓ Y)).hom.app _), Iso.inv_hom_id_app]
  simp only [Functor.mapHomotopyCategoryFactors, CategoryTheory.Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  erw [← DerivedCategory.quotientCompQhIso_inv_naturality]

/-- Exact pullback respects the prescribed tensor identification of locally free singles. -/
theorem flatSingleTensorPullback (v : X ⟶ Y) (A B : Coeff ℓ Y)
    (hA : IsLocallyFree (condensedRingObj Λ Y) A) :
    (pull v).map (hA.singleFunctorTensorObjIso B 0).hom ≫ (λ₀ v).app (A ⊗ B) ≫
        (S X).map (Functor.OplaxMonoidal.δ (U v) A B) =
      Functor.OplaxMonoidal.δ (pull v) ((S Y).obj A) ((S Y).obj B) ≫
        ((λ₀ v).app A ⊗ₘ (λ₀ v).app B) ≫
        ((hA.upperStar Λ v).singleFunctorTensorObjIso ((U v).obj B) 0).hom := by
  let H := (U v).mapHomotopyCategory (.up ℤ)
  let c := HomologicalComplex.singleMapHomologicalComplex (U v) (.up ℤ) 0
  rw [flatSingleFactor, flatSingleFactor]
  apply Etale.tensor_comparison_transport DerivedCategory.Qh DerivedCategory.Qh H (pull v)
    (CondensedRing.leftDerivedUpperStarTensor Λ v)
    (U v).leftDerivedFunctorCounit
    ((q Y).obj ((sg Y).obj A)) ((q Y).obj ((sg Y).obj B)) ((q Y).obj ((sg Y).obj (A ⊗ B)))
    ((q X).obj ((sg X).obj ((U v).obj A))) ((q X).obj ((sg X).obj ((U v).obj B)))
    ((q X).obj ((sg X).obj ((U v).obj A ⊗ (U v).obj B)))
    ((q Y).map (Etale.singleCochainTensorIso A B).hom)
    ((q X).map (Etale.singleCochainTensorIso ((U v).obj A) ((U v).obj B)).hom)
    ((q X).map (c.hom.app A)) ((q X).map (c.hom.app B))
    ((q X).map (c.hom.app (A ⊗ B)) ≫ (q X).map ((sg X).map (Functor.OplaxMonoidal.δ (U v) A B)))
    (Etale.singleHomotopyTensorIso_pullback (U v) A B)
    (CondensedRing.leftDerivedUpperStarTensor_laxSquare Λ v _ _)
    ((singleQh Y).app A) ((singleQh Y).app B) ((singleQh Y).app (A ⊗ B))
    ((singleQh X).app ((U v).obj A)) ((singleQh X).app ((U v).obj B))
    ((singleQh X).app ((U v).obj A ⊗ (U v).obj B))
    ((λ₀ v).app A) ((λ₀ v).app B)
    ((λ₀ v).app (A ⊗ B) ≫ (S X).map (Functor.OplaxMonoidal.δ (U v) A B))
    (singleCounit v A).symm (singleCounit v B).symm
  have hn := (singleQh X).hom.naturality (Functor.OplaxMonoidal.δ (U v) A B)
  erw [Category.assoc, hn, ← Category.assoc, ← singleCounit v (A ⊗ B)]
  simp only [Category.assoc, Functor.map_comp, Functor.comp_map]
  rfl

/-- The locally free single tensor comparison is natural in both module arguments. -/
theorem flatSingleTensor_naturality {A A' B B' : Coeff ℓ X} (f : A ⟶ A') (g : B ⟶ B')
    (hA : IsLocallyFree (condensedRingObj Λ X) A)
    (hA' : IsLocallyFree (condensedRingObj Λ X) A') :
    ((S X).map f ⊗ₘ (S X).map g) ≫ (hA'.singleFunctorTensorObjIso B' 0).hom =
      (hA.singleFunctorTensorObjIso B 0).hom ≫ (S X).map (f ⊗ₘ g) := by
  obtain ⟨ms, hs⟩ := Etale.exists_singleCochainMonoidal (C := Coeff ℓ X)
  let _ := ms
  let e := singleQh (ℓ := ℓ) X
  let _ := Functor.LaxMonoidal.transport e.symm
  have h (P N : Coeff ℓ X) (hP : IsLocallyFree (condensedRingObj Λ X) P) :
      (hP.singleFunctorTensorObjIso N 0).hom = Functor.LaxMonoidal.μ (S X) P N := by
    rw [Functor.LaxMonoidal.transport_μ e.symm, flatSingleFactor]
    simp only [Functor.LaxMonoidal.comp_μ, hs, Category.assoc, Functor.comp_map]
    have unitMap : DerivedCategory.Qh.map
        (Functor.LaxMonoidal.μ (q X) ((sg X).obj P) ((sg X).obj N)) = 𝟙 _ :=
      DerivedCategory.Qh.map_id _
    rw [unitMap, Category.id_comp]
    rfl
  rw [h _ _ hA', h _ _ hA]
  exact Functor.LaxMonoidal.μ_natural _ f g

end WeilII.ExternalProduct
