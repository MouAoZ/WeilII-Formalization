module

public import WeilII.AlgebraicGeometry.GeometricPointGradedTensorKunneth
public import WeilII.AlgebraicGeometry.CompactSupportShiftedUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
import WeilConjectures.CategoryTheory.ObjectProperty.FullSubcategoryEqToHom
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Shift

/-! # Pullback of the ordered splitting of a shifted unit -/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000
attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

section

variable {C : Type*} [Category* C] [HasShift C ℤ] (F : C ⥤ C) [F.CommShift ℤ]

private abbrev shiftedDatum {X : C} (i : ℤ) (x : F.obj X ⟶ X) :=
  (F.commShiftIso i).hom.app X ≫ x⟦i⟧'

private abbrev commutes {X Y : C} (x : F.obj X ⟶ X) (y : F.obj Y ⟶ Y) (f : X ⟶ Y) :=
  F.map f ≫ y = x ≫ f

omit [HasShift C ℤ] [F.CommShift ℤ] in
private theorem composeDatum {X Y Z : C} {x : F.obj X ⟶ X} {y : F.obj Y ⟶ Y} {z : F.obj Z ⟶ Z}
    {f : X ⟶ Y} {g : Y ⟶ Z} (h : commutes F x y f) (h' : commutes F y z g) :
    commutes F x z (f ≫ g) := by
  change F.map (f ≫ g) ≫ z = _
  rw [F.map_comp, Category.assoc, h', ← Category.assoc, h, Category.assoc]

private theorem shiftDatumMap {X Y : C} {x : F.obj X ⟶ X} {y : F.obj Y ⟶ Y} {f : X ⟶ Y}
    (h : commutes F x y f) (i : ℤ) :
    commutes F (shiftedDatum F i x) (shiftedDatum F i y) (f⟦i⟧') := by
  unfold commutes shiftedDatum
  rw [F.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]

private theorem addDatum {X : C} (x : F.obj X ⟶ X) (a b c : ℤ) (h : a + b = c) :
    commutes F (shiftedDatum F b (shiftedDatum F a x)) (shiftedDatum F c x)
      ((shiftFunctorAdd' C a b c h).inv.app X) := by
  unfold commutes shiftedDatum
  rw [F.commShiftIso_add' h]
  simp only [Functor.CommShift.isoAdd'_hom_app, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (shiftFunctorAdd' C a b c h).inv.naturality x]
  erw [F.map_id, Category.id_comp]
  rfl

private theorem functorShiftDatum (H : C ⥤ C) [H.CommShift ℤ] (τ : H ⋙ F ⟶ F ⋙ H)
    [NatTrans.CommShift τ ℤ] {X : C} (x : F.obj X ⟶ X) (i : ℤ) :
    commutes F (τ.app (X⟦i⟧) ≫ H.map (shiftedDatum F i x))
      (shiftedDatum F i (τ.app X ≫ H.map x)) ((H.commShiftIso i).hom.app X) := by
  have eq := NatTrans.shift_app_comm τ i X
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at eq
  unfold commutes shiftedDatum
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% eq, ← H.commShiftIso_hom_naturality]

omit [HasShift C ℤ] [F.CommShift ℤ] in
private theorem unitDatum [MonoidalCategory C] [F.OplaxMonoidal] :
    let η := Functor.OplaxMonoidal.η F
    commutes F (Functor.OplaxMonoidal.δ F _ _ ≫ ((η) ⊗ₘ η)) η (λ_ (𝟙_ C)).hom := by
  intro η
  unfold commutes
  rw [← Functor.OplaxMonoidal.left_unitality_hom F (𝟙_ C), MonoidalCategory.tensorHom_def]
  simp only [Category.assoc, leftUnitor_naturality]
  rfl

private theorem castDatum {X : C} (x : F.obj X ⟶ X) {i j : ℤ} (h : i = j) :
    commutes F (shiftedDatum F i x) (shiftedDatum F j x) (eqToHom (congrArg (fun n : ℤ ↦ X⟦n⟧) h)) := by
  subst j
  simp [commutes]

omit [HasShift C ℤ] [F.CommShift ℤ] in
private theorem splitDatum [MonoidalCategory C] [F.OplaxMonoidal] {V W Z : C}
    (m : Z ≅ V ⊗ W) (v : F.obj V ≅ V) (w : F.obj W ≅ W) (z : F.obj Z ≅ Z)
    (h : commutes F (Functor.OplaxMonoidal.δ F _ _ ≫ (v.hom ⊗ₘ w.hom)) z.hom m.inv) :
    z.inv ≫ F.map m.hom ≫ Functor.OplaxMonoidal.δ F _ _ = m.hom ≫ (v.inv ⊗ₘ w.inv) := by
  apply (cancel_epi z.hom).1
  apply (cancel_epi (F.map m.inv)).1
  apply (cancel_mono (v ⊗ᵢ w).hom).1
  simp only [tensorIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp,
    tensorHom_comp_tensorHom, Iso.inv_hom_id, id_tensorHom_id, Category.comp_id]
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω] [Fact (ringChar Ω).Prime]
  [Fact (ringChar Ω ≠ ℓ)]

set_option hygiene false in
local notation "D" => DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (point Ω).left) Ab.{u+1})
  (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point Ω).left))
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "U" => 𝟙_ D
local notation "T" => curriedTensor D

/-- Pullback along a geometric point endomorphism preserves the ordered shifted-unit
splitting. Use the compatibility of the derived tensor comparison with shifts in the
first and second input (`ProjectionMapShift`), the addition axiom for the pullback's
shift comparison, and the oplax left unit axiom. These are the three factors of
`DerivedCategory.shiftTensorShiftIso` followed by the shifted unitor. -/
public theorem geometricPointShiftedUnitTensor_pullback (σ : (point Ω).left ⟶ (point Ω).left)
    (a b : ℤ) :
    let F : D ⥤ D := CompactSupportClasses.pull (ℓ := ℓ) σ
    letI : F.Monoidal := monoidal_leftDerivedUpperStar Λ σ
    let ε (i : ℤ) := (CompactSupportClasses.pullUnit (ℓ := ℓ) σ (-i)).inv
    let s := (geometricPointShiftedUnitTensorIso ℓ Ω (a := a) (b := b) rfl).hom
    ε (a+b) ≫ F.map s ≫ Functor.OplaxMonoidal.δ F _ _ = s ≫ (ε a ⊗ₘ ε b) := by
  intro F ε s
  let : F.Monoidal := monoidal_leftDerivedUpperStar Λ σ
  let : F.CommShift ℤ := inferInstanceAs ((upperStar Λ σ).leftDerivedFunctor.CommShift ℤ)
  let comm := isCommMonObj_condensedRingObj Λ (point Ω).left
  let : MonoidalClosed (PointMod ℓ Ω) := @Mod.monoidalClosed _ _ _ _ _ _ _ _ _ comm
  let : SymmetricCategory (PointMod ℓ Ω) := @Mod.symmetricCategory _ _ _ _ _ _ _ _ _ comm
  let : (T).CommShift₂ CommShift₂Setup.int := DerivedCategory.commShift₂CurriedTensor _
  let (K : D) : ((T).obj K).CommShift ℤ := commShiftTensorLeftFamily Λ (point Ω).left K
  let (K : D) : ((T).flip.obj K).CommShift ℤ := commShiftTensorRightFamily Λ (point Ω).left K
  let η := (leftDerivedUpperStarUnitIso Λ σ).hom
  let pair {X Y : D} (x : F.obj X ⟶ X) (y : F.obj Y ⟶ Y) :=
    Functor.OplaxMonoidal.δ F X Y ≫ (x ⊗ₘ y)
  have left {X Y : D} (x : F.obj X ⟶ X) (y : F.obj Y ⟶ Y) (i : ℤ) :
      commutes F (pair (shiftedDatum F i x) y) (shiftedDatum F i (pair x y))
        ((((T).flip.obj Y).commShiftIso i).hom.app X) := by
    let constraint : (T).flip.obj Y ⋙ F ⟶ F ⋙ (T).flip.obj (F.obj Y) :=
      Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ σ) Y
    let τ : (T).flip.obj Y ⋙ F ⟶ F ⋙ (T).flip.obj Y := constraint ≫ Functor.whiskerLeft F ((T).flip.map y)
    have : NatTrans.CommShift ((T).flip.map y) ℤ :=
      Functor.CommShift₂.commShift_flip_map (G := T) (h := .int) y
    have : NatTrans.CommShift constraint ℤ :=
      commShift_leftDerivedUpperStarTensor_flipApp Λ σ _
    have : NatTrans.CommShift τ ℤ := by dsimp only [τ]; infer_instance
    have chart {V : D} (v : F.obj V ⟶ V) : τ.app V ≫ ((T).flip.obj Y).map v = pair v y :=
      (Category.assoc _ _ _).trans (congrArg (fun z ↦ Functor.OplaxMonoidal.δ F _ _ ≫ z)
        (MonoidalCategory.tensorHom_def' _ _).symm)
    have eq := functorShiftDatum F ((T).flip.obj Y) τ x i
    exact (congrArg₂ (fun l r ↦ commutes F l (shiftedDatum F i r) _)
      (chart (shiftedDatum F i x)) (chart x)) ▸ eq
  have right {X Y : D} (x : F.obj X ⟶ X) (y : F.obj Y ⟶ Y) (i : ℤ) :
      commutes F (pair x (shiftedDatum F i y)) (shiftedDatum F i (pair x y))
        ((((T).obj X).commShiftIso i).hom.app Y) := by
    let constraint : (T).obj X ⋙ F ⟶ F ⋙ (T).obj (F.obj X) :=
      (leftDerivedUpperStarTensor Λ σ).app X
    let τ : (T).obj X ⋙ F ⟶ F ⋙ (T).obj X := constraint ≫ Functor.whiskerLeft F ((T).map x)
    have : NatTrans.CommShift ((T).map x) ℤ :=
      Functor.CommShift₂.commShift_map (G := T) (h := .int) x
    have : NatTrans.CommShift constraint ℤ :=
      commShift_leftDerivedUpperStarTensor_app Λ σ _
    have : NatTrans.CommShift τ ℤ := by dsimp only [τ]; infer_instance
    have chart {V : D} (v : F.obj V ⟶ V) : τ.app V ≫ ((T).obj X).map v = pair x v :=
      (Category.assoc _ _ _).trans (congrArg (fun z ↦ Functor.OplaxMonoidal.δ F _ _ ≫ z)
        (MonoidalCategory.tensorHom_def _ _).symm)
    have eq := functorShiftDatum F ((T).obj X) τ y i
    exact (congrArg₂ (fun l r ↦ commutes F l (shiftedDatum F i r) _)
      (chart (shiftedDatum F i y)) (chart y)) ▸ eq
  have unitor : commutes F (pair η η) η (λ_ U).hom := unitDatum F
  let i := -a
  let j := -b
  have first := left η (shiftedDatum F j η) i
  have second := shiftDatumMap F (right η η j) i
  have third := addDatum F (pair η η) j i (i+j) (add_comm j i)
  have eq := composeDatum F first (composeDatum F second (composeDatum F third
    (shiftDatumMap F unitor (i+j))))
  have degree : i+j = -(a+b) := by dsimp [i,j]; omega
  have combined := composeDatum F eq (castDatum F η degree)
  apply splitDatum F (geometricPointShiftedUnitTensorIso ℓ Ω (a := a) (b := b) rfl)
    (CompactSupportClasses.pullUnit (ℓ := ℓ) σ (-a)) (CompactSupportClasses.pullUnit (ℓ := ℓ) σ (-b))
    (CompactSupportClasses.pullUnit (ℓ := ℓ) σ (-(a+b)))
  let glue := (DerivedCategory.shiftTensorShiftIso (PointMod ℓ Ω) U U i j).hom ≫
    (λ_ U).hom⟦i+j⟧' ≫ eqToHom (congrArg (fun n : ℤ ↦ U⟦n⟧) degree)
  have presentation : (geometricPointShiftedUnitTensorIso ℓ Ω (a := a) (b := b) rfl).inv = glue := by
    dsimp [geometricPointShiftedUnitTensorIso, boundedConstructibleShiftTensorShiftIso, glue]
    simp only [Functor.FullyFaithful.preimageIso, Iso.trans_hom,
      Iso.app_hom, Iso.symm_hom, Iso.app_inv, tensorIso_hom,
      ObjectProperty.ι_commShiftIso_inv_app, ObjectProperty.ι_commShiftIso_hom_app,
      ObjectProperty.FullSubcategory.eqToHom_hom', ObjectProperty.homMk_hom]
    let t := (DerivedCategory.shiftTensorShiftIso (PointMod ℓ Ω) U U i j).hom
    let l := (λ_ U).hom⟦i+j⟧'
    let c := eqToHom (congrArg (fun n : ℤ ↦ U⟦n⟧) degree)
    change ((𝟙 _ ⊗ₘ 𝟙 _) ≫ (((𝟙 _ ⊗ₘ 𝟙 _) ≫ t ≫ 𝟙 _) ≫ l ≫ c) ≫ 𝟙 _) = t ≫ l ≫ c
    simp only [id_tensorHom_id, Category.id_comp, Category.comp_id]
  rw [presentation]
  simp only [glue, DerivedCategory.shiftTensorShiftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Category.assoc] at combined ⊢
  exact combined

end WeilII
