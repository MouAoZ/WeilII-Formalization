module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisons
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Geometric pullback of the free constant coefficient presentation -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

private theorem compAdj {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {U : D ⥤ C} {G : D ⥤ E} {V : E ⥤ D}
    (a : F ⊣ U) (b : G ⊣ V) {x : C} {y : E} (φ : G.obj (F.obj x) ⟶ y) :
    a.homEquiv _ _ (b.homEquiv _ _ φ) = (a.comp b).homEquiv _ _ φ := by
  rw [Adjunction.comp_homEquiv]; rfl

private theorem adjUniq {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {U U' : D ⥤ C} (a : F ⊣ U) (b : F' ⊣ U') (i : U' ≅ U)
    {x : C} {y : D} (φ : F'.obj x ⟶ y) :
    a.homEquiv _ _ ((a.leftAdjointUniq (b.ofNatIsoRight i)).hom.app x ≫ φ) =
      b.homEquiv _ _ φ ≫ i.hom.app y := by
  rw [← Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

private theorem pullConstAdj (C : Type*) [Category.{u+1} C] [Abelian C]
    [IsGrothendieckAbelian.{u+1} C] [HasSmallSiteSheafify C]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : C) {N : Sheaf X.smallEtaleTopology C}
    (φ : (constantSheaf X.smallEtaleTopology C).obj M ⟶ N) :
    (constantSheafAdj Y.smallEtaleTopology C terminalIsTerminal).homEquiv _ _
      ((upperStarLowerStarAdjunction C f).homEquiv _ _
        ((upperStarConstantSheafIso C f).hom.app M ≫ φ)) =
      (constantSheafAdj X.smallEtaleTopology C terminalIsTerminal).homEquiv _ _ φ ≫
        (lowerStarCompSheafSectionsTerminalIso C f).inv.app N := by
  rw [compAdj]
  apply (cancel_mono ((lowerStarCompSheafSectionsTerminalIso C f).hom.app N)).1
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    ← Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_naturality_right,
    upperStarConstantSheafIso, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

private theorem pullFreeAdj (R : Type (u+1)) [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u+1})
    {N : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R)}
    (φ : (extendScalars R X).obj ((f)^*[AddCommGrpCat.{u+1}].obj M) ⟶ N) :
    (extendScalarsAdjunction R Y).homEquiv _ _
      ((upperStarLowerStarAdjunction _ f).homEquiv _ _
        ((upperStarExtendScalarsIso R f).hom.app M ≫ φ)) =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u+1} f).homEquiv _ _
        ((extendScalarsAdjunction R X).homEquiv _ _ φ) := by
  rw [compAdj, compAdj]
  unfold upperStarExtendScalarsIso
  rw [adjUniq]
  exact Category.comp_id _

private theorem constFreeAdj (R : Type (u+1)) [CommRing R] (X : Scheme.{u})
    (M : AddCommGrpCat.{u+1}) {N : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} R)}
    (φ : (constantSheaf X.smallEtaleTopology _).obj ((ModuleCat.extendScalarsAddCommGrp R).obj M) ⟶ N) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u+1} terminalIsTerminal).homEquiv _ _
      ((extendScalarsAdjunction R X).homEquiv _ _ ((constantSheafCompExtendScalarsIso R X).hom.app M ≫ φ)) =
      (ModuleCat.extendScalarsAddCommGrpAdj R).homEquiv _ _
        ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u+1} R) terminalIsTerminal).homEquiv _ _ φ) := by
  rw [compAdj, compAdj]
  unfold constantSheafCompExtendScalarsIso
  rw [adjUniq]
  exact Category.comp_id _

/-- Pulling back the free sheaf on the integers carries its standard basis to the standard basis. -/
theorem etaleKummer_freeBasis_pullback (R : Type (u+1)) [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (upperStarExtendScalarsConstantSheafIntIso R f).hom ≫
        (extendScalarsConstantZModIso X (Λ := R) (n := 0) (by simp)).hom =
      (f)^*[ModuleCat.{u+1} R].map (extendScalarsConstantZModIso Y (Λ := R) (n := 0) (by simp)).hom ≫
        (upperStarConstantSheafIso (ModuleCat.{u+1} R) f).hom.app (ModuleCat.of R R) := by
  let Z := AddCommGrpCat.of (ULift.{u+1} (ZMod 0))
  let k := (ModuleCat.extendScalarsAddCommGrpZModIso (Λ := R) (n := 0) (by simp)).hom
  let RX := constantSheaf X.smallEtaleTopology (ModuleCat.{u+1} R)
  let RY := constantSheaf Y.smallEtaleTopology (ModuleCat.{u+1} R)
  let PX := upperStarLowerStarAdjunction (ModuleCat.{u+1} R) f
  let ZY := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u+1} terminalIsTerminal
  apply (PX.homEquiv _ _).injective
  apply ((extendScalarsAdjunction R Y).homEquiv _ _).injective
  apply (ZY.homEquiv _ _).injective
  simp only [upperStarExtendScalarsConstantSheafIntIso, extendScalarsConstantZModIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc, Functor.map_comp]
  rw [pullFreeAdj, Adjunction.homEquiv_naturality_left]
  erw [pullConstAdj, constFreeAdj]
  rw [PX.homEquiv_naturality_left, PX.homEquiv_naturality_left]
  erw [constFreeAdj]
  let cX := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u+1} R) terminalIsTerminal
  let cY := constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u+1} R) terminalIsTerminal
  let V := ModuleCat.of R R
  let x := RX.obj V
  let d := (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u+1} R) f).inv.app x
  let m := ModuleCat.extendScalarsAddCommGrpAdj R
  have e : cY.homEquiv _ _ (PX.homEquiv _ _ ((upperStarConstantSheafIso _ f).hom.app V)) =
      cX.unit.app V ≫ d := by
    have hv := pullConstAdj (ModuleCat.{u+1} R) f V (𝟙 x)
    erw [Category.comp_id, cX.homEquiv_id] at hv
    exact hv
  have ex : cX.homEquiv _ _ (RX.map k) = k ≫ cX.unit.app V := by
    rw [← Category.comp_id (RX.map k), cX.homEquiv_naturality_left, cX.homEquiv_id]
  change m.homEquiv _ _ (cX.homEquiv _ _ (RX.map k)) ≫ (forget₂ _ AddCommGrpCat.{u+1}).map d =
    m.homEquiv _ _ (cY.homEquiv _ _ (RY.map k ≫ PX.homEquiv _ _ ((upperStarConstantSheafIso _ f).hom.app V)))
  rw [← m.homEquiv_naturality_right, ex, cY.homEquiv_naturality_left, e, Category.assoc]
  rfl

private theorem transport_basis {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (P : C ⥤ D) (S : E ⥤ D) {A B B' : C} {A' : D} {M N M' N' : E}
    (o : A ⟶ B) (g : B ⟶ B') (z : P.obj A ⟶ A') (o' : A' ⟶ S.obj M')
    (i : P.obj B ⟶ S.obj M) (j : P.obj B' ⟶ S.obj N)
    (p : M ⟶ N) (c : M ⟶ M') (q : N ⟶ N') (v : M' ⟶ N')
    (hu : P.map o ≫ i ≫ S.map c = z ≫ o')
    (hn : P.map g ≫ j = i ≫ S.map p) (hq : p ≫ q = c ≫ v) :
    P.map (o ≫ g) ≫ j ≫ S.map q = z ≫ o' ≫ S.map v := by
  rw [P.map_comp, Category.assoc, reassoc_of% hn, ← S.map_comp, hq, S.map_comp,
    ← Category.assoc i, ← Category.assoc, hu, Category.assoc]

open MonoidalCategory in
private theorem unitOnSingles (C : Type*) [Category.{u+1} C] [Abelian C]
    [IsGrothendieckAbelian.{u+1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L((f)^*[C]).map (singleFunctorObjUnitIso C Y).inv ≫
      (singleFunctorCompLeftDerivedUpperStarIso C f).hom.app ((constantSheaf Y.smallEtaleTopology C).obj (𝟙_ C)) ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map
          ((upperStarConstantSheafIso C f).hom.app (𝟙_ C)) =
      (leftDerivedUpperStarUnitIso C f).hom ≫ (singleFunctorObjUnitIso C X).inv := by
  have h := leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp C f
  rw [← constantSinglePullbackIso_source_hom, constantSinglePullbackIso_hom] at h
  exact h

open MonoidalCategory in
private theorem pull_unit_basis (C : Type*) [Category.{u+1} C] [Abelian C]
    [IsGrothendieckAbelian.{u+1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {J : Sheaf Y.smallEtaleTopology C} {I : Sheaf X.smallEtaleTopology C}
    (k : J ≅ (constantSheaf Y.smallEtaleTopology C).obj (𝟙_ C))
    (l : I ≅ (constantSheaf X.smallEtaleTopology C).obj (𝟙_ C))
    (q : (f)^*[C].obj J ⟶ I) (h : q ≫ l.hom =
      (f)^*[C].map k.hom ≫ (upperStarConstantSheafIso C f).hom.app (𝟙_ C))
    (z : L((f)^*[C]).obj (𝟙_ _) ⟶ 𝟙_ _) (hz : (leftDerivedUpperStarUnitIso C f).hom = z) :
    L((f)^*[C]).map ((singleFunctorObjUnitIso C Y).symm ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso k.symm).hom ≫
      (singleFunctorCompLeftDerivedUpperStarIso C f).hom.app J ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map q =
      z ≫ ((singleFunctorObjUnitIso C X).symm ≪≫
        (_root_.DerivedCategory.singleFunctor _ 0).mapIso l.symm).hom := by
  let P := (f)^*[C]
  let S := _root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology C) 0
  let SY := _root_.DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology C) 0
  let c := (upperStarConstantSheafIso C f).hom.app (𝟙_ C)
  have hq : P.map k.inv ≫ q = c ≫ l.inv := by
    apply (cancel_mono l.hom).1
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, h,
      ← P.map_comp_assoc, Iso.inv_hom_id, P.map_id, Category.id_comp]
  let n := (singleFunctorCompLeftDerivedUpperStarIso C f).hom
  have hn := n.naturality k.inv
  dsimp only [Functor.comp_map] at hn
  subst z
  exact transport_basis L(P) S (singleFunctorObjUnitIso C Y).inv (SY.map k.inv)
    _ (singleFunctorObjUnitIso C X).inv (n.app _) (n.app J)
    (P.map k.inv) c q l.inv (unitOnSingles C f) hn hq

/-- The direct degree-zero presentation of the constant unit commutes with geometric pullback. -/
theorem etaleKummer_unitPresentation_pullback (R : Type (u+1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L((f)^*[ModuleCat.{u+1} R]).map (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit Y R).hom ≫
      (singleFunctorCompLeftDerivedUpperStarIso _ f).hom.app _ ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map (upperStarExtendScalarsConstantSheafIntIso R f).hom =
      (leftDerivedUpperStarConstantComplexIso R f).hom ≫
        (constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X R).hom := by
  exact pull_unit_basis (ModuleCat.{u+1} R) f
    (extendScalarsConstantZModIso Y (Λ := R) (n := 0) (by simp))
    (extendScalarsConstantZModIso X (Λ := R) (n := 0) (by simp))
    _ (etaleKummer_freeBasis_pullback R f) _ (leftDerivedUpperStarUnitIso_hom_eq_η f)

/-- Pullback from the exponent base gives the direct degree-zero presentation on every scheme. -/
theorem etaleKummer_presentation_eq_ofUnit (R : Type (u+1)) [CommRing R] (X : Scheme.{u})
    [HasInvertibleExponent R X] :
    constantComplexIsoSingleFunctorExtendScalarsInt X R =
      constantComplexIsoSingleFunctorExtendScalarsIntOfUnit X R := by
  apply Iso.ext
  let f := toInvertibleExponentBase (Λ := R) X
  change (leftDerivedUpperStarConstantComplexIso R f).inv ≫ _ ≫ _ ≫ _ = _
  simp only [Functor.mapIso_hom, Iso.app_hom]
  rw [etaleKummer_unitPresentation_pullback, Iso.inv_hom_id_assoc]

end WeilII
