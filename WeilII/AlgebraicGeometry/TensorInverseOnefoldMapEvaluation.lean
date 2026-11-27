module

public import WeilII.AlgebraicGeometry.TensorInverseComparisonEvaluation
public import WeilII.AlgebraicGeometry.TensorInverseOnefoldEvaluation
import WeilII.AlgebraicGeometry.EtaleKummerTateSheafReduction
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Onefold evaluation under comparison of monoidal images -/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

private theorem onefoldUnitorComp {C B D : Type*} [Category* C] [Category* B] [Category* D]
    [MonoidalCategory C] [MonoidalCategory B] [MonoidalCategory D]
    (F : C ⥤ D) (G : B ⥤ D) [F.Monoidal] [G.Monoidal]
    {L : C} {M : B} {N : D} (p : F.obj L ≅ N) (q : G.obj M ≅ N) :
    (TensorInverse.tensorPowNatMapIso F p 1 ≪≫
      (TensorInverse.tensorPowNatMapIso G q 1).symm).hom ≫ G.map (ρ_ M).hom =
        F.map (ρ_ L).hom ≫ (p ≪≫ q.symm).hom := by
  apply (cancel_mono q.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← tensorPowNatMapIso_one_unitor G q, Iso.inv_hom_id_assoc, tensorPowNatMapIso_one_unitor]

private theorem map_onefold {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {L : C} (e : TensorInverse L) :
    μ F _ _ ≫ F.map (e.intTensorFamily.addIso 1 (-1)).hom ≫ η F =
      (F.map (ρ_ L).hom ⊗ₘ F.map (ρ_ e.obj).hom) ≫ (e.map F).rightIso.hom := by
  rw [tensorInverse_onefoldEvaluation]
  erw [F.map_comp, Category.assoc, ← μ_natural_assoc]
  simp [TensorInverse.map]
  rfl

/-- For two monoidal images compared through a common inverse, the comparisons at
one and minus one intertwine evaluation if both left evaluations are braided right
evaluations. This applies to a line and its sheaf dual. -/
theorem tensorInverse_onefoldMapEvaluation {C B D : Type*} [Category* C] [Category* B] [Category* D]
    [MonoidalCategory C] [MonoidalCategory B] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) (G : B ⥤ D) [F.Monoidal] [G.Monoidal]
    {L : C} {M : B} (e : TensorInverse L) (b : TensorInverse M)
    (h : F.obj L ≅ G.obj M) (t : TensorInverse (G.obj M))
    (hf : (e.map F).leftIso.hom = (β_ _ _).hom ≫ (e.map F).rightIso.hom)
    (hg : (b.map G).leftIso.hom = (β_ _ _).hom ≫ (b.map G).rightIso.hom) :
    let c (m : ℤ) := e.zpowMapIso t F h m ≪≫ (b.zpowMapIso t G (Iso.refl _) m).symm
    μ F _ _ ≫ F.map (e.intTensorFamily.addIso 1 (-1)).hom ≫ η F =
      ((c 1).hom ⊗ₘ (c (-1)).hom) ≫ μ G _ _ ≫ G.map (b.intTensorFamily.addIso 1 (-1)).hom ≫ η G := by
  let a := (e.map F).ofIso h
  let v := (b.map G).ofIso (Iso.refl _)
  let k := a.objIso t ≪≫ (v.objIso t).symm
  have hk := tensorInverse_comparison_leftEvaluation a v t
  change k.hom ▷ G.obj M ≫ (_ ◁ (𝟙 _) ≫ (b.map G).leftIso.hom) =
    _ ◁ h.inv ≫ (e.map F).leftIso.hom at hk
  simp only [whiskerLeft_id, Category.id_comp] at hk
  have hl : (k.hom ⊗ₘ h.hom) ≫ (b.map G).leftIso.hom = (e.map F).leftIso.hom := by
    erw [tensorHom_def', Category.assoc, hk, ← whiskerLeft_comp_assoc, h.hom_inv_id,
      whiskerLeft_id, Category.id_comp]
  have hr : (h.hom ⊗ₘ k.hom) ≫ (b.map G).rightIso.hom = (e.map F).rightIso.hom := by
    apply (cancel_epi (β_ (F.obj e.obj) (F.obj L)).hom).1
    erw [← BraidedCategory.braiding_naturality_assoc, ← hg, hl, ← hf]
  dsimp only
  erw [map_onefold F e, map_onefold G b, tensorHom_comp_tensorHom_assoc]
  have hp := onefoldUnitorComp F G h (Iso.refl _)
  have hn := onefoldUnitorComp F G (a.objIso t) (v.objIso t)
  simp only [Iso.trans_refl, Iso.refl_symm] at hp
  change _ = ((_ ≫ G.map (ρ_ M).hom) ⊗ₘ (_ ≫ G.map (ρ_ b.obj).hom)) ≫ _
  erw [show (e.zpowMapIso t F h 1 ≪≫ (b.zpowMapIso t G (Iso.refl _) 1).symm).hom ≫
    G.map (ρ_ M).hom = _ from hp,
    show (e.zpowMapIso t F h (-1) ≪≫ (b.zpowMapIso t G (Iso.refl _) (-1)).symm).hom ≫
    G.map (ρ_ b.obj).hom = _ from hn]
  erw [← tensorHom_comp_tensorHom, Category.assoc, hr]

end WeilII
