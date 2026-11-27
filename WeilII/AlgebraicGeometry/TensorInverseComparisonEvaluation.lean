module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.TensorInverseZPowMap
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # Comparing the evaluations of two inverse objects through a common inverse -/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace WeilII

/-- Comparing two inverse objects through a common third inverse intertwines their
left evaluations. The two comparisons use the same coevaluation of the third inverse. -/
theorem tensorInverse_comparison_leftEvaluation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] {L : C} (a b t : TensorInverse L) :
    ((a.objIso t).hom ≫ (b.objIso t).inv) ▷ L ≫ b.leftIso.hom = a.leftIso.hom := by
  let E := tensorRightEquivalenceOfTensorIso t.rightIso t.leftIso
  let k : a.obj ⟶ b.obj := E.functor.preimage (a.leftIso.hom ≫ b.leftIso.inv)
  have hk : k ▷ L = a.leftIso.hom ≫ b.leftIso.inv := E.functor.map_preimage _
  have he : k ▷ L ≫ b.leftIso.hom = a.leftIso.hom := by simp [hk]
  have hc : k ≫ (b.objIso t).hom = (a.objIso t).hom := by
    simp only [TensorInverse.objIso, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      whiskerRightIso_hom]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
      associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc, he]
  rw [← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact he

end WeilII
