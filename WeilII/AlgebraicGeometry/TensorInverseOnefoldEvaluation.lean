module

public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily

/-! # Evaluation in the integer tensor powers of a tensor-invertible object -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace WeilII

/-- In the integer tensor family, multiplication at `(1,-1)` removes the trailing unit
from each onefold tensor power and then applies the chosen evaluation. -/
theorem tensorInverse_onefoldEvaluation {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {L : C} (e : TensorInverse L) :
    (e.intTensorFamily.addIso 1 (-1)).hom =
      ((ρ_ L).hom ⊗ₘ (ρ_ e.obj).hom) ≫ e.rightIso.hom := by
  change (e.addIso 1 (-1) 0 rfl).hom = _
  rw [e.addIso_succ 0 1 (-1) (-1) 0 (by decide) (by decide) (by decide) (by decide),
    e.addIso_zero_left]
  simp only [TensorInverse.succIso, eqToIso_refl, Iso.refl_trans]
  change (𝟙 _ ▷ _) ≫ (α_ L _ _).hom ≫ L ◁ ((λ_ _).hom ≫ 𝟙 _) ≫
    (L ◁ (ρ_ e.obj).hom ≫ e.rightIso.hom) = _
  simp only [id_whiskerRight, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc]
  apply congrArg (· ≫ e.rightIso.hom)
  monoidal

end WeilII
