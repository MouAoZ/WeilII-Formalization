module

public import Mathlib.CategoryTheory.Monoidal.Functor

namespace WeilII

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

/-- The oplax tensor comparison combines two commuting squares, one on each tensor factor.
In the Künneth target square the factors are the pullbacks along the two projections. -/
public theorem oplaxMonoidal_tensor_square
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.OplaxMonoidal] {A₁ A₂ B₁ B₂ : C} {X₁ X₂ Y₁ Y₂ : D}
    {j₁ : A₁ ⟶ B₁} {j₂ : A₂ ⟶ B₂} {k₁ : X₁ ⟶ Y₁} {k₂ : X₂ ⟶ Y₂}
    {u₁ : F.obj A₁ ⟶ X₁} {u₂ : F.obj A₂ ⟶ X₂}
    {v₁ : F.obj B₁ ⟶ Y₁} {v₂ : F.obj B₂ ⟶ Y₂}
    (h₁ : F.map j₁ ≫ v₁ = u₁ ≫ k₁) (h₂ : F.map j₂ ≫ v₂ = u₂ ≫ k₂) :
    F.map (j₁ ⊗ₘ j₂) ≫ δ F B₁ B₂ ≫ (v₁ ⊗ₘ v₂) =
      δ F A₁ A₂ ≫ (u₁ ⊗ₘ u₂) ≫ (k₁ ⊗ₘ k₂) := by
  rw [← δ_natural_assoc F j₁ j₂]
  simp only [tensorHom_comp_tensorHom, h₁, h₂]

end WeilII
