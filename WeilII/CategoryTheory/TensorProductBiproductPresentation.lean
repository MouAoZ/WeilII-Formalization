module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Data.Fintype.BigOperators

/-! # Tensor products of finite biproduct presentations -/

public section

open CategoryTheory Limits MonoidalCategory

namespace WeilII

/-- Tensoring two finite families of split summands gives a presentation indexed by ordered
pairs. Each paired summand may be replaced by an isomorphic object. -/
theorem tensorProduct_biproductPresentation {C : Type*} [Category* C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] {A B : C}
    {I J : Type*} [Fintype I] [Fintype J] {X : I → C} {Y : J → C} {Z : I × J → C}
    (i : ∀ a, X a ⟶ A) (p : ∀ a, A ⟶ X a) (j : ∀ b, Y b ⟶ B) (q : ∀ b, B ⟶ Y b)
    (hA : ∑ a, p a ≫ i a = 𝟙 A) (hB : ∑ b, q b ≫ j b = 𝟙 B)
    (dA : ∀ a, i a ≫ p a = 𝟙 _) (dB : ∀ b, j b ≫ q b = 𝟙 _)
    (zA : ∀ a a', a ≠ a' → i a ≫ p a' = 0) (zB : ∀ b b', b ≠ b' → j b ≫ q b' = 0)
    (e : ∀ t : I × J, Z t ≅ X t.1 ⊗ Y t.2) :
    let inc (t : I × J) := (e t).hom ≫ (i t.1 ⊗ₘ j t.2)
    let pr (t : I × J) := (p t.1 ⊗ₘ q t.2) ≫ (e t).inv
    (∑ t, pr t ≫ inc t = 𝟙 (A ⊗ B)) ∧ (∀ t, inc t ≫ pr t = 𝟙 _) ∧
      ∀ t t', t ≠ t' → inc t ≫ pr t' = 0 := by
  dsimp only
  refine ⟨?_, fun t ↦ ?_, fun t t' h ↦ ?_⟩
  · simp only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom,
      Fintype.sum_prod_type, ← tensor_sum, ← sum_tensor, hA, hB, id_tensorHom_id]
  · simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, dA, dB,
      id_tensorHom_id, Category.id_comp, Iso.hom_inv_id]
  · by_cases ha : t.1 = t'.1
    · have hb : t.2 ≠ t'.2 := fun hb ↦ h (Prod.ext ha hb)
      simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, zB _ _ hb,
        MonoidalPreadditive.tensor_zero, zero_comp, comp_zero]
    · simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, zA _ _ ha,
        MonoidalPreadditive.zero_tensor, zero_comp, comp_zero]

end WeilII
