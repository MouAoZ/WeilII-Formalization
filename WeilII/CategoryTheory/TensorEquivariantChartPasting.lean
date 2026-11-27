module

public import WeilII.CategoryTheory.OplaxMonoidalTensorSquare

/-! # Composition of equivariant tensor charts -/

open CategoryTheory MonoidalCategory

namespace WeilII.ExternalProduct

/-- Two equivariant maps can be tensored and followed by a third equivariant map. -/
public theorem pasteTensorActions {C : Type*} [Category* C] [MonoidalCategory C]
    (H : C ⥤ C) [H.OplaxMonoidal] {A B A' B' T P Q : C}
    (a : A ⟶ A') (b : B ⟶ B') (m : A' ⊗ B' ⟶ T)
    (i : H.obj T ⟶ T) (f : H.obj A' ⟶ A') (g : H.obj B' ⟶ B')
    (d : H.obj A ⟶ P) (e : H.obj B ⟶ Q) (p : P ⟶ A) (s : Q ⟶ B)
    (ht : H.map m ≫ i = Functor.OplaxMonoidal.δ H A' B' ≫ (f ⊗ₘ g) ≫ m)
    (hp : H.map a ≫ f = d ≫ p ≫ a) (hs : H.map b ≫ g = e ≫ s ≫ b) :
    H.map ((a ⊗ₘ b) ≫ m) ≫ i =
      (Functor.OplaxMonoidal.δ H A B ≫ (d ⊗ₘ e) ≫ (p ⊗ₘ s)) ≫ ((a ⊗ₘ b) ≫ m) := by
  rw [H.map_comp, Category.assoc, ht]
  have square := WeilII.oplaxMonoidal_tensor_square H (u₁ := d) (u₂ := e)
    (k₁ := p ≫ a) (k₂ := s ≫ b) hp hs
  simpa only [Category.assoc, tensorHom_comp_tensorHom_assoc] using (reassoc_of% square) m

end WeilII.ExternalProduct
