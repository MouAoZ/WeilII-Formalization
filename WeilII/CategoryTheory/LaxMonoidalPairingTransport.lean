module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace WeilII

/-- Push a pairing compatible with three structure maps through a lax monoidal functor.
A monoidal natural transformation comparing the old and new endofunctors transports the
structure maps. Naturality of the tensor comparison reduces equivariance to that of the
original pairing, followed by monoidality and naturality of the transformation.
This is the categorical calculation in WeilConjectures, `WeilSheaf.lowerStar_pairing_str`. -/
public theorem laxMonoidal_map_equivariant_pairing
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    (G : C ⥤ D) (F : C ⥤ C) (B : D ⥤ D) [G.LaxMonoidal] [F.LaxMonoidal] [B.LaxMonoidal]
    (τ : G ⋙ B ⟶ F ⋙ G) [NatTrans.IsMonoidal τ] {A P Q : C}
    (a : F.obj A ⟶ A) (p : F.obj P ⟶ P) (q : F.obj Q ⟶ Q) (e : A ⊗ P ⟶ Q)
    (h : (a ⊗ₘ p) ≫ e = μ F A P ≫ F.map e ≫ q) :
    ((τ.app A ≫ G.map a) ⊗ₘ (τ.app P ≫ G.map p)) ≫ (μ G A P ≫ G.map e) =
      μ B (G.obj A) (G.obj P) ≫ B.map (μ G A P ≫ G.map e) ≫ τ.app Q ≫ G.map q := by
  have product := NatTrans.IsMonoidal.tensor (τ := τ) A P
  have natural := τ.naturality e
  simp only [comp_μ, Functor.comp_map, Functor.comp_obj] at product natural
  rw [← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, ← G.map_comp, h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% product, reassoc_of% natural]

end WeilII
