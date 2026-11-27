module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Frobenius compatibility of a normalized Künneth morphism -/

open CategoryTheory MonoidalCategory

namespace WeilII

/-- Paste the geometric and coefficient squares for an inverse Künneth map, then transport
its target. Here `E` is the exchange for the compact-support functor `H`. The maps `u` and
`v` are exchange components for the two factors, followed by their coefficient structures
`x` and `y`. The geometric square involves only `u` and `v`, while naturality of Künneth
accounts for `x` and `y`.

Move `F.map c` past the target structure by transport, and move `F.map (H.map e)` past
the exchange by naturality of `E`. Combine the two images under `H` and apply the normalized
coefficient square. The geometric and naturality squares now apply in succession, and
bifunctoriality composes the two tensor maps on the source. -/
public theorem normalizedKunnethImage_of_squares
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    (F : C ⥤ C) [F.OplaxMonoidal] (G : D ⥤ D) (H : D ⥤ C) (E : H ⋙ F ⟶ G ⋙ H)
    {A B A' B' T : C} {Q W N : D}
    (κ : A ⊗ B ⟶ H.obj Q) (κ' : A' ⊗ B' ⟶ H.obj W)
    (e : Q ⟶ N) (c : H.obj N ⟶ T) (n : G.obj N ⟶ N) (z : F.obj T ⟶ T)
    (α : G.obj Q ⟶ W) (β : W ⟶ Q)
    (u : F.obj A ⟶ A') (v : F.obj B ⟶ B') (x : A' ⟶ A) (y : B' ⟶ B)
    (transport : F.map c ≫ z = (E.app N ≫ H.map n) ≫ c)
    (coeff : G.map e ≫ n = α ≫ β ≫ e)
    (geom : F.map κ ≫ E.app Q ≫ H.map α =
      (Functor.OplaxMonoidal.δ F A B ≫ (u ⊗ₘ v)) ≫ κ')
    (naturality : κ' ≫ H.map β = (x ⊗ₘ y) ≫ κ) :
    let γ := κ ≫ H.map e ≫ c
    F.map γ ≫ z = Functor.OplaxMonoidal.δ F A B ≫ ((u ≫ x) ⊗ₘ (v ≫ y)) ≫ γ := by
  dsimp only
  have h : F.map (H.map e) ≫ E.app N = E.app Q ≫ H.map (G.map e) := E.naturality e
  simp only [F.map_comp, Category.assoc, transport, reassoc_of% h]
  rw [← H.map_comp_assoc, coeff]
  simp only [H.map_comp, Category.assoc, reassoc_of% geom, reassoc_of% naturality,
    tensorHom_comp_tensorHom_assoc]

end WeilII
