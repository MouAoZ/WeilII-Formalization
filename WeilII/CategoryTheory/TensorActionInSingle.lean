module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Transport of a tensor action through a functor on coefficients -/

open CategoryTheory MonoidalCategory

namespace WeilII.ExternalProduct

/-- A natural comparison for an endofunctor intertwines tensor actions whenever its
tensor square and the ordinary action square commute. -/
public theorem tensorActionInSingle {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (S : C ⥤ D) (U : C ⥤ C) [U.OplaxMonoidal]
    (H : D ⥤ D) [pullTensor : H.OplaxMonoidal] (c : S ⋙ H ⟶ U ⋙ S) {A B T : C} {i : A ⊗ B ⟶ T}
    {u : U.obj A ⟶ A} {v : U.obj B ⟶ B} {w : U.obj T ⟶ T}
    {l : S.obj A ⊗ S.obj B ⟶ S.obj (A ⊗ B)}
    {l' : S.obj (U.obj A) ⊗ S.obj (U.obj B) ⟶ S.obj (U.obj A ⊗ U.obj B)}
    {a : H.obj (S.obj A) ⟶ S.obj A} {b : H.obj (S.obj B) ⟶ S.obj B}
    {t : H.obj (S.obj T) ⟶ S.obj T}
    (ha : a = c.app A ≫ S.map u) (hb : b = c.app B ≫ S.map v)
    (hw : t = c.app T ≫ S.map w)
    (ht : U.map i ≫ w = Functor.OplaxMonoidal.δ U A B ≫ (u ⊗ₘ v) ≫ i)
    (hd : H.map l ≫ c.app (A ⊗ B) ≫ S.map (Functor.OplaxMonoidal.δ U A B) =
      Functor.OplaxMonoidal.δ H (S.obj A) (S.obj B) ≫ (c.app A ⊗ₘ c.app B) ≫ l')
    (hn : (S.map u ⊗ₘ S.map v) ≫ l = l' ≫ S.map (u ⊗ₘ v)) :
    H.map (l ≫ S.map i) ≫ t =
      Functor.OplaxMonoidal.δ H (S.obj A) (S.obj B) ≫ (a ⊗ₘ b) ≫ l ≫ S.map i := by
  rw [ha, hb, hw]
  have hi := c.naturality i
  dsimp only [Functor.comp_map] at hi
  rw [H.map_comp, Category.assoc, reassoc_of% hi, ← S.map_comp, ht]
  simp only [S.map_comp, reassoc_of% hd, ← reassoc_of% hn,
    tensorHom_comp_tensorHom_assoc]

end WeilII.ExternalProduct
