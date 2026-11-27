module

public import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Tactic.CategoryTheory.Reassoc

/-! # Transporting a pullback square through a natural single-object chart -/

open CategoryTheory

namespace WeilII.ExternalProduct

public section

/-- A square of exact functors computed on singles transports an ordinary equivariant
coefficient map. The chart on the incoming object can be any equivariant presentation. -/
theorem pullChartOfSingleSquare {C D C₀ D₀ : Type*} [Category* C] [Category* D]
    [Category* C₀] [Category* D₀] (J : C₀ ⥤ C) (J' : D₀ ⥤ D)
    (R : C ⥤ D) (F : C ⥤ C) (G : D ⥤ D) (r : C₀ ⥤ D₀) (f : C₀ ⥤ C₀) (g : D₀ ⥤ D₀)
    (d : R ⋙ G ⟶ F ⋙ R) (l : J ⋙ R ⟶ r ⋙ J')
    (lF : J ⋙ F ⟶ f ⋙ J) (lG : J' ⋙ G ⟶ g ⋙ J')
    {K : C} {A : C₀} {B : D₀} (b : K ⟶ J.obj A) (v : r.obj A ⟶ B)
    (φ : F.obj K ⟶ K) (u : f.obj A ⟶ A) (u' : g.obj B ⟶ B)
    (d₀ : g.obj (r.obj A) ⟶ r.obj (f.obj A))
    (a : R.obj K ⟶ J'.obj B) (vK : R.obj (F.obj K) ⟶ R.obj K)
    (wK : G.obj (R.obj K) ⟶ R.obj (F.obj K))
    (s : F.obj (J.obj A) ⟶ J.obj A) (s' : G.obj (J'.obj B) ⟶ J'.obj B)
    (ha : a = R.map b ≫ l.app A ≫ J'.map v) (hvK : vK = R.map φ)
    (hwK : wK = d.app K) (hs : s = lF.app A ≫ J.map u) (hs' : s' = lG.app B ≫ J'.map u')
    (hc : g.map v ≫ u' = d₀ ≫ r.map u ≫ v)
    (hF : φ ≫ b = F.map b ≫ s)
    (hd : d.app (J.obj A) ≫ R.map (lF.app A) ≫ l.app (f.obj A) =
      G.map (l.app A) ≫ lG.app (r.obj A) ≫ J'.map d₀) :
    G.map a ≫ s' = wK ≫ vK ≫ a := by
  subst a vK wK s s'
  have hn := lG.naturality v
  have hm := l.naturality u
  have hb := d.naturality b
  simp only [Functor.comp_map] at hn hm hb
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← J'.map_comp, hc, J'.map_comp, J'.map_comp]
  rw [← reassoc_of% hd, reassoc_of% hb, ← reassoc_of% hm]
  rw [← R.map_comp_assoc φ b, hF]
  simp only [R.map_comp, Category.assoc]

end
end WeilII.ExternalProduct
