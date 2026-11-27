module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

open CategoryTheory

namespace WeilII

/-- Two objects representing maps from the image of `F` are isomorphic over the common target. -/
public theorem iso_of_counit_bijections {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B : C} {T : D} (c : F.obj A ⟶ T) (d : F.obj B ⟶ T)
    (hc : ∀ N, Function.Bijective (fun f : N ⟶ A ↦ F.map f ≫ c))
    (hd : ∀ N, Function.Bijective (fun f : N ⟶ B ↦ F.map f ≫ d)) :
    ∃ e : A ≅ B, F.map e.hom ≫ d = c := by
  obtain ⟨f, hf⟩ := (hd A).2 c
  obtain ⟨g, hg⟩ := (hc B).2 d
  refine ⟨⟨f, g, (hc A).1 ?_, (hd B).1 ?_⟩, hf⟩
  · simp only [Functor.map_comp, Category.assoc, hg, hf, Functor.map_id, Category.id_comp]
  · simp only [Functor.map_comp, Category.assoc, hf, hg, Functor.map_id, Category.id_comp]

end WeilII
