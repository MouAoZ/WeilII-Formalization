module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilII.CategoryTheory.CounitBijectionIso

open CategoryTheory

namespace WeilII

/-- A fully faithful functor detects an isomorphism of arrows when their targets represent
the same functor and their composites with the representing counits are isomorphic over the base. -/
public theorem arrowIso_of_counit_bijections {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} (ff : F.FullyFaithful) {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B')
    {T : D} (c : F.obj B ⟶ T) (d : F.obj B' ⟶ T)
    (hc : ∀ N, Function.Bijective (fun h : N ⟶ B ↦ F.map h ≫ c))
    (hd : ∀ N, Function.Bijective (fun h : N ⟶ B' ↦ F.map h ≫ d))
    (a : Over.mk (F.map f ≫ c) ≅ Over.mk (F.map g ≫ d)) :
    Nonempty (Arrow.mk f ≅ Arrow.mk g) := by
  obtain ⟨b, hb⟩ := iso_of_counit_bijections F c d hc hd
  let s := ff.preimageIso ((Over.forget T).mapIso a)
  refine ⟨Arrow.isoMk s b ((hd A).1 ?_)⟩
  change F.map (s.hom ≫ g) ≫ d = F.map (f ≫ b.hom) ≫ d
  simp only [F.map_comp, Category.assoc, hb]
  have hs : F.map s.hom = a.hom.left := ff.map_preimage _
  rw [hs]
  exact Over.w a.hom

end WeilII
