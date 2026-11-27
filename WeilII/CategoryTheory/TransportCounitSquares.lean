module

public import Mathlib.CategoryTheory.Comma.Over.Basic

open CategoryTheory

namespace WeilII

/-- Paste slice isomorphisms for two maps of diagrams after transporting their bases.
The compatibility with the common base is needed only on the ambient objects. -/
public theorem transport_overIso_of_counit_squares
    {C D : Type*} [Category* C] [Category* D] (P : C ⥤ D)
    {A B X Y : C} {E E' F F' T T' : D} {c : A ⟶ X} {d : B ⟶ Y}
    {f : E ⟶ F} {g : E' ⟶ F'} {c' : F ⟶ T} {d' : F' ⟶ T'}
    {x : X ⟶ Y} {v : P.obj X ⟶ T} {v' : P.obj Y ⟶ T'} {y : T ⟶ T'}
    (s : A ≅ B) (hs : s.hom ≫ d = c ≫ x) (h : v ≫ y = P.map x ≫ v')
    (r : Over.mk (f ≫ c') ≅ Over.mk (P.map c ≫ v))
    (r' : Over.mk (g ≫ d') ≅ Over.mk (P.map d ≫ v')) :
    Nonempty (Over.mk (f ≫ c' ≫ y) ≅ Over.mk (g ≫ d')) := by
  let dom := (Over.forget T).mapIso r ≪≫ P.mapIso s ≪≫ (Over.forget T').mapIso r'.symm
  refine ⟨Over.isoMk dom ?_⟩
  change (r.hom.left ≫ P.map s.hom ≫ r'.inv.left) ≫ (g ≫ d') = f ≫ c' ≫ y
  have hr : r.hom.left ≫ P.map c ≫ v = f ≫ c' := Over.w r.hom
  have hr' : r'.inv.left ≫ g ≫ d' = P.map d ≫ v' := Over.w r'.inv
  rw [Category.assoc, Category.assoc, hr', ← P.map_comp_assoc, hs, P.map_comp,
    Category.assoc, ← h]
  simpa only [Category.assoc] using congrArg (· ≫ y) hr

end WeilII
