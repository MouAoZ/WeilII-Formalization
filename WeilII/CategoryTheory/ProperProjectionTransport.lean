module

public import Mathlib.CategoryTheory.NatIso

/-! # Transport of a projection-formula square along proper identifications -/

@[expose] public section

open CategoryTheory

namespace WeilII

/-- A direct-image projection square transports along its two forget-supports comparisons.
Only the target comparison needs to be invertible. -/
theorem projectionSquare_of_forgetSupports
    {C D V : Type*} [Category* C] [Category* D] [Category* V]
    (J : C ⥤ C) (J' : D ⥤ D) (F : C ⥤ D) {L S : V ⥤ D} (e : L ≅ S)
    {x y z w : C} {m k l v : V}
    (a : x ⟶ y) (b : z ⟶ w) (s : F.obj y ⟶ S.obj m) (t : F.obj w ⟶ S.obj k)
    (g : k ⟶ l) (p : l ⟶ v)
    (q : J.obj x ⟶ z) (r : J.obj y ⟶ w)
    (q' : J'.obj (L.obj m) ⟶ L.obj v) (r' : J'.obj (S.obj m) ⟶ S.obj v)
    (d : F.obj (J.obj x) ⟶ J'.obj (F.obj x))
    (d' : F.obj (J.obj y) ⟶ J'.obj (F.obj y))
    (h₁ : q ≫ b = J.map a ≫ r)
    (h₂ : q' ≫ e.hom.app v = J'.map (e.hom.app m) ≫ r')
    (hn : F.map (J.map a) ≫ d' = d ≫ J'.map (F.map a))
    (hs : F.map r ≫ t ≫ S.map (g ≫ p) = d' ≫ J'.map s ≫ r') :
    F.map q ≫ (F.map b ≫ t ≫ e.inv.app k) ≫ L.map g ≫ L.map p =
      d ≫ J'.map (F.map a ≫ s ≫ e.inv.app m) ≫ q' := by
  apply (cancel_mono (e.hom.app v)).1
  simp only [Category.assoc, e.hom.naturality, e.hom.naturality_assoc, e.inv_hom_id_app_assoc,
    h₂, Functor.map_comp]
  rw [← F.map_comp_assoc, h₁, F.map_comp_assoc, ← S.map_comp, hs, reassoc_of% hn]
  rw [← J'.map_comp_assoc (e.inv.app m), e.inv_hom_id_app, Functor.map_id, Category.id_comp]

end WeilII
