module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transport of the unit equation for a mate

We use the unit characterization of mates in Mathlib's
`CategoryTheory.Adjunction.Mates` with natural isomorphisms on the four pullback functors.
-/

open CategoryTheory

namespace WeilII

/-- Transport the unit equation for a square of left adjoints when its right adjoints and
horizontal functors are identified through natural isomorphisms.

The formula for the unit of a transported right adjoint is the original unit followed by the
inverse comparison. Move that comparison past the primed right adjoint's map by naturality.
Naturality of the primed unit then moves the horizontal comparison to the source. Apply the
given unit equation and the comparison of the two pullback squares. Naturality of the source
comparison on the unprimed unit gives the desired other path. This uses the unit formula in
Mathlib's `CategoryTheory.Adjunction.Mates` and `Adjunction.ofNatIsoRight`. -/
public theorem transportExchangeUnit
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {J : A ⥤ B} {R r : B ⥤ A} {J' : A' ⥤ B'} {R' r' : B' ⥤ A'}
    {U u : A ⥤ A'} {V v : B ⥤ B'} (a : J ⊣ R) (a' : J' ⊣ R')
    (cj : r ≅ R) (cj' : r' ≅ R') (cu : u ≅ U) (cv : v ≅ V)
    (K : A) (E : J'.obj (U.obj K) ⟶ V.obj (J.obj K))
    (T : U.obj (R.obj (J.obj K)) ⟶ R'.obj (V.obj (J.obj K)))
    (D : u.obj (r.obj (J.obj K)) ⟶ r'.obj (v.obj (J.obj K)))
    (unit_eq : a'.unit.app (U.obj K) ≫ R'.map E = U.map (a.unit.app K) ≫ T)
    (square_eq : U.map (cj.inv.app (J.obj K)) ≫ cu.inv.app _ ≫ D =
      T ≫ R'.map (cv.inv.app _) ≫ cj'.inv.app _) :
    (a'.ofNatIsoRight cj'.symm).unit.app (u.obj K) ≫
        r'.map (J'.map (cu.hom.app K) ≫ E ≫ cv.inv.app (J.obj K)) =
      u.map ((a.ofNatIsoRight cj.symm).unit.app K) ≫ D := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc]
  rw [← cj'.inv.naturality, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc]
  erw [a'.unit_naturality_assoc (cu.hom.app K), reassoc_of% unit_eq]
  rw [← square_eq, ← U.map_comp_assoc, cu.inv.naturality_assoc]
  simp

end WeilII
