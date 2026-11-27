module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Transporting a slice structure along an isomorphism of schemes -/

open AlgebraicGeometry CategoryTheory Limits

namespace WeilII.SchemeSlice

universe u

variable {B U V : Scheme.{u}} {X Y : Over B}

/-- Give the source of an isomorphism the field or base structure of its target. -/
public abbrev over (X : Over B) {U : Scheme} (i : U ≅ X.left) : Over B :=
  Over.mk (i.hom ≫ X.hom)

/-- The given isomorphism viewed over the transported base structure. -/
public abbrev iso (X : Over B) {U : Scheme} (i : U ≅ X.left) : over X i ≅ X :=
  Over.isoMk i

/-- A map commuting with the two isomorphisms is over the transported structures. -/
public abbrev map (f : X ⟶ Y) (i : U ≅ X.left) (j : V ≅ Y.left) (g : U ⟶ V)
    (w : CommSq i.hom g f.left j.hom) : over X i ⟶ over Y j :=
  Over.homMk g (by
    change g ≫ j.hom ≫ Y.hom = i.hom ≫ X.hom
    rw [← reassoc_of% w.w, Over.w])

public instance (i : U ≅ X.left) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (over X i).hom := by
  change LocallyOfFiniteType (i.hom ≫ X.hom)
  infer_instance

public instance (i : U ≅ X.left) [QuasiCompact X.hom] : QuasiCompact (over X i).hom := by
  change QuasiCompact (i.hom ≫ X.hom)
  infer_instance

public instance (i : U ≅ X.left) [IsSeparated X.hom] : IsSeparated (over X i).hom := by
  change IsSeparated (i.hom ≫ X.hom)
  infer_instance

/-- The comparison with the original edge is a cartesian square in the slice. -/
public theorem edge (f : X ⟶ Y) (i : U ≅ X.left) (j : V ≅ Y.left) (g : U ⟶ V)
    (w : CommSq i.hom g f.left j.hom) :
    IsPullback (iso X i).hom (map f i j g w) f (iso Y j).hom :=
  IsPullback.of_horiz_isIso ⟨Over.OverMorphism.ext w.w⟩

end WeilII.SchemeSlice
