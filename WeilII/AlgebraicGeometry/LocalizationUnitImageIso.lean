module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Balanced
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Localization of the image quotient of the adjunction unit

The proof uses the triangle identity and image factorization from mathlib.
-/

open CategoryTheory CategoryTheory.Limits

namespace WeilII

/-- In a reflective localization, factoring the unit through its image gives the same
localization, provided the image quotient stays epi and the target is balanced.
The triangle identity makes the localized unit invertible. Its first factor is therefore
monic, and by hypothesis epi, hence invertible. -/
public theorem isIso_map_factorThruImage_localizationUnit
    {C D : Type*} [Category* C] [Category* D] [Balanced D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.counit] (N : C)
    [HasImage (adj.unit.app N)] [Epi (L.map (factorThruImage (adj.unit.app N)))] :
    IsIso (L.map (factorThruImage (adj.unit.app N))) := by
  have : IsIso (L.map (adj.unit.app N)) :=
    isIso_of_comp_hom_eq_id _ (adj.left_triangle_components N)
  have : Mono (L.map (factorThruImage (adj.unit.app N))) :=
    mono_of_mono_fac (show L.map (factorThruImage (adj.unit.app N)) ≫
      L.map (image.ι (adj.unit.app N)) = L.map (adj.unit.app N) by
      rw [← L.map_comp, image.fac])
  exact isIso_of_mono_of_epi _

end WeilII
