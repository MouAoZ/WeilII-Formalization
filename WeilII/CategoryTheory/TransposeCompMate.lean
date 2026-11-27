module

public import Mathlib.CategoryTheory.Adjunction.Mates

namespace WeilII

open CategoryTheory

/-- Transposing a morphism across a square of left adjoints maps its transpose
along the horizontal functor and composes with the right-adjoint mate. -/
public theorem homEquiv_comp_mate
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {J : C ⥤ E} {K : D ⥤ F} (a : L ⊣ R) (b : L' ⊣ R') (s : J ⋙ L' ⟶ L ⋙ K)
    {W : C} {M : D} (u : W ⟶ R.obj M) :
    b.homEquiv _ _ (s.app W ≫ K.map ((a.homEquiv _ _).symm u)) =
      J.map u ≫ (mateEquiv a b s).app M := by
  apply (b.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    L'.map_comp, Category.assoc, mateEquiv_counit a b s M, K.map_comp]
  simpa only [Functor.comp_map, Category.assoc] using
    (congrArg (· ≫ K.map (a.counit.app M)) (s.naturality u)).symm

end WeilII
