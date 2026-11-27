module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars

open AlgebraicGeometry AlgebraicGeometry.Etale CategoryTheory
open scoped CategoryTheory.Functor

namespace WeilII

universe u

/-- Forgetting the coefficients of a semilinear pullback square gives the same square
on abelian sheaves, via the canonical pullback comparisons. To see this, transpose
along pullback. The comparisons with restriction and forgetting identify each
transposed vertical map with the underlying unit of the module adjunction. -/
public theorem etaleForgetSemilinearPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (ρ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)}
    {M' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (g : M ⟶ (Sheaf.restrictScalars _ ρ).obj N) (g' : M' ⟶ (Sheaf.restrictScalars _ ρ).obj N')
    (i : (f)^*[ModuleCat.{u + 1} A].obj M ⟶ M') (j : (f)^*[ModuleCat.{u + 1} B].obj N ⟶ N')
    (h : (f)^*[ModuleCat.{u + 1} A].map g ≫ (upperStarRestrictScalars ρ f).app N ≫
        (Sheaf.restrictScalars _ ρ).map j = i ≫ g') :
    (f)^*[Ab.{u + 1}].map ((sheafCompose Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A) Ab)).map g) ≫
        upperStarForget₂Comparison B f N ≫
        (sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} B) Ab)).map j =
      (upperStarForget₂Comparison A f M ≫
        (sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A) Ab)).map i) ≫
        (sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A) Ab)).map g' := by
  let p := upperStarLowerStarAdjunction Ab.{u + 1} f
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  have square := congrArg (a.homEquiv _ _) h
  rw [a.homEquiv_naturality_left, a.homEquiv_unit, a.homEquiv_unit,
    Functor.map_comp, ← Category.assoc (a.unit.app _), ← restrictScalars_map_unit_app] at square
  have forgetTranspose (R : Type (u + 1)) [CommRing R]
      {L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
      {L' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
      (m : (f)^*[ModuleCat.{u + 1} R].obj L ⟶ L') :
      (p.homEquiv _ _) (upperStarForget₂Comparison R f L ≫
        (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) Ab)).map m) =
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} R) Ab)).map
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).homEquiv _ _) m) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, unit_comp_lowerStar_map_upperStarForget₂Comparison, Functor.map_comp]
    rfl
  apply (p.homEquiv _ _).injective
  erw [p.homEquiv_naturality_left, forgetTranspose B j, Category.assoc, ← Functor.map_comp,
    forgetTranspose A (i ≫ g')]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  ext U x
  exact congrArg (fun α ↦ (α.hom.app U).hom x) square

end WeilII
