module

public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsRestrictScalarsMate
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.Adjunction.MateTransposeIsIso

/-! # Two adjoint forms of the coefficient square on sheaves -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Etale AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilII

variable {A B : Type (u+1)} [CommRing A] [CommRing B] (ρ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- Taking adjoints of the four sides identifies the restriction and extension formulations
of a square of coefficient maps on sheaves. -/
theorem etaleSheafScalarSquare_iff
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A)} {M' : Sheaf Z.smallEtaleTopology (ModuleCat.{u+1} A)}
    {N : Sheaf X.smallEtaleTopology (ModuleCat.{u+1} B)} {N' : Sheaf Z.smallEtaleTopology (ModuleCat.{u+1} B)}
    (u : (Sheaf.extendScalars _ ρ).obj M ⟶ N) (v : (Sheaf.extendScalars _ ρ).obj M' ⟶ N')
    (j : (i)^*[ModuleCat.{u+1} A].obj M ⟶ M') (k : (i)^*[ModuleCat.{u+1} B].obj N ⟶ N') :
    ((i)^*[ModuleCat.{u+1} A].map ((Sheaf.extendScalarsAdjunction _ ρ).homEquiv _ _ u) ≫
      (upperStarRestrictScalarsIso ρ i).hom.app _ ≫ (Sheaf.restrictScalars _ ρ).map k =
      j ≫ (Sheaf.extendScalarsAdjunction _ ρ).homEquiv _ _ v) ↔
    ((i)^*[ModuleCat.{u+1} B].map u ≫ k = (sheafExtendScalarsCompUpperStarIso ρ i).hom.app _ ≫
      (Sheaf.extendScalars _ ρ).map j ≫ v) := by
  let a := Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ
  let b := Sheaf.extendScalarsAdjunction Z.smallEtaleTopology ρ
  let ex := sheafExtendScalarsCompUpperStarIso ρ i
  have t := a.homEquiv_symm_map_comp_app b (upperStarRestrictScalarsIso ρ i).hom (a.homEquiv _ _ u)
  have hm : (mateEquiv a b).symm (upperStarRestrictScalarsIso ρ i).hom = ex.inv := by
    apply (mateEquiv a b).injective
    rw [Equiv.apply_symm_apply]
    exact (mateEquiv_sheafExtendScalarsCompUpperStarIso_inv ρ i).symm
  rw [hm, Equiv.symm_apply_apply] at t
  rw [← (b.homEquiv _ _).symm.injective.eq_iff, ← Category.assoc, b.homEquiv_naturality_right_symm,
    t, b.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, Category.assoc]
  exact (ex.app M).inv_comp_eq

end WeilII
