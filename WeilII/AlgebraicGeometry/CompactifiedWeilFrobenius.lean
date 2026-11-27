module

public import WeilConjectures.WeilSheaf.SmoothPurityShriekWeilUniversality
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedExactLift

/-! # Descent on the geometric fibre of an arithmetic compactification -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Endofunctor CategoryTheory.Limits
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilII

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
  (c : Compactification f) (h : f ≫ t = s)
  (M : DerivedCategory (IsoAlgebra (lowerStar Λ s.geometricGaloisFrobenius.asIso.inv)))

/-- The descent map of the compactification on the geometric fibre, expressed
as the proper pushforward of the open extension's descent map preceded by
the proper exchange with inverse Frobenius pushforward. -/
def compactifiedWeilFrobenius :
    (lowerStar Λ t.geometricGaloisFrobenius.asIso.inv).mapDerivedCategory.obj
      ((rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h)).obj
        ((IsoAlgebra.forget _).mapDerivedCategory.obj M)) ⟶
      (rightDerivedLowerShriekOfCompactification Λ (c.geometricFiber h)).obj
        ((IsoAlgebra.forget _).mapDerivedCategory.obj M) :=
  let ej := openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ c.i (c.i_comp_g_comp h)
  let ep := lowerStarGeometricFiberMapCompFrobeniusIso Λ c.g (rfl : c.g ≫ t = c.g ≫ t)
  transportWeilDatum _ (IsoAlgebra.derivedCommIso ep).symm
    (transportWeilDatum _ (IsoAlgebra.derivedExactCommIso ej).symm
      ((IsoAlgebra.derivedStrIso _).hom.app M))

/-- Forgetting the Weil compact-support functor preserves its descent datum.
The proper factor uses the right-derived forgetful square, and the image of
the exact forgetful square gives the open factor. -/
theorem compactifiedWeilFrobenius_forget :
    IsWeilEquivariant (lowerStar Λ t.geometricGaloisFrobenius.asIso.inv).mapDerivedCategory
      ((IsoAlgebra.derivedStrIso _).hom.app ((weilRightDerivedLowerShriek Λ c h).obj M))
      (compactifiedWeilFrobenius Λ c h M)
      ((weilRightDerivedLowerShriekCompForgetIso Λ c h).hom.app M) := by
  let ej := openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ c.i (c.i_comp_g_comp h)
  let ep := lowerStarGeometricFiberMapCompFrobeniusIso Λ c.g (rfl : c.g ≫ t = c.g ≫ t)
  let J := (IsoAlgebra.mapOfNatIso ej).mapDerivedCategory.obj M
  let R := (lowerStar Λ (Scheme.Hom.geometricFiberMap c.g (rfl : c.g ≫ t = c.g ≫ t))).rightDerivedFunctor
  have hj := (IsoAlgebra.isWeilEquivariant_derivedExactForgetCommIso_hom_app ej M).map R
    (IsoAlgebra.derivedCommIso ep).symm
  have hp : IsWeilEquivariant _
      ((IsoAlgebra.derivedStrIso _).hom.app ((IsoAlgebra.mapOfNatIso ep).rightDerivedFunctor.obj J))
      (transportWeilDatum R (IsoAlgebra.derivedCommIso ep).symm ((IsoAlgebra.derivedStrIso _).hom.app J))
      ((IsoAlgebra.derivedForgetCommIso ep).hom.app J) :=
    (IsoAlgebra.derivedStrIso_hom_app_comp_derivedForgetCommIso ep J).symm
  have component : (weilRightDerivedLowerShriekCompForgetIso Λ c h).hom.app M =
      (IsoAlgebra.derivedForgetCommIso ep).hom.app J ≫
        R.map ((IsoAlgebra.derivedExactForgetCommIso ej).hom.app M) := by
    dsimp only [weilRightDerivedLowerShriekCompForgetIso, IsoAlgebra.exactRightDerivedForgetIso,
      Adjunction.compForgetIso, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Iso.symm_hom, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    simp only [Category.id_comp, Category.comp_id]
    have same : Functor.mapDerivedCategoryCompForgetIso (IsoAlgebra.mapOfNatIsoCompForgetIso ej) =
        IsoAlgebra.derivedExactForgetCommIso ej := by
      simp only [Functor.mapDerivedCategoryCompForgetIso, IsoAlgebra.derivedExactForgetCommIso,
        Iso.trans_assoc]
    exact congrArg (fun e ↦ (IsoAlgebra.derivedForgetCommIso ep).hom.app J ≫ R.map (e.hom.app M)) same
  rw [component]
  exact hp.comp hj

end WeilII
