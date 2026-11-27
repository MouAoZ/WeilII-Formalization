module

public import WeilII.AlgebraicGeometry.ArithmeticFrobeniusPullSquare
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree
public import WeilConjectures.WeilSheaf.SmoothPurityBaseChangeNormalization
import WeilII.CategoryTheory.RightDerivedExchangeConjugation
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
meta import WeilConjectures.Tactic.ExactByKernel

/-! # Frobenius base change for the direct image on an arithmetic geometric fibre -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
open scoped CategoryTheory.Functor

namespace WeilII

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} (p : X ⟶ Y) (h : p ≫ t = s)

/-- Weakly étale base change for the direct image along the geometric fibre of a
map over a finite field agrees with the right-derived arithmetic inverse-pushforward
square after converting the two Frobenius pullbacks. -/
theorem arithmeticDirectImageFrobeniusExchange
    (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology s.geometricFiber) Ab.{u+1}) (condensedRingObj Λ s.geometricFiber))) :
    let i := Scheme.Hom.geometricFiberMap p h
    let R := (lowerStar Λ i).rightDerivedFunctor
    let sq := Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap p h
    (Functor.mapDerivedCategoryNatIso (upperStarIsoLowerStarInv Λ t.geometricGaloisFrobenius.asIso)).hom.app
        (R.obj K) ≫
      (IsoAlgebra.derivedCommIso (lowerStarGeometricFiberMapCompFrobeniusIso Λ p h)).hom.app K =
      (rightDerivedLowerStarBaseChangeIso Λ sq).hom.app K ≫
        R.map ((Functor.mapDerivedCategoryNatIso
          (upperStarIsoLowerStarInv Λ s.geometricGaloisFrobenius.asIso)).hom.app K) := by
  intro i R sq
  let adj := upperStarLowerStarAdjunction Λ i
  let f := lowerStarGeometricFiberMapCompFrobeniusIso Λ p h
  have H := rightDerivedExchangeConjugation (upperStar Λ i) adj
    (upperStarIsoLowerStarInv Λ s.geometricGaloisFrobenius.asIso)
    (upperStarIsoLowerStarInv Λ t.geometricGaloisFrobenius.asIso)
    (upperStarSquareComparison Λ sq.toCommSq) (IsoAlgebra.leftMateIso adj f) f
    (IsoAlgebra.mateEquiv_leftMateIso_inv adj f) (arithmeticFrobeniusPullSquare Λ p h).1
    K ((rightDerivedLowerStarBaseChangeIso Λ sq).hom.app K)
    (rightDerivedLowerStarBaseChangeIso_hom_app_eq_derivedBaseChange Λ sq K)
  exact_by_kernel H

end WeilII
