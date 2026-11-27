module

public import WeilII.AlgebraicGeometry.ArithmeticFrobeniusPullSquare
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedExactLift
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.WeilSheaf.SmoothPurityAmbientOpenExchange
import WeilII.CategoryTheory.ExactOpenExchangeConjugation
meta import WeilConjectures.Tactic.ExactByKernel

/-! # Frobenius base change for extension by zero on an arithmetic geometric fibre -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
open scoped CategoryTheory.Functor

namespace WeilII

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} (j : X ⟶ Y) [IsOpenImmersion j]
  (h : j ≫ t = s)

/-- The exact derived open exchange, conjugated from Frobenius pullback to inverse
pushforward at its endpoints, gives the arithmetic extension-by-zero exchange. -/
theorem arithmeticOpenFrobeniusExchange
    (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology s.geometricFiber) Ab.{u+1}) (condensedRingObj Λ s.geometricFiber))) :
    let i := Scheme.Hom.geometricFiberMap j h
    let J := openImmersionLowerShriek Λ i
    let sq := (Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap j h).flip
    (Functor.mapDerivedCategoryNatIso (upperStarIsoLowerStarInv Λ t.geometricGaloisFrobenius.asIso)).hom.app
        (J.mapDerivedCategory.obj K) ≫
      (IsoAlgebra.derivedExactCommIso (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ j h)).hom.app K =
      (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ sq).hom.app K ≫
        J.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso
          (upperStarIsoLowerStarInv Λ s.geometricGaloisFrobenius.asIso)).hom.app K) := by
  intro i J sq
  let adj := openImmersionLowerShriekUpperStarAdjunction Λ i
  let a := upperStarGeometricFiberMapCompFrobeniusIso Λ j h
  have H := exactOpenExchangeConjugation J adj
    (upperStarIsoLowerStarInv Λ s.geometricGaloisFrobenius.asIso)
    (upperStarIsoLowerStarInv Λ t.geometricGaloisFrobenius.asIso)
    (openImmersionLowerShriekUpperStarBaseChangeIso Λ sq) (IsoAlgebra.leftMateIso adj a)
    (upperStarSquareComparison Λ sq.toCommSq) a
    (purityOpenImmersionLowerShriekUpperStarBaseChangeIso_inv Λ sq)
    (IsoAlgebra.mateEquiv_leftMateIso_inv adj a) (arithmeticFrobeniusPullSquare Λ j h).2 K
  exact_by_kernel H

end WeilII
