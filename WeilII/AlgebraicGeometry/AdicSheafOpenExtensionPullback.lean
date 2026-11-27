module

public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
import WeilII.AlgebraicGeometry.AdicPullSquareMate

/-! # Open extension by zero and pullback of geometric adic sheaves -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilII

universe u

/-- For a cartesian square over an open immersion, the inverse mate of the pullback
square on adic sheaves is invertible. Its conjugate along the composite adjunctions
is weakly étale base change applied to the open immersion. -/
public theorem isIso_adicSheafOpenExtensionPullbackMate
    (ℓ : ℕ) [Fact ℓ.Prime] {U' U T Y : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ T}
    {j : U ⟶ Y} {b : T ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j b) :
    IsIso ((mateEquiv (adicOpenImmersionLowerShriekAdjunction ℓ j)
      (adicOpenImmersionLowerShriekAdjunction ℓ j')).symm
        (TwoSquare.mk _ _ _ _ (adicUpperStarCompIso ℓ sq.w).hom)) := by
  let adjA := adicUpperStarLowerStarAdjunction ℓ a
  let adjB := adicUpperStarLowerStarAdjunction ℓ b
  let extJ := adicOpenImmersionLowerShriekAdjunction ℓ j
  let extJ' := adicOpenImmersionLowerShriekAdjunction ℓ j'
  let θ := TwoSquare.mk _ _ _ _ (adicUpperStarCompIso ℓ sq.w).hom
  let e := (mateEquiv extJ extJ').symm θ
  have : IsIso (conjugateEquiv (extJ.comp adjB) (adjA.comp extJ') e) := by
    rw [← iterated_mateEquiv_conjugateEquiv extJ extJ' adjA adjB e,
      show mateEquiv extJ extJ' e = θ from Equiv.apply_symm_apply _ _,
      mate_adicUpperStarCompIso_eq_baseChangeMap ℓ sq.toCommSq]
    exact isIso_adicBaseChangeMap_of_isPullback ℓ sq
  exact conjugateEquiv_of_iso (extJ.comp adjB) (adjA.comp extJ') e

end WeilII
