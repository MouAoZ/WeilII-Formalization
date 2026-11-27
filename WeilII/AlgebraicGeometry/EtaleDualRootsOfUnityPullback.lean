module

public import WeilII.AlgebraicGeometry.EtaleDualRootsOfUnityReductionTower
import WeilII.AlgebraicGeometry.EtaleForgetSemilinearPullback
import WeilII.AlgebraicGeometry.EtaleNegativeTateSheafReductionPullback

open AlgebraicGeometry AlgebraicGeometry.Etale CategoryTheory Opposite

namespace WeilII

universe u

/-- Pullback of a finite dual Tate line as an abelian sheaf. Its module comparison
is composition of pullbacks from the universal invertible-exponent base. -/
@[expose] public noncomputable def etaleDualRootLevelPullbackIso
    {V Z : Scheme.{u}} (p : V ⟶ Z) (ℓ : ℕ) [Fact ℓ.Prime]
    (hZ : IsUnit (ℓ : Γ(Z, ⊤))) (hV : IsUnit (ℓ : Γ(V, ⊤))) (n : ℕ) :
    (upperStar Ab.{u + 1} p).obj ((etaleDualRootsOfUnityReductionTower Z ℓ hZ).obj (op n)) ≅
      (etaleDualRootsOfUnityReductionTower V ℓ hV).obj (op n) :=
  let A := ZModCoeff.{u} (ℓ ^ (n + 1))
  letI : NeZero (ringChar A) :=
    ⟨by rw [ringChar.eq A (ℓ ^ (n + 1))]; exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  letI : HasInvertibleExponent A Z :=
    ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos _, ULift.ext (ZMod.natCast_self _),
      by simpa only [Nat.cast_pow] using hZ.pow (n + 1)⟩
  letI : HasInvertibleExponent A V := .of_hom p
  letI : IsIso (upperStarForget₂Comparison A p (tateTwistSheaf A Z (-1))) :=
    isIso_upperStarForget₂Comparison A p _
  let e₁ := asIso (upperStarForget₂Comparison A p (tateTwistSheaf A Z (-1)))
  let e₂ :=
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} A) Ab)).mapIso
      ((upperStarComp (ModuleCat.{u + 1} A) p _ _
        (comp_toInvertibleExponentBase (Λ := A) p).symm).symm.app
        ((tateSheafTensorInverse A).zpow (-1)))
  e₁ ≪≫ e₂

/-- Pullback of the finite dual lines intertwines the adjacent reductions of
SGA 4, XVI, 3.10(a). Apply pullback compatibility of the negative Tate sheaf to the
quotient of successive residue rings. Forget the module square via the pullback
units and identify its horizontal arrows with the transitions of the tower. -/
public theorem etaleDualRootLevelPullback_naturality
    {V Z : Scheme.{u}} (p : V ⟶ Z) (ℓ : ℕ) [Fact ℓ.Prime]
    (hZ : IsUnit (ℓ : Γ(Z, ⊤))) (hV : IsUnit (ℓ : Γ(V, ⊤))) (n : ℕ) :
    let D := etaleDualRootsOfUnityReductionTower Z ℓ hZ
    let Dg := etaleDualRootsOfUnityReductionTower V ℓ hV
    let f := (homOfLE n.le_succ).op
    (upperStar Ab.{u + 1} p).map (D.map f) ≫ (etaleDualRootLevelPullbackIso p ℓ hZ hV n).hom =
      (etaleDualRootLevelPullbackIso p ℓ hZ hV (n + 1)).hom ≫ Dg.map f := by
  let A (j : ℕ) := ZModCoeff.{u} (ℓ ^ (j + 1))
  let (j : ℕ) : NeZero (ringChar (A j)) :=
    ⟨by rw [ringChar.eq (A j) (ℓ ^ (j + 1))]; exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let (j : ℕ) : HasInvertibleExponent (A j) Z :=
    ⟨ℓ ^ (j + 1), pow_pos (Fact.out : ℓ.Prime).pos _, ULift.ext (ZMod.natCast_self _),
      by simpa only [Nat.cast_pow] using hZ.pow (j + 1)⟩
  let (j : ℕ) : HasInvertibleExponent (A j) V := .of_hom p
  let ρ : A (n + 1) →+* A n :=
    (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) _).ulift
  let g (X : Scheme.{u}) [HasInvertibleExponent (A (n + 1)) X] [HasInvertibleExponent (A n) X] :=
    (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).homEquiv _ _
      (sheafExtendScalarsTateTwistSheafIso ρ X (-1)).hom
  let v (j : ℕ) := (upperStarComp (ModuleCat.{u + 1} (A j)) p _ _
    (comp_toInvertibleExponentBase (Λ := A j) p).symm).inv.app ((tateSheafTensorInverse (A j)).zpow (-1))
  have sq : (upperStar (ModuleCat.{u + 1} (A (n + 1))) p).map (g Z) ≫
      (upperStarRestrictScalars ρ p).app _ ≫ (Sheaf.restrictScalars _ ρ).map (v n) =
      v (n + 1) ≫ g V := etaleNegativeTateSheafReduction_pullback ρ p
  have eq := etaleForgetSemilinearPullback ρ p (g Z) (g V) (v (n + 1)) (v n) sq
  change (upperStar Ab.{u + 1} p).map ((Functor.ofOpSequence _).map _) ≫ _ =
    _ ≫ (Functor.ofOpSequence _).map _
  erw [Functor.ofOpSequence_map_homOfLE_succ _ n, Functor.ofOpSequence_map_homOfLE_succ _ n]
  exact eq

end WeilII
