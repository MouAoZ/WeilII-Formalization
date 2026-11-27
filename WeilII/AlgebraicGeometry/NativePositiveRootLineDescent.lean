module

public import WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.WeilSheaf.SmoothPurityNativeTateDescent

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory

namespace WeilII

universe u

/-- The native positive Weil Tate line is the geometric pullback of the positive
root line on the arithmetic scheme. Transport the condensed descent comparison
through the native equivalence and its compatibility with geometric pullback. -/
public theorem nativePositiveRootLineDescent
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (Z : Scheme.{u}) [Z.Over (Spec (.of k))] :
    Nonempty ((WeilSheaf.tateTwistSheaf k ℓ Z 1).obj ≅
      (ProEtaleWeilSheaf.geometricFiberPullback k ℓ Z).obj
        ((adicSheafEquivCondensedMod ℓ Z).inverse.obj (ProEtale.tateTwist Z ℓ 1))) := by
  let E := adicSheafEquivCondensedMod ℓ Z
  let root := ProEtale.tateTwist Z ℓ 1
  let positive := E.inverse.obj root
  let C := ProEtaleWeilSheaf.toCondensed k ℓ Z
  let descent := CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ)
    (Z ↘ Spec (.of k))
  obtain ⟨t⟩ := WeilSheaf.purity_nonempty_toCondensedTateDescentIso k ℓ Z 1
  have e := (ProEtaleWeilSheaf.geometricFiberPullbackCompToCondensedIso k ℓ Z).app positive
  exact ⟨C.preimageIso (t ≪≫ (descent.mapIso (E.counitIso.app root)).symm ≪≫ e.symm)⟩

end WeilII
