module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

import WeilII.AlgebraicGeometry.EtaleReductionPullbackTensor

/-! # Scalar reduction of the direct-image projection formula -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilII

variable {A B : Type (u+1)} [CommRing A] [CommRing B]
  {ρ : A →+* B} (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
  {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- SGA 4, XVI, 3.8 and 3.10(a). Transpose the two sides under derived pullback and
direct image. The direct-image exchange is the mate of the inverse pullback exchange, so
its composition with the counit is pullback exchange followed by the original counit.
Naturality moves the counit across the scalar tensor comparison. On K-flat resolutions
the remaining square is the monoidal square of sheaf pullback and scalar extension:
both composites apply extension to the pullback of each tensor factor and use the same
balanced map. The derived counits determine that square uniquely (pinned
`Functor.map_leftDerivedTensorComparison_comp_eq_of_counit_of_iso`). The transposes are
therefore equal by `Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`. -/
theorem etaleScalarReduction_directImageProjection
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u+1} A)))
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A))) :
    let F := derivedExtendScalars hρ ha X
    let G := derivedExtendScalars hρ ha Z
    let b := derivedExtendScalarsLowerStarMap hρ ha i
    let J := L((i)^*[ModuleCat.{u+1} A])
    let S := R((i)_*[ModuleCat.{u+1} B])
    F.map (((rightDerivedLowerStarProjectionMap (ModuleCat.{u+1} A) i).app M).app N) ≫
        b.app (M ⊗ J.obj N) ≫ S.map ((derivedExtendScalarsDerivedTensorIso hρ ha Z M _).hom ≫
          (G.obj M ◁ (derivedExtendScalarsPullbackIso hρ ha i).hom.app N)) =
      (derivedExtendScalarsDerivedTensorIso hρ ha X _ N).hom ≫ b.app M ▷ F.obj N ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u+1} B) i).app (G.obj M)).app (F.obj N) := by
  have h := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u+1} A) i)
    |>.map_rightAdjointProjectionMap_comp_mateEquiv
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u+1} B) i)
      (etaleScalarReduction_pullbackTensor hρ ha i) M N
  dsimp only
  simp only [asIso_hom, Functor.OplaxMonoidal.δNatTrans_app_app, Iso.symm_hom, Iso.symm_inv] at h
  rw [derivedExtendScalarsDerivedTensorIso_hom, derivedExtendScalarsDerivedTensorIso_hom]
  exact h

end WeilII
