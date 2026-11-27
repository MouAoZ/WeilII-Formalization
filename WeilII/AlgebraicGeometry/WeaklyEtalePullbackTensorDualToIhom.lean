module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorDualToIhomMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHomEvaluation
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom

/-! # Tensor-dual evaluation under weakly étale pullback

The comparison of pairings in `TensorDualToIhomMap.lean` applies to the weakly étale
internal Hom comparison of `Adic/InternalHomEvaluation.lean`.
-/

public section

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory

namespace WeilII

universe u

attribute [local instance] Sheaf.symmetricCategory
attribute [local instance 25000] SymmetricCategory.toBraidedCategory

/-- Commutativity of the adic coefficient ring for the chosen sheaf braiding, from
`Adic/Hom.lean`. -/
local instance tensorDualPullbackCoefficientsComm {ℓ : ℕ} [Fact ℓ.Prime] (X : Scheme.{u}) :
    IsCommMonObj (adicConstantSheaf ℓ X) :=
  adicConstantSheaf.isCommMonObj X

/-- Let `F` be pullback along a weakly étale morphism. If the canonical evaluation for
`F M` and `F P` is invertible, then so is the pullback of the canonical evaluation for
`M` and `P`.

Write `D = [M,R_Y]` for the dual with respect to the coefficient unit. The weakly étale
comparison gives isomorphisms `ψ_N : F[M,N] ≅ [FM,FN]` compatible with evaluation.
Compose `ψ` at `R_Y` with internal Hom applied to the unit isomorphism `F R_Y ≅ R_Z`
to obtain `δ : F D ≅ [FM,R_Z]`. Naturality of evaluation in its target shows that this
comparison respects the dual pairing after applying the unit isomorphism. The underlying
map of the unit isomorphism is inverse to the ring map defining pullback. The tensor-dual comparison
square thus identifies the pullback of evaluation, via the relative tensor isomorphism and
`ψ_P`, with tensoring by `δ.hom` followed by evaluation for `FM` and `FP`. Tensoring
sends `δ` to an isomorphism, and the latter evaluation is invertible by hypothesis.
Cancelling the two comparison isomorphisms proves the claim.

Sources are `Mod.tensorLeftCompMapModComapIso_inv_app_map_tensorDualToIhom`,
`adicUpperStarIhomIso_evaluation`, and `Mod.evaluation_naturality` in WeilConjectures. -/
theorem isIso_adicUpperStar_map_tensorDualToIhom {ℓ : ℕ} [Fact ℓ.Prime] {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) [WeaklyEtale g] (M P : AdicSheaf ℓ Y)
    (h : IsIso (Mod.tensorDualToIhom ((adicUpperStar ℓ g).obj M) ((adicUpperStar ℓ g).obj P))) :
    IsIso ((adicUpperStar ℓ g).map (Mod.tensorDualToIhom M P)) :=
  open MonoidalCategory Limits in
  set_option backward.isDefEq.respectTransparency.types false in by
  let _ : (g)_*[WeilCoefficients.{u} ℓ].LaxBraided := laxBraided_lowerStar _ g
  let pull := adicUpperStar ℓ g
  let unit := adicUpperStarUnitIso ℓ g
  let ψ := (adicUpperStarIhomIso ℓ g M).app P
  let δ := (adicUpperStarIhomIso ℓ g M).app (AdicSheaf.unit ℓ Y) ≪≫
    (Mod.ihom (pull.obj M)).mapIso unit
  let c := (adicUpperStarTensorLeftIso ℓ g ((Mod.ihom M).obj (AdicSheaf.unit ℓ Y))).app P
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} ℓ]) (adicUpperStarRingHom ℓ g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair pull)
  have square : c.inv ≫ pull.map (Mod.tensorDualToIhom M P) ≫ ψ.hom =
      (Mod.tensorLeftMap δ.hom).app _ ≫ Mod.tensorDualToIhom (pull.obj M) (pull.obj P) := by
    apply Mod.tensorLeftCompMapModComapIso_inv_app_map_tensorDualToIhom (adicUpperStarRingHom ℓ g)
      (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _)
      M P ψ.hom (adicUpperStarIhomIso_evaluation g M P) δ.hom unit.hom.hom
    · let adj := upperStarLowerStarAdjunction (WeilCoefficients.{u} ℓ) g
      exact IsIso.hom_inv_id ((adj.homEquiv _ _).symm (adicConstantSheafToLowerStar ℓ g))
    · dsimp only [δ, Iso.trans_hom, Functor.mapIso_hom]
      erw [Mod.comp_hom', comp_whiskerRight_assoc]
      erw [Mod.evaluation_naturality (pull.obj M) unit.hom]
      exact (reassoc_of% (adicUpperStarIhomIso_evaluation g M (AdicSheaf.unit ℓ Y))) _
  have hδ : IsIso ((Mod.tensorLeftMap δ.hom).app (pull.obj P)) :=
    inferInstanceAs (IsIso ((Mod.tensorLeftMapIso δ).app (pull.obj P)).hom)
  have : IsIso (c.inv ≫ pull.map (Mod.tensorDualToIhom M P) ≫ ψ.hom) := by
    rw [square]
    exact IsIso.comp_isIso' hδ h
  have hc : IsIso (pull.map (Mod.tensorDualToIhom M P) ≫ ψ.hom) :=
    IsIso.of_isIso_comp_left c.inv (pull.map (Mod.tensorDualToIhom M P) ≫ ψ.hom)
  exact IsIso.of_isIso_comp_right (pull.map (Mod.tensorDualToIhom M P)) ψ.hom

end WeilII
