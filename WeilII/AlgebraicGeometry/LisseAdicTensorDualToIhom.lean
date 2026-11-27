module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorDualToIhomMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseBidual
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom

/-! # Tensor evaluation for a lisse adic sheaf

The finite-free calculation is `Mod.isIso_tensorDualToIhom_of_iso_biproduct`. We descend
it along the pro-étale covers used in `SixFunctors/ProEtale/Adic/LisseBidual.lean`. -/

public section

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory MonoidalCategory Limits
open Functor.LaxMonoidal

namespace WeilII

universe u

attribute [local instance] Sheaf.symmetricCategory
attribute [local instance 25000] SymmetricCategory.toBraidedCategory
set_option backward.isDefEq.respectTransparency.types false
local instance {ℓ : ℕ} [Fact ℓ.Prime] (X : Scheme.{u}) : IsCommMonObj (adicConstantSheaf ℓ X) :=
  adicConstantSheaf.isCommMonObj X

/-- Tensoring with the dual of a lisse adic sheaf computes internal Hom out of it.
Restrict to a pro-étale cover trivializing the first sheaf. The relative tensor and
internal Hom comparison maps preserve evaluations, so the restricted map agrees with
finite-free tensor evaluation up to isomorphism. The cover detects isomorphisms.
See `CategoryTheory/Monoidal/Mod/TensorDualToIhomMap.lean` and `Adic/LisseBidual.lean`. -/
theorem isIso_lisseAdicTensorDualToIhom {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}}
    (M B : AdicSheaf ℓ X) (hM : IsAdicLisseSheaf M) : IsIso (Mod.tensorDualToIhom M B) := by
  obtain ⟨R, hR, h⟩ := hM
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : WeaklyEtale (f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  refine isIso_of_isIso_adicUpperStar ℓ f hR _ fun i ↦ ?_
  obtain ⟨n, ⟨trivialization⟩⟩ := h (f i) (.mk i)
  let g := f i
  let _ : (g)_*[WeilCoefficients.{u} ℓ].LaxBraided := laxBraided_lowerStar _ g
  let pull := adicUpperStar ℓ g
  let unit := adicUpperStarUnitIso ℓ g
  let ψ := (adicUpperStarIhomIso ℓ g M).app B
  let δ := (adicUpperStarIhomIso ℓ g M).app (AdicSheaf.unit ℓ X) ≪≫
    (Mod.ihom (pull.obj M)).mapIso unit
  let c := (adicUpperStarTensorLeftIso ℓ g ((Mod.ihom M).obj (AdicSheaf.unit ℓ X))).app B
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} ℓ]) (adicUpperStarRingHom ℓ g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair pull)
  have square : c.inv ≫ pull.map (Mod.tensorDualToIhom M B) ≫ ψ.hom =
      (Mod.tensorLeftMap δ.hom).app _ ≫ Mod.tensorDualToIhom (pull.obj M) (pull.obj B) := by
    apply Mod.tensorLeftCompMapModComapIso_inv_app_map_tensorDualToIhom (adicUpperStarRingHom ℓ g)
      (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _)
      M B ψ.hom (adicUpperStarIhomIso_evaluation g M B) δ.hom unit.hom.hom
    · let adj := upperStarLowerStarAdjunction (WeilCoefficients.{u} ℓ) g
      exact IsIso.hom_inv_id ((adj.homEquiv _ _).symm (adicConstantSheafToLowerStar ℓ g))
    · dsimp only [δ, Iso.trans_hom, Functor.mapIso_hom]
      erw [Mod.comp_hom', comp_whiskerRight_assoc]
      erw [Mod.evaluation_naturality (pull.obj M) unit.hom]
      exact (reassoc_of% (adicUpperStarIhomIso_evaluation g M (AdicSheaf.unit ℓ X))) _
  have heval : IsIso (Mod.tensorDualToIhom (pull.obj M) (pull.obj B)) :=
    Mod.isIso_tensorDualToIhom_of_iso_biproduct (pull.obj B) trivialization
  have hδ : IsIso ((Mod.tensorLeftMap δ.hom).app (pull.obj B)) :=
    inferInstanceAs (IsIso ((Mod.tensorLeftMapIso δ).app (pull.obj B)).hom)
  have : IsIso (c.inv ≫ pull.map (Mod.tensorDualToIhom M B) ≫ ψ.hom) := by
    rw [square]
    exact IsIso.comp_isIso' hδ heval
  have hc : IsIso (pull.map (Mod.tensorDualToIhom M B) ≫ ψ.hom) :=
    IsIso.of_isIso_comp_left c.inv (pull.map (Mod.tensorDualToIhom M B) ≫ ψ.hom)
  exact IsIso.of_isIso_comp_right (pull.map (Mod.tensorDualToIhom M B)) ψ.hom

end WeilII
