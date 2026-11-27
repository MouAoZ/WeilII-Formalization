module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelConstructible
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationDescent
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralStratum
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing

/-! # Integral models before removing torsion

SGA 4½, *Rapport sur la formule des traces*, §§2.8–2.11. -/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- A constructible geometric adic sheaf on a noetherian scheme admits an ordinary integral
model over a finite coefficient field. Descend the condensed sheaf to one finite intermediate
field. Choose its constructible stratification and an integral model on each stratum, then apply
integral gluing. Composing the two coefficient isomorphisms gives the claim.
See SGA 4½, *Rapport*, §§2.8–2.11 and the pinned `ContinuousConstructibleIntegralSingle`. -/
public theorem exists_constructibleAdicSheaf_integralModel
    (ℓ : ℕ) [Fact ℓ.Prime] {Z : Scheme.{u}} [IsNoetherian Z]
    (F : AdicSheaf ℓ Z) (hF : IsAdicConstructibleSheaf F) :
    ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z)),
      IsConstructibleModuleObject _ N ∧
      Nonempty ((Mod.extendScalars (padicIntegersToPadicSubfield Z ℓ E) ⋙
        Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Z ℓ E)).obj N ≅
        (adicSheafEquivCondensedMod ℓ Z).functor.obj F) := by
  classical
  let A := (adicSheafEquivCondensedMod ℓ Z).functor.obj F
  obtain ⟨E, F_E, hE, ⟨eF⟩⟩ :=
    exists_constructible_finiteCoefficient_model Z ℓ A hF.isConstructibleModuleObject
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  obtain ⟨S, hS⟩ := hE
  obtain ⟨N, hN, ⟨eN⟩⟩ := CondensedRing.continuousConstructible_integral_gluing ℓ E.1 Z F_E S
    (fun i ↦ CondensedRing.continuousConstructible_integral_stratum ℓ E.1 Z
      (S.immersion i) _ (hS i))
  refine ⟨E, N, hN, ⟨?_⟩⟩
  exact (Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Z ℓ E)).mapIso eN ≪≫ eF

end WeilII
