module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueFinal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear

/-!
# Uniformizer action on an integral submodule of a rational sheaf

SGA 4½, *Rapport*, §2.8, and the constant-section identities in `PushResidueFinal`.
-/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- An integral submodule of a rational sheaf is uniformizer-torsion-free. The nonzero
uniformizer is a unit of the coefficient field, so its action through constant global
sections is invertible. The central action commutes with the submodule inclusion. -/
public theorem mono_uniformizer_of_mono_into_restrictedFieldModule
    (ℓ : ℕ) [Fact ℓ.Prime] (Z : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {π})
    (P : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (padicSubfieldRingObj Z ℓ E))
    {M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z)}
    (i : M ⟶ (Mod.comap (padicIntegersToPadicSubfield Z ℓ E)).obj P) [Mono i] :
    Mono ((padicIntegersCenter Z ℓ E.1 π).app M) := by
  let φ := CondensedRing.constRingHom (Profinite.continuousMapRingObj E)
    (Profinite.continuousMapConstRingHom.{u} E) Z
  let c := Mod.toCatCenter (padicSubfieldRingObj Z ℓ E) (φ (π : E.1))
  have hu : IsUnit (π : E.1) :=
    isUnit_iff_ne_zero.mpr (CondensedRing.coe_ne_zero_of_maximalIdeal_eq_span ℓ E.1 hπ)
  have : IsIso c.asHom := (isUnit_iff_isIso _).mp ((hu.map φ).map (Mod.toCatCenter _))
  have : IsIso ((c.app P).hom) := (Mod.forget _).map_isIso (c.app P)
  let B := (Mod.comap (padicIntegersToPadicSubfield Z ℓ E)).obj P
  have heq : ((padicIntegersCenter Z ℓ E.1 π).app B).hom = (c.app P).hom := by
    refine (regularEndSMul_padicIntegersRegularEnd_hom Z ℓ E.1 π B).trans ?_
    dsimp only [B]
    rw [Mod.globalSmul_comap, padicIntegersConstSection, Category.assoc, ← Functor.map_comp]
    exact congrArg (fun v ↦ Mod.globalSmul (Functor.LaxMonoidal.ε (upperStarFromPoint Z) ≫
      (upperStarFromPoint Z).map v) P)
      (continuousMapConstRingHom_hom_comp_padicIntegersRingObjToSubfieldRingObj ℓ E.1 π)
  have hmono : Mono ((c.app P).hom) := inferInstance
  have : Mono (((padicIntegersCenter Z ℓ E.1 π).app B).hom) :=
    (congrArg (fun z : P.X ⟶ P.X ↦ Mono z) heq).mpr hmono
  have : Mono ((padicIntegersCenter Z ℓ E.1 π).app B) := (Mod.forget _).mono_of_mono_map this
  exact mono_of_mono_fac ((padicIntegersCenter Z ℓ E.1 π).naturality i).symm

end WeilII
