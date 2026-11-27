module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilII.AlgebraicGeometry.CoefficientUnitImagePullback
import WeilII.AlgebraicGeometry.IntegralConstantLocalizationImage
import WeilII.AlgebraicGeometry.ConstructibleFromLocalModels

/-!
# Constructibility of the image in the field localization

SGA 4½, *Rapport*, §2.8, and the pullback of the unit in `LisseLatticeEmbedding`.
-/

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- The image of a constructible integral sheaf in its localization is constructible.
See SGA 4½, *Rapport*, §2.8, and `AlgebraicGeometry.ProEtale.exists_cover_iso_integralConstantModule`.
Choose a constructible stratification for the integral sheaf.
Pullback to each stratum and its local elementary-divisor cover is exact and commutes with
extension and restriction of the two pulled-back coefficient rings. It therefore identifies
the pullback of the image with the image of the local localization map. This map kills every
cyclic summand killed by a power of π and embeds each copy of the ring of integers in the
coefficient field. Its image on that cover is consequently finite free, proving finite
presentation on each stratum. -/
public theorem isConstructible_image_integralLocalizationUnit
    (ℓ : ℕ) [Fact ℓ.Prime] {Z : Scheme.{u}} [IsNoetherian Z]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (hπ : IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1) = Ideal.span {π})
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Z))
    (hN : IsConstructibleModuleObject _ N) :
    let M := image ((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield Z ℓ E)).unit.app N)
    IsConstructibleModuleObject _ M := by
  refine isConstructibleModuleObject_of_localModels (Profinite.padicIntegersRingObj ℓ E.1)
    (fun X P ↦ image ((Mod.extendRestrictAdjunction (padicIntegersToPadicSubfield X ℓ E)).unit.app P))
    (fun f P _ d ↦ nonempty_upperStar_image_coefficientUnit_iso
      (padicIntegersRingObjToContinuousMapRingObj ℓ E) f P d) ?_ N hN
  intro X _ P hP
  obtain ⟨𝒰, h𝒰⟩ := exists_cover_iso_integralConstantModule ℓ E.1 X hP π hπ
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨k, r, e, d⟩ := h𝒰 i
  refine ⟨integralConstantModule ℓ E.1 (𝒰.X i) π k r e, d, Mod.IsFree.isFinitelyPresented ?_⟩
  exact ⟨r, nonempty_image_integralConstantModule_unit_iso_finiteFree ℓ E (𝒰.X i) π hπ k r e⟩

end WeilII
