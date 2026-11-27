module

public import WeilII.AlgebraicGeometry.AdicOpenExtensionPullback
public import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory

universe u

/-- Membership in the essential image of extension by zero is local on the target.
In Katz A.2, p. 219, the charts may already have been identified with products.
Full faithfulness identifies the image by invertibility of the open counit.
On a chart the mate counit equation identifies its pullback with the local counit
up to the open base-change isomorphism and the composition isomorphism for pullbacks. -/
public theorem adicDerivedOpenExtension_essImage_of_locally
    (ℓ : ℕ) [Fact ℓ.Prime] {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (M : DerivedCategory (AdicSheaf ℓ Y))
    (h : ∀ z : Y, ∃ (T : Scheme.{u}) (y : T ⟶ Y), IsOpenImmersion y ∧ z ∈ Set.range y ∧
      ∃ (V : Scheme.{u}) (i : V ⟶ T) (_ : IsOpenImmersion i) (a : V ⟶ U), IsPullback a i j y ∧
        (adicOpenImmersionLowerShriek ℓ i).mapDerivedCategory.essImage
          ((adicUpperStar ℓ y).mapDerivedCategory.obj M)) :
    (adicOpenImmersionLowerShriek ℓ j).mapDerivedCategory.essImage M := by
  classical
  let adj := adicDerivedOpenExtensionAdjunction ℓ j
  suffices IsIso (adj.counit.app M) from adj.mem_essImage_of_counit_isIso M
  choose T y hy cover V i hi a sq localImage using h
  let c : Scheme.OpenCover Y :=
    { I₀ := Y
      X := T
      f := y
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun z ↦ ⟨z, cover z⟩, hy⟩ }
  apply isIso_of_isIso_mapDerivedCategory_adicUpperStar ℓ y
    (Scheme.zariskiPrecoverage_le_proetalePrecoverage _ c.mem₀)
  intro z
  let adj' := adicDerivedOpenExtensionAdjunction ℓ (i z)
  have hunit : IsIso adj'.unit := (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨adj', adicDerivedUpperStarLowerStarAdjunction ℓ (i z)⟩).2
    (isIso_adicDerivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion _)
  have := adj'.fullyFaithfulLOfIsIsoUnit.full
  have := adj'.fullyFaithfulLOfIsIsoUnit.faithful
  have hε := adj'.isIso_counit_app_iff_mem_essImage.mpr (localImage z)
  let s := (sq z).toCommSq
  let γ := (adicDerivedPullSquare ℓ s.flip).hom
  have he := mateEquiv_counit_symm adj adj' (TwoSquare.mk _ _ _ _ γ) M
  change (adicOpenImmersionLowerShriek ℓ (i z)).mapDerivedCategory.map (γ.app M) ≫
      adj'.counit.app _ = (adicOpenExtensionPullbackMap ℓ s).app _ ≫
      (adicUpperStar ℓ (y z)).mapDerivedCategory.map (adj.counit.app M) at he
  have := isIso_adicOpenExtensionPullbackMap ℓ (sq z)
  have : IsIso ((adicOpenExtensionPullbackMap ℓ s).app _ ≫
      (adicUpperStar ℓ (y z)).mapDerivedCategory.map (adj.counit.app M)) := by
    rw [← he]
    dsimp only [γ]
    infer_instance
  exact IsIso.of_isIso_comp_left ((adicOpenExtensionPullbackMap ℓ s).app _) _

end WeilII
