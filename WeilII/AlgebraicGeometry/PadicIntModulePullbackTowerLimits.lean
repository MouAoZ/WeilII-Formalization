module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperStarMapModLimits

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilII

universe u

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- Weakly étale pullback of integral modules preserves inverse limits of towers.
On underlying abelian sheaves it is restriction to the slice site. The forgetful
functors preserve limits and the forgetful functor at the source scheme reflects them. -/
public theorem padicIntModulePullback_preservesTowerLimits
    (ℓ : ℕ) [Fact ℓ.Prime] {V Z : Scheme.{u}} (p : V ⟶ Z) [WeaklyEtale p] :
    PreservesLimitsOfShape ℕᵒᵖ (padicIntModUpperStar ℓ p) := by
  let U : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (padicIntAbSheaf V ℓ) ⥤
      Sheaf (Scheme.ProEt.topology V) Ab.{u + 1} := Mod.forget (padicIntAbSheaf V ℓ)
  let UZ : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (padicIntAbSheaf Z ℓ) ⥤
      Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1} := Mod.forget (padicIntAbSheaf Z ℓ)
  have : ReflectsLimitsOfShape ℕᵒᵖ U := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape ℕᵒᵖ (padicIntModUpperStar ℓ p ⋙ U) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ (UZ ⋙ ProEtale.upperStar Ab.{u + 1} p))
  exact preservesLimitsOfShape_of_reflects_of_preserves (padicIntModUpperStar ℓ p) U

end WeilII
