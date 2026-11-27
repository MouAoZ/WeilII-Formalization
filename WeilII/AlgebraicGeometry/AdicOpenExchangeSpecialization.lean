module

public import WeilII.AlgebraicGeometry.AdicOpenExtensionDirectImageExchange
import WeilII.CategoryTheory.MateEssentialImage
import Mathlib.CategoryTheory.Adjunction.Triple

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory

universe u

/-- Specializing the open-extension exchange of Katz A.2–A.3, pp. 219–220. Suppose
the universal exchange is invertible at `L` and that ordinary direct image commutes
with the indicated base change on the extension of `L` by zero. Then the fibre
exchange is invertible on the restriction of `L`.

Indeed, the first isomorphism exhibits the universal direct image as an extension by
zero. Pullback commutes with open extension on both sides, and the assumed base-change
isomorphism therefore exhibits the fibre direct image as an extension by zero as well.
Both open extensions are fully faithful, so the adjunction mate is invertible there. -/
public theorem isIso_adicOpenExchange_of_baseChange
    (ℓ : ℕ) [Fact ℓ.Prime] {X Y X' Y' : Scheme.{u}}
    {F : X ⟶ Y} {f : X' ⟶ Y'} {x : X' ⟶ X} {y : Y' ⟶ Y} (q : CommSq x f F y)
    (B : Y.Opens) (B' : Y'.Opens) {b : B'.toScheme ⟶ B.toScheme}
    (qb : IsPullback b B'.ι B.ι y)
    {a : (f ⁻¹ᵁ B').toScheme ⟶ (F ⁻¹ᵁ B).toScheme}
    (qa : IsPullback a (f ⁻¹ᵁ B').ι (F ⁻¹ᵁ B).ι x)
    (L : DerivedCategory (AdicSheaf ℓ (F ⁻¹ᵁ B).toScheme))
    (hL : IsIso ((adicOpenExtensionDirectImageExchange ℓ F B).app L))
    (hF : IsIso ((adicDerivedBaseChange ℓ q).app
      ((adicOpenImmersionLowerShriek ℓ (F ⁻¹ᵁ B).ι).mapDerivedCategory.obj L))) :
    IsIso ((adicOpenExtensionDirectImageExchange ℓ f B').app
      ((adicUpperStar ℓ a).mapDerivedCategory.obj L)) := by
  let ff {T Z : Scheme.{u}} (j : T ⟶ Z) [IsOpenImmersion j] :
      (adicOpenImmersionLowerShriek ℓ j).mapDerivedCategory.FullyFaithful := by
    have hu := (Adjunction.Triple.isIso_unit_iff_isIso_counit
      ⟨adicDerivedOpenExtensionAdjunction ℓ j, adicDerivedUpperStarLowerStarAdjunction ℓ j⟩).2
      (isIso_adicDerivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion j)
    exact (adicDerivedOpenExtensionAdjunction ℓ j).fullyFaithfulLOfIsIsoUnit
  let sq := isPullback_morphismRestrict f B'
  have := isIso_adicOpenExtensionPullbackMap ℓ sq
  apply isIso_mate_app_of_essImage (adicDerivedUpperStarLowerStarAdjunction ℓ (f ∣_ B'))
    (adicDerivedUpperStarLowerStarAdjunction ℓ f) (ff B'.ι) (ff (f ⁻¹ᵁ B').ι)
    (asIso (adicOpenExtensionPullbackMap ℓ sq.toCommSq)).symm
  have := isIso_adicOpenExtensionPullbackMap ℓ qb
  have := isIso_adicOpenExtensionPullbackMap ℓ qa
  let N := (adicLowerStar ℓ (F ∣_ B)).rightDerivedFunctor.obj L
  refine ⟨(adicUpperStar ℓ b).mapDerivedCategory.obj N, ⟨?_⟩⟩
  exact (asIso (adicOpenExtensionPullbackMap ℓ qb.toCommSq)).app N ≪≫
    (adicUpperStar ℓ y).mapDerivedCategory.mapIso
      (asIso ((adicOpenExtensionDirectImageExchange ℓ F B).app L)) ≪≫
    asIso ((adicDerivedBaseChange ℓ q).app _) ≪≫
    (adicLowerStar ℓ f).rightDerivedFunctor.mapIso
      ((asIso (adicOpenExtensionPullbackMap ℓ qa.toCommSq)).app L).symm

end WeilII
