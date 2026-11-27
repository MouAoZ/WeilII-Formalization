module

public import WeilII.AlgebraicGeometry.AdicOpenExtensionPullback
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport

/-!
# Exchange of open extension by zero with derived direct image

Katz, *Affine cohomological transforms, perversity, and monodromy*, Appendix A.2–A.3,
pp. 218–220, uses the adjunction map for the restriction of a morphism to an open.
-/

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory

universe u

/-- The adjunction map of Katz A.2–A.3. Write `β : B ↪ Y`, `j : f⁻¹B ↪ X`, and
`g : f⁻¹B ⟶ B`. The component `β_! Rg_* M ⟶ Rf_* j_! M` is adjoint to the inverse
open-extension pullback comparison followed by `j_!` applied to the counit at `M`. -/
@[expose] public noncomputable def adicOpenExtensionDirectImageExchange
    (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Y.Opens) :
    (adicLowerStar ℓ (morphismRestrict f B)).rightDerivedFunctor ⋙
        (adicOpenImmersionLowerShriek ℓ B.ι).mapDerivedCategory ⟶
      (adicOpenImmersionLowerShriek ℓ (f ⁻¹ᵁ B).ι).mapDerivedCategory ⋙
        (adicLowerStar ℓ f).rightDerivedFunctor := by
  let sq := isPullback_morphismRestrict f B
  have : IsIso (adicOpenExtensionPullbackMap ℓ sq.toCommSq) :=
    isIso_adicOpenExtensionPullbackMap ℓ sq
  exact mateEquiv (adicDerivedUpperStarLowerStarAdjunction ℓ (morphismRestrict f B))
    (adicDerivedUpperStarLowerStarAdjunction ℓ f)
    (TwoSquare.mk _ _ _ _ (inv (adicOpenExtensionPullbackMap ℓ sq.toCommSq)))

end WeilII
