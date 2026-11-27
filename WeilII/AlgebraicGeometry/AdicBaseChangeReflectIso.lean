module

public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedExchangeComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

namespace WeilII

open AlgebraicGeometry AlgebraicGeometry.ProEtale CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj

universe u

set_option backward.isDefEq.respectTransparency false in
/-- An invertible ordinary bounded constructible exchange gives an invertible native
component whenever the native input realizes a bounded constructible complex. -/
public theorem isIso_adicBaseChange_of_condensed
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback v p' p g) (M : DerivedCategory (AdicSheaf l X.left))
    (K : BoundedConstructible (condensedRingObj Λ.X X.left))
    (e : (nativeExchangeEncodingAt l Λ hΛ X.left).mapDerivedCategory.obj M ≅ K.obj)
    (hb : IsIso (CondensedRing.boundedConstructibleBaseChange l sq.toCommSq)) :
    IsIso ((adicDerivedBaseChange l ((Over.forget _).map_commSq sq.toCommSq)).app M) := by
  have hi : IsIso (CondensedRing.boundedConstructibleBaseChangeOfPreserves Λ.X l
      (CondensedRing.rationalCoefficientPushforwardPreservation l Λ (Or.inr hΛ)) sq.toCommSq) := by
    subst Λ
    rw [CondensedRing.boundedConstructibleBaseChange_def] at hb
    with_unfolding_all exact hb
  obtain ⟨a⟩ := nativeDerivedExchange_condensed_comparison l k Λ hΛ sq M K e
  have reflect {A B : DerivedCategory (AdicSheaf l Y'.left)} (f : A ⟶ B)
      (hf : IsIso ((nativeExchangeEncodingAt l Λ hΛ Y'.left).mapDerivedCategory.map f)) : IsIso f :=
    @isIso_of_reflects_iso _ _ _ _ _ _ f (nativeExchangeEncodingAt l Λ hΛ Y'.left).mapDerivedCategory
      hf inferInstance
  exact reflect _ ((@Arrow.isIso_hom_iff_isIso_hom_of_isIso _ _ _ _ a.hom a.isIso_hom).2
    (nativeUnderlyingExchangeArrow_isIso _ _ (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hi K)))

end WeilII
