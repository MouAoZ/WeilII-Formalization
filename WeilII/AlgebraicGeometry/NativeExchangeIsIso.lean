module

public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedExchangeComparison
public import WeilII.AlgebraicGeometry.CondensedStandardExchangeIsIso

/-! # Reflection of base-change isomorphisms in the native adic model -/

namespace WeilII

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

universe u

/-- In a cartesian square over the ground field, invertibility of the restricted condensed
exchange on an encoding of the input implies invertibility of the native exchange.

The native–condensed comparison identifies the encoded arrow with the image of the
restricted exchange under the inclusion. This inclusion preserves isomorphisms and the
encoding reflects them. -/
public theorem isIso_adicDerivedBaseChange_of_condensed
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj R.X] (hR : R = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback v p' p g) (M : DerivedCategory (AdicSheaf ℓ X.left))
    (K : BoundedConstructible (condensedRingObj R.X X.left))
    (e : (nativeExchangeEncodingAt ℓ R hR X.left).mapDerivedCategory.obj M ≅ K.obj)
    (h : IsInvertibleCondensedExchange R.X ℓ k sq.toCommSq
      (CondensedRing.rationalCoefficientPushforwardPreservation ℓ R (Or.inr hR)) K) :
    IsIso ((adicDerivedBaseChange ℓ ((Over.forget _).map_commSq sq.toCommSq)).app M) := by
  obtain ⟨b⟩ := nativeDerivedExchange_condensed_comparison ℓ k R hR sq M K e
  have hi := nativeUnderlyingExchangeArrow_isIso
    (boundedConstructible (condensedRingObj R.X Y'.left))
    ((CondensedRing.boundedConstructibleBaseChangeOfPreserves R.X ℓ
      (CondensedRing.rationalCoefficientPushforwardPreservation ℓ R (Or.inr hR))
      sq.toCommSq).app K) h.isIso
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _
    (nativeExchangeEncodingAt ℓ R hR Y'.left).mapDerivedCategory
    ((Arrow.isIso_hom_iff_isIso_hom_of_isIso b.hom).mpr hi) inferInstance

end WeilII
