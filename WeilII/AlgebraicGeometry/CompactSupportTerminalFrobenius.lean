module

public import WeilII.AlgebraicGeometry.WeilLisseExternalProductCondensed

/-! # Frobenius on a compact-support image along a map to the geometric point -/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.CompactSupportClasses

attribute [local instance] instOverLeftSchemeSpecOf_weilII
  instIsSeparatedOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instQuasiCompactOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII
  instLocallyOfFiniteTypeOverSchemeLeftSpecOfInferInstanceOverClassOfHom_weilII

set_option backward.isDefEq.respectTransparency.types false
set_option maxSynthPendingDepth 12

universe u
variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
local notation "Ω" => AlgebraicClosure k
private instance : Fact (ringChar Ω).Prime := ⟨Algebra.ringChar_eq k Ω ▸ CharP.prime_ringChar k⟩
private instance : Fact (ringChar Ω ≠ ℓ) := ⟨Algebra.ringChar_eq k Ω ▸ (Fact.out : ringChar k ≠ ℓ)⟩

/-- Frobenius gives a cartesian square for every map to the terminal geometric point. -/
public theorem isPullback_frobenius_terminalMap {Z : Over (Spec (.of k))}
    (t : geometricFiberOver Z ⟶ point Ω) :
    IsPullback Z.hom.geometricGaloisFrobenius.asIso.hom t.left t.left
      (specGeometricFrobenius k).asIso.hom := by
  rw [toPoint_ext t (toPoint _), toPoint_left]
  exact Z.hom.isPullback_geometricGaloisFrobenius

/-- The image Weil structure along a chosen map to the terminal geometric point.
Shriek base change followed by the shriek image of the carrier structure gives the isomorphism. -/
@[expose] public noncomputable def imageFrobeniusAt
    {Z : Over (Spec (.of k))} [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (N : WeilSheaf k ℓ Z.left) (t : geometricFiberOver Z ⟶ point Ω) :=
  (purityFieldLowerShriekBaseChange ℓ t t (isPullback_frobenius_terminalMap t)).app (carrier.obj N) ≪≫
    (boundedConstructibleLowerShriek ℓ t).mapIso (carrierFrobenius N)

/-- Changing the terminal map transports both sides of the image Weil structure. -/
public theorem imageFrobeniusAt_transport
    {Z : Over (Spec (.of k))} [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (N : WeilSheaf k ℓ Z.left) (a b : geometricFiberOver Z ⟶ point Ω) (q : a = b) :
    let img := fun t : geometricFiberOver Z ⟶ point Ω ↦
      (boundedConstructibleLowerShriek ℓ t).obj (carrier.obj N)
    let G := boundedConstructibleUpperStarOfMap ℓ (X := point Ω) (Y := point Ω)
      (specGeometricFrobenius k).asIso.hom
    let c := eqToHom (congrArg img q)
    G.map c ≫ (imageFrobeniusAt N b).hom = (imageFrobeniusAt N a).hom ≫ c := by
  subst b
  intro img G c
  change G.map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
  rw [G.map_id, Category.id_comp, Category.comp_id]

/-- Inclusion of the bounded image structure for the canonical terminal map gives
the ambient image Weil structure used for compact-support classes. -/
public theorem imageFrobenius_eq_mapIso_at
    {Z : Over (Spec (.of k))} [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (N : WeilSheaf k ℓ Z.left) :
    imageFrobenius N = (boundedConstructible _).ι.mapIso
      (imageFrobeniusAt N (toPoint (geometricFiberOver Z))) := rfl

end WeilII.CompactSupportClasses
