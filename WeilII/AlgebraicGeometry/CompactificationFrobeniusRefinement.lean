module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeGeometricFiber
public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange
public import WeilConjectures.WeilSheaf.SmoothPurityAmbientOpenExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence
import WeilII.AlgebraicGeometry.SemilinearCompactificationExchange
meta import WeilII.AlgebraicGeometry.CompactificationComponentTransport

/-! # Geometric Frobenius and change of compactification

Zhang uses Frobenius-equivariant compact support on p. 2 in the deduction of Theorem 1.1
from Proposition 1.5. This compatibility compares the two compactifications in the ambient
condensed derived category. It uses the open and proper exchange of `CondensedModelBaseChange`
and the bounded constructible compactification comparisons of `BaseChangeIndependence`.
-/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

/-- Geometric Frobenius base change intertwines the specified compactification comparisons.
The cartesian open and proper squares specify representatives of the two pullbacks. One can
take each `dσ` to be `d.ofIsPullback Z.hom.isPullback_geometricGaloisFrobenius`. The first
equality uses these pullbacks. The second transports each exchange back to its original
compactification. Both are equalities of ambient morphisms.

Proof. Write `S = Spec k̄`. Postcompose the structure maps in the original row with the inverse
of geometric Frobenius on `S`. The two Frobenius maps and the projection from each pulled-back
middle scheme now respect the maps to `S`. The open and proper squares are cartesian in the
slice since they are cartesian on underlying schemes and the projections are slice morphisms.

In this slice, compute the chosen compact-support exchange using each of the two pairs of
compactifications. By `boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_baseChange`,
each computation is the exchange for that pair preceded and followed by comparisons with the
chosen compactifications. Cancel the outer comparisons and use their cocycle identity. This
gives the comparison square for the bounded constructible exchanges.

To identify its sides after inclusion, compute the original comparison and the comparison
in the reindexed row through a common proper refinement. Postcomposing structure maps carries
the same refinement to the reindexed row. Each refinement comparison inserts identity direct
image, uses the exchange for the open square, and composes the proper direct images. Their
pullback constraints are the same underlying scheme constraints. The adjunctions restrict
through the fully faithful inclusions, so their units and counits agree there as well. Hence
the two refinement calculations give the same ambient comparison. The two published versions
of compactification independence agree by the refinement comparison theorem.

For the horizontal exchange, the proper factor is the right mate of the pullback square.
Through the inclusions this is the ambient proper base change. For the open factor, the inverse
exchange is the left mate of the pullback square. The pullbacks and extension by zero here are
exact, so this mate is computed degreewise and is the inverse ambient open exchange. Composing
and using the comparison of left-derived and levelwise pullback gives precisely
`purityFieldCompactificationAmbientExchange`. The inclusion comparisons at the intermediate
objects cancel, leaving the first equality. Postcompose with the comparison from the second
pulled-back compactification to its original one and apply the cocycle identity once more.
This gives the second equality. -/
public theorem geometricCompactificationFrobeniusRefinement
    {k : Type u} [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (d₁ d₂ d₁σ d₂σ : Compactification Z.hom.geometricFiberToAlgebraicClosure)
    (π₁ : d₁σ.Z ⟶ d₁.Z) (π₂ : d₂σ.Z ⟶ d₂.Z)
    (hi₁ : IsPullback d₁σ.i Z.hom.geometricGaloisFrobenius.asIso.hom π₁ d₁.i)
    (hg₁ : IsPullback π₁ d₁σ.g d₁.g (specGeometricFrobenius k).asIso.hom)
    (hi₂ : IsPullback d₂σ.i Z.hom.geometricGaloisFrobenius.asIso.hom π₂ d₂.i)
    (hg₂ : IsPullback π₂ d₂σ.g d₂.g (specGeometricFrobenius k).asIso.hom)
    (K : Dᵇc(Z.hom.geometricFiber)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    letI : Fact (ringChar (AlgebraicClosure k)).Prime :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
    letI : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
    let f : geometricFiberOver Z ⟶ point (AlgebraicClosure k) :=
      Over.homMk Z.hom.geometricFiberToAlgebraicClosure (Category.comp_id _)
    let σK := (boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver Z)
      (Y := geometricFiberOver Z) Z.hom.geometricGaloisFrobenius.asIso.hom).obj K
    let J (d e : Compactification f.left)
        (A : Dᵇc(Z.hom.geometricFiber)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
      (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ (f := f) d).inv.app A ≫
        (boundedConstructible _).ι.map
          ((boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
            (f := f) d e).hom.app A) ≫
        (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ (f := f) e).hom.app A
    haveI : WeaklyEtale π₁ := MorphismProperty.of_isPullback hg₁.flip
      (inferInstance : WeaklyEtale (specGeometricFrobenius k).asIso.hom)
    haveI : WeaklyEtale π₂ := MorphismProperty.of_isPullback hg₂.flip
      (inferInstance : WeaklyEtale (specGeometricFrobenius k).asIso.hom)
    let b₁ := (purityFieldCompactificationAmbientExchange ℓ f f d₁ d₁σ hi₁ hg₁).hom.app K.obj
    let b₂ := (purityFieldCompactificationAmbientExchange ℓ f f d₂ d₂σ hi₂ hg₂).hom.app K.obj
    let τ₁ := b₁ ≫ J d₁σ d₁ σK
    let τ₂ := b₂ ≫ J d₂σ d₂ σK
    let σJ := L(((specGeometricFrobenius k).asIso.hom)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map
      (J d₁ d₂ K)
    (σJ ≫ b₂ = b₁ ≫ J d₁σ d₂σ σK) ∧ (σJ ≫ τ₂ = τ₁ ≫ J d₁ d₂ σK) := by
  intro f
  have : Fact (ringChar (AlgebraicClosure k)).Prime :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
  have : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
  let σ := (specGeometricFrobenius k).asIso
  have wx : Z.hom.geometricGaloisFrobenius.asIso.hom ≫ (geometricFiberOver Z).hom ≫ σ.inv =
      (geometricFiberOver Z).hom := by
    change _ ≫ Z.hom.geometricFiberToAlgebraicClosure ≫ σ.inv = _
    rw [← Category.assoc, Z.hom.geometricGaloisFrobenius_hom_comp_geometricFiberToAlgebraicClosure,
      Category.assoc, σ.hom_inv_id, Category.comp_id]
    rfl
  have wy : σ.hom ≫ (point (AlgebraicClosure k)).hom ≫ σ.inv = (point (AlgebraicClosure k)).hom := by
    change σ.hom ≫ 𝟙 _ ≫ σ.inv = 𝟙 _
    rw [Category.id_comp, σ.hom_inv_id]
  have : WeaklyEtale π₁ := MorphismProperty.of_isPullback hg₁.flip (inferInstance : WeaklyEtale σ.hom)
  have : WeaklyEtale π₂ := MorphismProperty.of_isPullback hg₂.flip (inferInstance : WeaklyEtale σ.hom)
  have h := semilinearCompactificationExchange_normalized ℓ (f := f) σ.symm
    Z.hom.geometricGaloisFrobenius.asIso.hom σ.hom wx wy Z.hom.isPullback_geometricGaloisFrobenius
    d₁ d₂ d₁σ d₂σ π₁ π₂ hi₁ hg₁ hi₂ hg₂ K
  constructor
  · transport_compactification_component h.1
  · transport_compactification_component h.2

end WeilII
