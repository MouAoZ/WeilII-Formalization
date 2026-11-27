module

public import WeilConjectures.PoincareDuality.CompactSupportKunneth
public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeGeometricFiber
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale

import WeilII.AlgebraicGeometry.CompactSupportKunnethNaturality
import WeilII.AlgebraicGeometry.KunnethSchemeAutomorphisms
meta import WeilII.Tactic.StructuralDefEq

/-!
# Frobenius and the compact-support Künneth morphism

SGA 4, XVII, Lemma 5.4.3.2 (p. 369), gives the base-change square for the compact-support
external product with torsion coefficients. We state its geometric Galois Frobenius case for
the condensed `ℚ̄_ℓ` Künneth isomorphism used in Zhang's deduction of Theorem 1.1 on p. 2.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Geometric Galois Frobenius commutes with the inverse compact-support Künneth isomorphism,
and this same morphism is natural in both coefficient complexes.

Proof (SGA 4, XVII, Lemma 5.4.3.2 for torsion coefficients, applied here through the
condensed construction in `PoincareDuality/CompactSupportKunneth.lean`). Base change the
given product to the algebraic closure. The Galois automorphisms commute with both projections
and with the structure maps, giving cartesian squares since their horizontal sides are
isomorphisms. On the source, split the Frobenius pullback of the tensor product and apply the
two shriek base-change components. On the target, apply shriek base change for the composite,
then split the pullback of the external tensor product and commute pullback past each projection.

Expand the inverse Künneth map. Apply the projection morphism for the first structure map,
then tensor the identity with shriek base change for the product square. Inside the first
shriek functor, braid the factors, apply the projection morphism for the first projection,
and undo the inner braiding. Finally invert the shriek composition comparison. The base-change
square for each projection morphism moves Frobenius past that morphism. The shriek base-change
cube moves it past the product square, compatibility of monoidal pullback with braiding moves
it past the two inverse braidings, and compatibility of shriek composition with isomorphism
base change moves it past the last comparison. Pasting gives the first equality. For the
second, move the two coefficient maps through the same factors by naturality of the projection
morphisms, base change, braiding and shriek composition, in that order. -/
public theorem geometricCompactSupportKunnethFrobeniusSquare
    {k : Type u} [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y P : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (p : P ⟶ X) (s : P ⟶ Y) (product : IsPullback s.left p.left Y.hom X.hom)
    (K : Dᵇc(X.hom.geometricFiber)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.hom.geometricFiber)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    letI : Fact (ringChar (AlgebraicClosure k)).Prime :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
    letI : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
      ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ)
      (geometricFiberOver P)).toMonoidalCategoryStruct
    letI := (monoidalCategory_boundedConstructible (ℓ := ℓ)
      (point (AlgebraicClosure k))).toMonoidalCategoryStruct
    let p' := geometricFiberOverMap p
    let s' := geometricFiberOverMap s
    let f : geometricFiberOver X ⟶ point (AlgebraicClosure k) :=
      Over.homMk X.hom.geometricFiberToAlgebraicClosure (Category.comp_id _)
    let g : geometricFiberOver Y ⟶ point (AlgebraicClosure k) :=
      Over.homMk Y.hom.geometricFiberToAlgebraicClosure (Category.comp_id _)
    let h := p' ≫ f
    have sq : IsPullback s' p' g f := by
      apply IsPullback.of_map_of_faithful (Over.forget _)
      change IsPullback (Scheme.Hom.geometricFiberMap s.left (Over.w s))
        (Scheme.Hom.geometricFiberMap p.left (Over.w p))
        Y.hom.geometricFiberToAlgebraicClosure X.hom.geometricFiberToAlgebraicClosure
      have right : IsPullback Y.hom.geometricFiberProj Y.hom.geometricFiberToAlgebraicClosure
          Y.hom (Scheme.specAlgebraicClosure k).hom := IsPullback.of_hasPullback _ _
      apply IsPullback.of_right _ _ right
      · erw [Scheme.Hom.geometricFiberMap_comp_geometricFiberProj, ← X.hom.geometricFiber_condition]
        exact (isPullback_geometricFiberOverMap p).paste_horiz product
      · exact (Over.w s').trans (Over.w p').symm
    let σ := (specGeometricFrobenius k).asIso.hom
    let F := boundedConstructibleUpperStarOfMap ℓ
      (X := point (AlgebraicClosure k)) (Y := point (AlgebraicClosure k)) σ
    let Fp := boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver P)
      (Y := geometricFiberOver P) P.hom.geometricGaloisFrobenius.asIso.hom
    let Ef := purityFieldLowerShriekBaseChange ℓ f f X.hom.isPullback_geometricGaloisFrobenius
    let Eg := purityFieldLowerShriekBaseChange ℓ g g Y.hom.isPullback_geometricGaloisFrobenius
    have sqh : IsPullback P.hom.geometricGaloisFrobenius.asIso.hom h.left h.left σ := by
      rw [show h.left = P.hom.geometricFiberToAlgebraicClosure from Over.w p']
      exact P.hom.isPullback_geometricGaloisFrobenius
    let Eh := purityFieldLowerShriekBaseChange ℓ h h sqh
    let Dp := boundedConstructibleUpperStarOfMapSquareIso ℓ p' p'
      (Scheme.Hom.commSq_geometricGaloisFrobenius p.left (Over.w p)).w
    let Ds := boundedConstructibleUpperStarOfMapSquareIso ℓ s' s'
      (Scheme.Hom.commSq_geometricGaloisFrobenius s.left (Over.w s)).w
    let pStar := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p'
    let sStar := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ s'
    let τtgt := Eh.hom.app (pStar.obj K ⊗ sStar.obj L) ≫
      (boundedConstructibleLowerShriek ℓ h).map (Functor.OplaxMonoidal.δ Fp _ _ ≫
        (Dp.hom.app K ⊗ₘ Ds.hom.app L))
    let τsrc := Functor.OplaxMonoidal.δ F ((boundedConstructibleLowerShriek ℓ f).obj K)
      ((boundedConstructibleLowerShriek ℓ g).obj L) ≫ (Ef.hom.app K ⊗ₘ Eg.hom.app L)
    let Fx := boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver X)
      (Y := geometricFiberOver X) X.hom.geometricGaloisFrobenius.asIso.hom
    let Fy := boundedConstructibleUpperStarOfMap ℓ (X := geometricFiberOver Y)
      (Y := geometricFiberOver Y) Y.hom.geometricGaloisFrobenius.asIso.hom
    F.map (compactSupportKunnethIso ℓ sq K L).inv ≫ τtgt =
        τsrc ≫ (compactSupportKunnethIso ℓ sq (Fx.obj K) (Fy.obj L)).inv ∧
      ∀ {K' L'} (x : K ⟶ K') (y : L ⟶ L'),
        (compactSupportKunnethIso ℓ sq K L).inv ≫
            (boundedConstructibleLowerShriek ℓ h).map (pStar.map x ⊗ₘ sStar.map y) =
          ((boundedConstructibleLowerShriek ℓ f).map x ⊗ₘ
            (boundedConstructibleLowerShriek ℓ g).map y) ≫
            (compactSupportKunnethIso ℓ sq K' L').inv := by
  intro p' s' f g h sq σ F Fp Ef Eg sqh Eh Dp Ds pStar sStar τtgt τsrc Fx Fy
  have : Fact (ringChar (AlgebraicClosure k)).Prime :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ CharP.prime_ringChar k⟩
  have : Fact (ringChar (AlgebraicClosure k) ≠ ℓ) :=
    ⟨Algebra.ringChar_eq k (AlgebraicClosure k) ▸ (Fact.out : ringChar k ≠ ℓ)⟩
  constructor
  · have square := compactSupportKunneth_underSchemeAutomorphisms ℓ sq
      P.hom.geometricGaloisFrobenius.asIso X.hom.geometricGaloisFrobenius.asIso
      Y.hom.geometricGaloisFrobenius.asIso (specGeometricFrobenius k).asIso
      (Scheme.Hom.commSq_geometricGaloisFrobenius p.left (Over.w p))
      (Scheme.Hom.commSq_geometricGaloisFrobenius s.left (Over.w s))
      X.hom.isPullback_geometricGaloisFrobenius Y.hom.isPullback_geometricGaloisFrobenius
      sqh K L
    structural_exact square.1
  · intro K' L' x y
    exact compactSupportKunneth_inv_naturality ℓ sq x y

end WeilII
