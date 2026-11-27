module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedProper
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
public import WeilII.AlgebraicGeometry.CompactifiedExceptionalProjection
public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange

import Mathlib.Util.TermReduce
import WeilConjectures.Tactic.TransportModProofs
import WeilConjectures.WeilSheaf.SmoothPurityPointOpenComparison
import WeilII.AlgebraicGeometry.CompactifiedProjectionFactorization
import WeilII.AlgebraicGeometry.OpenExchangeUnitAdjunction
import WeilII.AlgebraicGeometry.UnderlyingSchemePullbackComparison
import WeilII.AlgebraicGeometry.UnderlyingSchemePullbackPaste

/-! # The exceptional projection on a pair of cartesian compactifications -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilII

universe u

/-- The raw compactified projection maps intertwine the specified exchange for the two
compactifications. Both horizontal maps are underlying scheme isomorphisms.

Proof. Apply the open–proper adjunction criterion (WeilII.openProperProjectionBaseChange)
to the two rows. Use the factorization in ProjectionFormulaOpenImmersion,
`homMk_exceptionalProjectionMorphismOfCompactification_eq`, on the two rows.
The first map is the projection of the proper adjunction. Its base-change square follows
by transposing along the primed adjunction. The counit identity for restricted proper
base change identifies the component on the first tensor factor, and the mixed tensor
identity for the bounded pullback square identifies the tensor constraints. For the
second map apply the unit identity for open extension to its forward projection comparison.
After transposition its two components are the pulled-back unit and the pullback
composition comparison on the coefficient. The same mixed tensor identity identifies
the two transposes. Inverting the open projection comparisons gives the required direction.
Paste these squares by naturality of the proper projection in its input and of the
open projection in the coefficient. The resulting exchange is
`purityFieldCompactificationExchange_eq_paste`. On the second factor the triangle
comparisons for the two compactifications cancel by pasting the pullback squares.
The bounded comparison identifies with the restricted ambient comparison by
WeilII.underlyingSchemePullbackComparison. Forget to the derived category, use `pullbackSquareComparison_paste_horizontal`, and
identify the two factored maps with the original maps using the compactification
equations. This gives the displayed identity on raw components. -/
public theorem compactifiedProjection_baseChange
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
    [Fact (ringChar Ω ≠ ℓ)] {U V U' V' : Over (Spec (.of Ω))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (f : U ⟶ V) (f' : U' ⟶ V') (tU : U'.left ≅ U.left) (tV : V'.left ≅ V.left)
    (sq : CommSq tU.hom f'.left f.left tV.hom)
    (c : Compactification f.left) (c' : Compactification f'.left)
    (tz : c'.Z ≅ c.Z)
    (hi : IsPullback tU.hom c'.i c.i tz.hom)
    (hg : IsPullback tz.hom c'.g c.g tV.hom) :
    ProjectionBaseChange.PFBaseChange
      (boundedConstructibleUpperStarOfMap ℓ (X := V) (Y := V') tV.hom)
      (boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom)
      (purityFieldCompactificationExchange ℓ f f' c c' hi.flip hg).hom
      (boundedConstructibleUpperStarOfMapSquareIso ℓ f f' sq.w).symm
      (compactifiedExceptionalProjection ℓ f c) (compactifiedExceptionalProjection ℓ f' c') := by
  let O := purityFieldOpenRestrictedExchange ℓ f f' c c' hi.flip
  let T := purityFieldProperRestrictedExchange ℓ f f' c c' hg
  -- Use the full-subcategory monoidal structures occurring in the bounded tensor identities.
  refine @openProperProjectionBaseChange_of_components _ _ _ _ _ _ _ _ _ _ _ _
    (delta% delta% monoidalCategory_boundedConstructible (ℓ := ℓ) U)
    (delta% delta% monoidalCategory_boundedConstructible (ℓ := ℓ) c.overObj)
    (delta% delta% monoidalCategory_boundedConstructible (ℓ := ℓ) V)
    (delta% delta% monoidalCategory_boundedConstructible (ℓ := ℓ) U')
    (delta% delta% monoidalCategory_boundedConstructible (ℓ := ℓ) c'.overObj)
    (delta% delta% monoidalCategory_boundedConstructible (ℓ := ℓ) V')
    (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.overI) _
    (boundedConstructibleLowerStar ℓ c.overG)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.overG) _
    (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ c'.overI)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c'.overI) _
    (boundedConstructibleLowerStar ℓ c'.overG)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c'.overG) _
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ c.overG)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ c'.overI)
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ c'.overG)
    _ _
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f')
    (boundedConstructibleUpperStarOfMap ℓ (X := V) (Y := V') tV.hom) _
    (boundedConstructibleUpperStarOfMap ℓ (X := c.overObj) (Y := c'.overObj) tz.hom)
    (monoidal_boundedConstructibleUpperStarOfMap ℓ (X := c.overObj) (Y := c'.overObj) tz.hom)
    (boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom)
    (monoidal_boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom)
    O T (purityFieldCompactificationExchange ℓ f f' c c' hi.flip hg)
    (boundedConstructibleUpperStarOfMapSquareIso ℓ c.overI c'.overI hi.w).symm
    (boundedConstructibleUpperStarOfMapSquareIso ℓ c.overG c'.overG hg.w).symm
    (boundedConstructibleUpperStarOfMapSquareIso ℓ f f' sq.w).symm
    (compactifiedExceptionalProjection ℓ f c)
    (compactifiedExceptionalProjection ℓ f' c')
    (boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ c.overI_overG)
    (boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ c'.overI_overG)
    ?_ ?_ ?_ ?_ ?_
    (boundedConstructiblePullbackComparisonOfMap ℓ (f := c.overI) (f' := c'.overI) hi.toCommSq)
    (boundedConstructiblePullbackComparisonOfMap ℓ (f := c.overG) (f' := c'.overG) hg.toCommSq)
    (underlyingSchemePullbackComparison ℓ c.overI c'.overI hi.toCommSq)
    (underlyingSchemePullbackComparison ℓ c.overG c'.overG hg.toCommSq)
    (boundedConstructibleBaseChangeOfMap ℓ (f := c.overG) (f' := c'.overG) hg.toCommSq)
    (purityFieldProperRestrictedExchange_hom ℓ f f' c c' hg)
    (by
      transport_mod_proofs map_boundedConstructibleBaseChangeOfMap_app_comp_counit ℓ
        (f := c.overG) (f' := c'.overG) hg.toCommSq)
    (by
      transport_mod_proofs map_μ_comp_boundedConstructiblePullbackComparisonOfMap_app ℓ
        (f := c.overI) (f' := c'.overI) hi.toCommSq)
    (by
      transport_mod_proofs map_μ_comp_boundedConstructiblePullbackComparisonOfMap_app ℓ
        (f := c.overG) (f' := c'.overG) hg.toCommSq)
  · exact isOpenProperProjection_compactified ℓ f c
  · exact isOpenProperProjection_compactified ℓ f' c'
  · exact purityFieldCompactificationExchange_eq_paste ℓ f f' c c' hi.flip hg
  · have h := underlyingSchemePullbackComparison_paste ℓ
      (X := U) (Y := V) (X' := U') (Y' := V') (Z := c.overObj) (Z' := c'.overObj)
      (i := c.overI) (g := c.overG) (i' := c'.overI) (g' := c'.overG)
      sq hi.toCommSq hg.toCommSq c.overI_overG c'.overI_overG
    dsimp +instances only [Compactification.overObj_left, Compactification.overI_left,
      Compactification.overG_left] at h ⊢
    transport_mod_proofs h
  · dsimp only [O]
    rw [purityFieldOpenRestrictedExchange_eq_pointOpenExchange]
    have h := isOpenExchangeUnit_underSchemeIsomorphisms ℓ c.overI c'.overI tU tz hi.toCommSq
    dsimp +instances only [Compactification.overObj_left, Compactification.overI_left] at h ⊢
    transport_mod_proofs h

end WeilII
