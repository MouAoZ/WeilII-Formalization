module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedProper
public import WeilConjectures.WeilSheaf.SmoothPurityPointOpenComparison
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale

import WeilII.AlgebraicGeometry.ExceptionalProjectionCartesianCompactifications

/-!
# Exceptional projection under isomorphisms of schemes

The compact-support projection for bounded constructible condensed `ℚ̄_ℓ` complexes commutes
with pullback by isomorphisms of the underlying schemes. The exchange is the one constructed
in `WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange`. The calculation
uses the open and proper factors of the projection in
`WeilConjectures.PoincareDuality.ProjectionFormula`.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilII

universe u

/-- In a commutative square with horizontal scheme isomorphisms, pulling back the exceptional
projection and then transporting its target gives the same map as transporting its source and
then applying the exceptional projection. The two vertical maps are over `Ω`; the horizontal
isomorphisms may act nontrivially on the base field.

Proof. Take the chosen Nagata compactification `f = r ∘ j` and pull it back along the square.
The new middle scheme maps isomorphically to the old one. By
`purityFieldLowerShriekExchange_eq_paste`, the shriek exchange between these compactifications
is proper base change followed by the proper direct image of the open-extension exchange.
On either compactification the exceptional projection factors as the proper projection, the
proper direct image of the inverse open projection comparison, and the identification of
`j^* r^*` with `f^*` on the second tensor factor.

For the proper factor transpose both paths under the pulled-back pullback–direct-image
adjunction. The tensor compatibility of the pullback square splits the two factors.
The counit identity for proper base change then identifies the first factors with the
pullback of the original counit, and the second factors are identities. For the open factor
use the forward open projection comparison. Precompose with the inverse open exchange and
transpose under open extension by zero and restriction. The unit identity for the open
exchange identifies both transposes with the tensor comparison followed by the transported
unit on the first factor and the pullback comparison on the second, combined by the monoidal
constraint for restriction. Invert the open comparisons to obtain the square in the direction
used by exceptional projection.

Paste the proper and open squares, using naturality in the first argument of the proper
projection and the second argument of the open comparison. Pasting the two pullback
comparisons identifies the map on the second factor with the comparison for the original
square. Finally, the primed compactification-change isomorphisms intertwine the two endpoint
projections by `boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom_app_whiskerRight_comp`.
Naturality moves these isomorphisms past the tensor comparison and gives the stated equality
for the chosen shriek functors. -/
public theorem exceptionalProjection_underSchemeIsomorphisms
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
    [Fact (ringChar Ω ≠ ℓ)] {U V U' V' : Over (Spec (.of Ω))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (f : U ⟶ V) (f' : U' ⟶ V') (tU : U'.left ≅ U.left) (tV : V'.left ≅ V.left)
    (sq : CommSq tU.hom f'.left f.left tV.hom) :
    ProjectionBaseChange.PFBaseChange
      (boundedConstructibleUpperStarOfMap ℓ (X := V) (Y := V') tV.hom)
      (boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom)
      (purityFieldLowerShriekBaseChange ℓ f f' (IsPullback.of_horiz_isIso sq)).hom
      (boundedConstructibleUpperStarOfMapSquareIso ℓ f f' sq.w).symm
      (boundedConstructibleExceptionalProjection ℓ f)
      (boundedConstructibleExceptionalProjection ℓ f') := by
  let h := IsPullback.of_horiz_isIso sq
  let c := compactificationOverField f
  let tz := asIso (Limits.pullback.fst c.g tV.hom)
  exact exceptionalProjection_cartesianCompactifications ℓ f f' tU tV sq c (c.ofIsPullback h)
    tz (c.isPullback_i_ofIsPullback h) (c.isPullback_g_ofIsPullback h).flip

end WeilII
