module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedProper
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange
import WeilII.AlgebraicGeometry.CompactifiedProjectionBaseChange
import WeilII.CategoryTheory.TransportProjectionBaseChange
import WeilConjectures.Tactic.ExactByKernel
import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion

/-! # The projection square on two cartesian compactifications -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilII

universe u

/-- Given cartesian open and proper squares between two compactifications, the transported
exceptional projections commute with their specified cross-field shriek exchange. Start
with the projection square on these two compactifications. The primed comparison from
the chosen source compactification to the specified source intertwines their projections,
as does the primed comparison from the specified target to the chosen target. Transport
the square along these isomorphisms. Their whiskerings with the two horizontal pullbacks
give exactly the chosen-shriek exchange. -/
public theorem exceptionalProjection_cartesianCompactifications
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
      (purityFieldLowerShriekExchange ℓ f f' c c' hi.flip hg).hom
      (boundedConstructibleUpperStarOfMapSquareIso ℓ f f' sq.w).symm
      (boundedConstructibleExceptionalProjection ℓ f)
      (boundedConstructibleExceptionalProjection ℓ f') := by
  refine transportProjectionBaseChange
    (boundedConstructibleUpperStarOfMap ℓ (X := V) (Y := V') tV.hom)
    (boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (compactificationOverField f) c)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c' (compactificationOverField f'))
    (purityFieldCompactificationExchange ℓ f f' c c' hi.flip hg)
    (boundedConstructibleUpperStarOfMapSquareIso ℓ f f' sq.w).symm
    (boundedConstructibleExceptionalProjection ℓ f) (boundedConstructibleExceptionalProjection ℓ f')
    (compactifiedExceptionalProjection ℓ f c) (compactifiedExceptionalProjection ℓ f' c')
    ?_ ?_ ?_
  · exact_by_kernel boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom_app_whiskerRight_comp
      ℓ (compactificationOverField f) c
  · exact_by_kernel boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_hom_app_whiskerRight_comp
      ℓ c' (compactificationOverField f')
  · exact compactifiedProjection_baseChange ℓ f f' tU tV sq c c' tz hi hg

end WeilII
