module

public import WeilConjectures.TraceFormula.BaseChangeCoherence

import WeilII.AlgebraicGeometry.CompactificationComparisonStructure
import WeilII.AlgebraicGeometry.CompactificationPastingComponent
import WeilII.AlgebraicGeometry.CompactificationComponentTransport
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Dependence of the compact-support exchange on the field structures -/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]

/-- The open/proper exchange for a compactification and its cartesian pullback has
the same underlying component after giving the four vertices other field structures.
Source: `LowerShriek/BaseChangeIndependence.lean` (open/proper formula) and
`Derived/Bounded/BoundedExchangeAmbient.lean` (proper exchange as the ambient mate).
Use the same compactification on the right and its pullback along the unchanged
underlying bottom map on the left. The proper factor in each slice is the restriction
of the ambient right mate, evaluated on the same open extension. For the open factor,
take inverses. Both inverses are left mates for the extension-by-zero/restriction
adjunction of the ambient pullback square. The restricted unit and counit have the
same components under the full inclusion, and the pullback composition constraints
restrict the ambient ones. Thus the two inverse components agree. Inverting gives the
same open exchange. Composing the proper factor with the image of the open factor
gives the asserted equality for the compactification pasting. -/
public theorem compactificationPasting_changeStructure
    {x : U' ⟶ U} {y : V' ⟶ V} {f : U ⟶ V} {f' : U' ⟶ V'} (sq : IsPullback x f' f y)
    {a : U.left ⟶ Spec (.of k)} {b : V.left ⟶ Spec (.of k)}
    {a' : U'.left ⟶ Spec (.of k)} {b' : V'.left ⟶ Spec (.of k)}
    [LocallyOfFiniteType (Over.mk a).hom] [QuasiCompact (Over.mk a).hom] [IsSeparated (Over.mk a).hom]
    [LocallyOfFiniteType (Over.mk b).hom] [QuasiCompact (Over.mk b).hom] [IsSeparated (Over.mk b).hom]
    [LocallyOfFiniteType (Over.mk a').hom] [QuasiCompact (Over.mk a').hom] [IsSeparated (Over.mk a').hom]
    [LocallyOfFiniteType (Over.mk b').hom] [QuasiCompact (Over.mk b').hom] [IsSeparated (Over.mk b').hom]
    (wx : x.left ≫ a = a') (wy : y.left ≫ b = b') (wf : f.left ≫ b = a) (wf' : f'.left ≫ b' = a')
    (sq₁ : IsPullback (Over.homMk (U := Over.mk a') (V := Over.mk a) x.left wx)
      (Over.homMk (V := Over.mk b') f'.left wf') (Over.homMk (V := Over.mk b) f.left wf)
      (Over.homMk y.left wy))
    (c : Compactification f.left) (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ
        (f := Over.homMk (U := Over.mk a) (V := Over.mk b) f.left wf) c sq₁).app K).hom =
      ((boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ c sq).app K).hom := by
  let f₁ := Over.homMk (U := Over.mk a) (V := Over.mk b) f.left wf
  let c₁ : Compactification f₁.left := c
  have h₁ := compactificationPasting_ambientComponent ℓ sq₁ c₁ K
  have h₀ := compactificationPasting_ambientComponent ℓ sq c K
  exact h₁.trans h₀.symm

private theorem sliceFormula
    {x : U' ⟶ U} {y : V' ⟶ V} {f : U ⟶ V} {f' : U' ⟶ V'} (sq : IsPullback x f' f y)
    (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K).hom =
      ((boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ
        (compactificationOverField f) sq).app K).hom ≫
      ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        ((compactificationOverField f).ofIsPullback sq.overLeft) (compactificationOverField f')).hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)).hom := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq,
    boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq']
  rfl

/-- Replacing the four field structures on a cartesian square, keeping its underlying
scheme maps fixed, preserves the chosen compact-support exchange. In the formula of
`LowerShriek/BaseChangeIndependence.lean`, take the chosen compactification of the right
edge and its pullback; these only depend on the scheme arrows. The proper exchange is
the right mate of pullback comparison, and the inverse open exchange is its left mate.
Under the fully faithful inclusion the pullbacks, units and counits in these formulas
are the same for both field structures. For the last compactification comparison take
a common proper refinement and give it the second structure via its proper projection.
Its transition factors through the identity direct image, the open/proper mate, and
composition of direct images. These are again computed by the same ambient units,
counits and pullback comparisons. Thus both refinement transitions, and hence the
composite with the open and proper exchanges, have equal components. -/
public theorem shriekBaseChange_changeStructure
    {x : U' ⟶ U} {y : V' ⟶ V} {f : U ⟶ V} {f' : U' ⟶ V'} (sq : IsPullback x f' f y)
    {a : U.left ⟶ Spec (.of k)} {b : V.left ⟶ Spec (.of k)}
    {a' : U'.left ⟶ Spec (.of k)} {b' : V'.left ⟶ Spec (.of k)}
    [LocallyOfFiniteType (Over.mk a).hom] [QuasiCompact (Over.mk a).hom] [IsSeparated (Over.mk a).hom]
    [LocallyOfFiniteType (Over.mk b).hom] [QuasiCompact (Over.mk b).hom] [IsSeparated (Over.mk b).hom]
    [LocallyOfFiniteType (Over.mk a').hom] [QuasiCompact (Over.mk a').hom] [IsSeparated (Over.mk a').hom]
    [LocallyOfFiniteType (Over.mk b').hom] [QuasiCompact (Over.mk b').hom] [IsSeparated (Over.mk b').hom]
    (wx : x.left ≫ a = a') (wy : y.left ≫ b = b') (wf : f.left ≫ b = a) (wf' : f'.left ≫ b' = a')
    (sq₁ : IsPullback (Over.homMk (U := Over.mk a') (V := Over.mk a) x.left wx)
      (Over.homMk (V := Over.mk b') f'.left wf') (Over.homMk (V := Over.mk b) f.left wf)
      (Over.homMk y.left wy))
    (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁).app K =
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K := by
  let c := compactificationOverField f
  let d := c.ofIsPullback sq.overLeft
  let K' := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K
  have hx := compactificationPasting_changeStructure ℓ sq wx wy wf wf' sq₁ c K
  have hc := compactificationComparison_changeStructure ℓ f' wf' d (compactificationOverField f') K'
  apply ObjectProperty.hom_ext (P := boundedConstructible _)
  refine (sliceFormula ℓ sq₁ K).trans (Eq.trans ?_ (sliceFormula ℓ sq K).symm)
  refine congrArg₂ (· ≫ ·) ?_ ?_
  · exact hx
  · dsimp only [c, d, K', compactificationOverField, Over.homMk_left, boundedConstructibleUpperStar,
      Compactification.ofIsPullback, Functor.comp_obj, ObjectProperty.lift_obj_obj] at hc ⊢
    transport_compactification_component hc

end WeilII
