module

public import WeilII.CategoryTheory.OpenProperProjectionComponents
public import WeilII.AlgebraicGeometry.CompactifiedExceptionalProjection
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion
import Mathlib.Util.TermReduce

/-! # Open and proper factors of a bounded compactified projection -/

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilII

universe u

/-- The bundled projection of a specified compactification has the open–proper component
formula. In the definition of the bundle its component is the bounded morphism induced by
`exceptionalProjectionMorphismOfCompactification`. Apply
`homMk_exceptionalProjectionMorphismOfCompactification_eq` (pinned WeilConjectures,
`PoincareDuality/ProjectionFormulaOpenImmersion.lean`, line 188) with the inverse of the
pullback triangle as coefficient comparison. The hypothesis on the underlying coefficient
map is `ι_map_eqToIso_trans_upperStarComp_inv_app_compactification` in the same file,
line 377, since the triangle is the composition comparison transported along
`c.overI_overG`. The proper and general bounded direct images are the lifts of the same
ambient direct image and agree by proof irrelevance for the preservation property. -/
public theorem isOpenProperProjection_compactified
    {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] {U V : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (f : U ⟶ V) (c : Compactification f.left) :
    @IsOpenProperProjection _ _ _ _ _ _
      (delta% delta% monoidalCategory_boundedConstructible (ℓ := ℓ) U)
      (delta% delta% monoidalCategory_boundedConstructible (ℓ := ℓ) c.overObj)
      (delta% delta% monoidalCategory_boundedConstructible (ℓ := ℓ) V)
      (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.overI) _
      (boundedConstructibleLowerStar ℓ c.overG)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ c.overG) _
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ c.overI)
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ c.overG) _
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
      (compactifiedExceptionalProjection ℓ f c)
      (boundedConstructibleUpperStarTriangleComparison _ ℓ c.overI_overG) := by
  generalize ht : boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ
    c.overI_overG = t
  intro A B
  refine homMk_exceptionalProjectionMorphismOfCompactification_eq ℓ c A B (t.inv.app B) ?_
  have h := ι_map_eqToIso_trans_upperStarComp_inv_app_compactification ℓ c B
  refine Eq.trans ?_ h
  apply congrArg _
  apply congrArg (fun e : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ≅
      boundedConstructibleUpperStar _ ℓ c.overG ⋙ boundedConstructibleUpperStar _ ℓ c.overI ↦
    e.inv.app B)
  exact ht.symm

end WeilII
