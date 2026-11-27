module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.FieldPoints
public import WeilConjectures.WeilSheaf.TraceFunctionOps

/-! # Rational points and coordinate projections

The coordinate change used for Zhang, Lemma 2.2. -/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- Applying a coordinate projection to a field point gives its indicated coordinate.
Pull back the distinguished affine-line section along the composite of the point and
the projection. Its first pullback is the indicated coordinate section.
Source: the coordinate projections in Zhang's equation (2.2.1). -/
public theorem fieldPointsEquiv_coordinateProjection
    {k L : Type u} [Field k] [Field L] [Algebra k L] {I : Type u}
    (j : I) (x : (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).fieldPoints L) :
    let S := Spec (CommRingCat.of k)
    let proj := AffineSpace.reindex (fun _ : PUnit.{u + 1} ↦ j) S
    letI : proj.IsOver S := ⟨AffineSpace.reindex_over _ _⟩
    AffineSpace.fieldPointsEquiv k L (proj.mapFieldPoints L x) =
      AffineSpace.fieldPointsEquivPi I k L x j := by
  intro S proj
  rw [AffineSpace.fieldPointsEquiv_apply, AffineSpace.fieldPointsEquivPi_apply,
    Scheme.Hom.mapFieldPoints_coe, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.reindex_appTop_coord]

end WeilII
