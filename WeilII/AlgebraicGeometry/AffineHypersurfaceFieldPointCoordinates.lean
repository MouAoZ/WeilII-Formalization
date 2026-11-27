module

public import WeilII.AlgebraicGeometry.AffineHypersurfaceFieldPoints

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The hypersurface equivalence reads the ambient coordinates after the inclusion, by its
construction. This is the closed-point change of variables in Zhang, equation (2.2.1). -/
public theorem affineHypersurfaceFieldPoints_apply
    (k L : Type u) [Field k] [Field L] [Algebra k L] {n : ℕ} (P : MvPolynomial (Fin n) k) :
    let S := Spec (CommRingCat.of k)
    let X := 𝔸(ULift.{u} (Fin n); S)
    let coeff := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ S).appTop).hom
    let p := MvPolynomial.eval₂Hom coeff (fun j : Fin n ↦ AffineSpace.coord S (ULift.up.{u} j)) P
    let i := X.zeroLocusSubschemeι {p}
    letI : (X.zeroLocusSubscheme {p}).Over S := ⟨i ≫ X ↘ S⟩
    letI : i.IsOver S := ⟨rfl⟩
    ∀ y : (i ≫ X ↘ S).fieldPoints L, (affineHypersurfaceFieldPoints k L P y).1 =
      fun r ↦ AffineSpace.fieldPointsEquivPi (ULift.{u} (Fin n)) k L (i.mapFieldPoints L y) (ULift.up r) := by
  intro S X coeff p i y
  rfl

end WeilII
