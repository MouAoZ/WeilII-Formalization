module

public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Polynomial sections under base change of affine space
-/

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u v

/-- Pullback of a polynomial in affine coordinates along a change of base ring applies the
ring map to its coefficients. The coordinate assignment allows the polynomial variables
and the affine-space coordinates to lie in different universes. -/
public theorem affineSpace_map_appTop_eval₂Hom {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {I : Type u} {σ : Type v} (j : σ → I) (P : MvPolynomial σ R) :
    let X := 𝔸(I; Spec R)
    let Y := 𝔸(I; Spec S)
    let coeffR := ((Scheme.ΓSpecIso R).inv ≫ (X ↘ Spec R).appTop).hom
    let coeffS := ((Scheme.ΓSpecIso S).inv ≫ (Y ↘ Spec S).appTop).hom
    let b := AffineSpace.map I (Spec.map φ)
    b.appTop (MvPolynomial.eval₂Hom coeffR (fun i ↦ AffineSpace.coord (Spec R) (j i)) P) =
      MvPolynomial.eval₂Hom coeffS (fun i ↦ AffineSpace.coord (Spec S) (j i))
        (MvPolynomial.map φ.hom P) := by
  intro X Y coeffR coeffS b
  have hcoeff : b.appTop.hom.comp coeffR = coeffS.comp φ.hom := by
    change ((Scheme.ΓSpecIso R).inv ≫ (X ↘ Spec R).appTop ≫ b.appTop).hom =
      (φ ≫ (Scheme.ΓSpecIso S).inv ≫ (Y ↘ Spec S).appTop).hom
    rw [← Scheme.Hom.comp_appTop, AffineSpace.map_over, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc]
  change b.appTop.hom (MvPolynomial.eval₂Hom coeffR _ P) = _
  rw [MvPolynomial.map_eval₂Hom, hcoeff, MvPolynomial.eval₂Hom_map_hom]
  have hcoord (i : σ) : b.appTop.hom (AffineSpace.coord (Spec R) (j i)) =
      AffineSpace.coord (Spec S) (j i) := AffineSpace.map_appTop_coord _ _
  simp only [hcoord]

end WeilII
