module

public import WeilII.Paper.GeometricExternalTensorPowerLisse
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseNilInvariance

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

/-- The coordinate external power is lisse. Zhang uses this in the proof of Lemma 2.2.
Apply geometric lissity with the identity of the algebraic closure. The resulting map
of affine spaces is the identity followed by the canonical isomorphism to the geometric
fiber. Pullback along this isomorphism reflects lissity. -/
public theorem affineLineExternalTensorPower_isLisse
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (E : WeilSheaf k ℓ (affineLine k)) (hE : E.IsLisse) (n : ℕ) (hn : 2 ≤ n) :
    (affineLineExternalTensorPower E hE n).IsLisse := by
  let e := AlgEquiv.refl (R := k) (A₁ := AlgebraicClosure k)
  let I := ULift.{u} (Fin n)
  let j := AffineSpace.map I (Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom))
  have hj : j = 𝟙 _ := by
    change AffineSpace.map I (Spec.map (𝟙 (CommRingCat.of (AlgebraicClosure k)))) = _
    rw [Spec.map_id, AffineSpace.map_id]
  have ij : IsIso j := hj ▸ IsIso.id _
  let toFiber :=
    (AffineSpace.isPullback_map (n := I) (Scheme.specAlgebraicClosure k).hom).isoPullback
  let : IsIso (j ≫ toFiber.hom) := IsIso.comp_isIso' ij toFiber.isIso_hom
  have hg := geometricExternalTensorPowerLisse E hE n hn (AlgebraicClosure k) e
  exact ProEtale.IsAdicLisseSheaf.of_upperStar_of_isIso (j ≫ toFiber.hom) hg

end WeilII
