module

public import WeilII.AlgebraicGeometry.EtalePositiveTatePowerComparison

/-! # Identifying the supported and direct positive Tate reductions -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale

namespace WeilII

/-- Both degree-two positive-Tate comparisons are the shifted first transpose of
the Kummer power morphism, so the supported comparison equals the direct one. -/
theorem etaleSupportedPositiveTateReduction
    {A B : Type (u+1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [NeZero (ringChar A)] [NeZero (ringChar B)] {ρ : A →+* B}
    (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    (X : Scheme.{u}) [HasInvertibleExponent A X] [HasInvertibleExponent B X]
    {d : ℕ} (hd : ringChar A = ringChar B * d) :
    ((reductionSupportedCoefficientChange hρ ha (reductionTateShiftData hρ ha)).tateShiftIso X 1).hom =
      (derivedExtendScalarsTateShiftIso hρ ha X 1).hom := by
  let φ := unitToGmSheaf (1 : Γ(X, ⊤)ˣ)
  let := derivedExtendScalarsCommShift hρ ha X
  change _ = (Functor.commShiftIso _ (2 : ℤ)).hom.app _ ≫
    (derivedExtendScalarsTateObjectIso hρ ha X 1).hom⟦(2 : ℤ)⟧'
  rw [positiveTateObjectReduction_eq_kummer φ hd hρ ha]
  exact etaleDivisorPositiveTatePowerComparison hρ ha φ hd

end WeilII
