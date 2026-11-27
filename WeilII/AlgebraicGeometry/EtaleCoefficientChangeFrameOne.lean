module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficientsFrame
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryProductOne

/-! # Coefficient transport on a frame with one equation -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilII

/-- For a one-equation regular immersion the frame class transports as soon as the
supported Kummer boundary of its single equation transports. This uses the right unit
law of the supported cup product and transport along the singleton support equality. -/
theorem etaleCoefficientChange_frameClass_one
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    [HasKummerClass A] [HasKummerClass B] (Φ : SupportedCoefficientChange A B)
    {X Z : Scheme.{u}} (i : Z ⟶ X) [HasInvertibleExponent A X] [HasInvertibleExponent B X]
    (F : i.EtaleFrame 1) :
    letI : HasInvertibleExponent A F.U := .of_hom F.e
    letI : HasInvertibleExponent B F.U := .of_hom F.e
    Φ.mapSupportedClass _ (Φ.tateShiftIso F.U 1)
        (shiftSupportedClass A _ 2 (kummerBoundary A (F.f 0))) =
      shiftSupportedClass B _ 2 (kummerBoundary B (F.f 0)) →
    Φ.mapSupportedClass _ (Φ.tateShiftIso F.U (1 : ℕ)) (frameClass A F) = frameClass B F := by
  let : HasInvertibleExponent A F.U := .of_hom F.e
  let : HasInvertibleExponent B F.U := .of_hom F.e
  intro h
  have hs : ({F.f 0} : Set Γ(F.U, ⊤)) = Set.range F.f := by
    rw [Set.range_unique, Fin.default_eq_zero]
  have transport {s t : Set Γ(F.U, ⊤)} (e : s = t)
      {L : _root_.DerivedCategory (Sheaf F.U.smallEtaleTopology (ModuleCat.{u+1} A))}
      {L' : _root_.DerivedCategory (Sheaf F.U.smallEtaleTopology (ModuleCat.{u+1} B))}
      (τ : (Φ.functor F.U).obj L ≅ L')
      (c : constantComplex A F.U ⟶ (R(F.U.zeroLocusSubschemeι s)_![ModuleCat.{u+1} A]).obj
        ((R(F.U.zeroLocusSubschemeι s)^![A]).obj L)) :
      Φ.mapSupportedClass (F.U.zeroLocusSubschemeι t) τ (c ≫ eqToHom (by rw [e])) =
        Φ.mapSupportedClass (F.U.zeroLocusSubschemeι s) τ c ≫ eqToHom (by rw [e]) := by
    subst t
    simp
  rw [frameClass, frameClass, kummerBoundaryProduct_one, kummerBoundaryProduct_one,
    ← Category.assoc, transport hs]
  rw [Φ.mapSupportedClass_comp_eqToHom (Nat.cast_one (R := ℤ)).symm, h, Category.assoc]

end WeilII
