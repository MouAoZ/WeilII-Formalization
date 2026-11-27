module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateTwist
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift

/-! # Coefficient reduction of a class carried by a direct image -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace WeilII

/-- Transpose a class on the source of a morphism and move its shift outside the direct
image. Reduction carries this transpose to the transpose of the reduced class, through the
mate of pullback exchange. This applies in particular to the open part of localization. -/
theorem etaleScalarReduction_shiftedAdjoint
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {ρ : A →+* B}
    (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a})
    {V X : Scheme.{u}} (j : V ⟶ X)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A)))
    (M : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u+1} A)))
    (N : _root_.DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u+1} B)))
    (m : ℤ) (y : (L((j)^*[ModuleCat.{u + 1} A])).obj K ⟶ M⟦m⟧)
    (p : (derivedExtendScalars hρ ha V).obj M ⟶ N) :
    letI := derivedExtendScalarsCommShift hρ ha X
    letI := derivedExtendScalarsCommShift hρ ha V
    let Ψ := derivedExtendScalars hρ ha X
    let ΨV := derivedExtendScalars hρ ha V
    let RA := R((j)_*[ModuleCat.{u+1} A])
    let RB := R((j)_*[ModuleCat.{u+1} B])
    NatTrans.CommShift (derivedExtendScalarsPullbackMap hρ ha j) ℤ →
      Ψ.map ((derivedUpperStarLowerStarAdjunction _ j).unit.app K ≫ RA.map y ≫
          (RA.commShiftIso m).hom.app M) ≫ (Ψ.commShiftIso m).hom.app _ ≫
          ((derivedExtendScalarsLowerStarMap hρ ha j).app M ≫ RB.map p)⟦m⟧' =
        (derivedUpperStarLowerStarAdjunction _ j).unit.app (Ψ.obj K) ≫
          RB.map ((derivedExtendScalarsPullbackIso hρ ha j).inv.app K ≫ ΨV.map y ≫
            (ΨV.commShiftIso m).hom.app M ≫ p⟦m⟧') ≫ (RB.commShiftIso m).hom.app N := by
  let := derivedExtendScalarsCommShift hρ ha X
  let := derivedExtendScalarsCommShift hρ ha V
  dsimp only
  intro h
  have : NatTrans.CommShift (derivedExtendScalarsPullbackIso hρ ha j).hom ℤ := h
  have : NatTrans.CommShift (derivedExtendScalarsLowerStarMap hρ ha j) ℤ :=
    NatTrans.CommShift.mateEquiv
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)
      (TwoSquare.mk _ _ _ _ (derivedExtendScalarsPullbackIso hρ ha j).inv)
  have hs := NatTrans.shift_app_comm (derivedExtendScalarsLowerStarMap hρ ha j) m M
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj, Category.assoc] at hs
  have hn := (derivedExtendScalarsLowerStarMap hρ ha j).naturality y
  have hu := map_unit_comp_derivedExtendScalarsLowerStarMap_app hρ ha j K
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs, reassoc_of% hn, reassoc_of% hu]
  rw [Functor.commShiftIso_hom_naturality]

end WeilII
