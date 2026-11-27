module

public import WeilII.AlgebraicGeometry.EtaleKummerPowerPullback
public import WeilII.AlgebraicGeometry.EtaleKummerTateSheafReduction
public import WeilII.AlgebraicGeometry.EtaleSheafScalarSquare
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalarsComp

/-! # Geometric pullback of the coefficient comparison on universal root lines -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Etale AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilII

variable {A B : Type (u+1)} [CommRing A] [CommRing B] (ρ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X)

variable [NeZero (ringChar A)] [NeZero (ringChar B)]
  [HasInvertibleExponent A Z] [HasInvertibleExponent B Z] [HasInvertibleExponent A X] [HasInvertibleExponent B X]

private theorem upperStar_rootLine_comp (R : Type (u+1)) [CommRing R] [NeZero (ringChar R)]
    [HasInvertibleExponent R Z] [HasInvertibleExponent R X] :
    (i)^*[ModuleCat.{u+1} R].map (upperStarTateSheafIso R X).hom ≫ upperStarTateSheafToTateSheaf R i =
      (upperStarComp _ i _ _ (comp_toInvertibleExponentBase (Λ := R) i).symm).inv.app _ ≫
      (upperStarTateSheafIso R Z).hom := by
  let hπ := (comp_toInvertibleExponentBase (Λ := R) i).symm
  have hc : ∀ (π : Z ⟶ invertibleExponentBase.{u} R) (h : π = i ≫ toInvertibleExponentBase (Λ := R) X),
      (upperStarComp _ i _ π h).hom.app _ ≫ (i)^*[AddCommGrpCat.{u+1}].map
        (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar R) (toInvertibleExponentBase (Λ := R) X)) ≫
        upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar R) i =
        upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar R) π := by
    rintro _ rfl
    exact upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp _ i _
  have h := upperStarComp_hom_app_comp_upperStar_map_extendScalars R i _ _ hπ _ _ _ (hc _ hπ)
    (𝟙 (tateSheaf R (invertibleExponentBase.{u} R)))
  erw [CategoryTheory.Functor.map_id, Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact ((upperStarComp (ModuleCat.{u+1} R) i _ _ hπ).app _).eq_inv_comp.mpr h

/-- The direct reduction of the positive root line on the universal bases commutes
with pullback. The coefficient map on local roots raises each root to the ratio
of the two exponents, which commutes with restriction. -/
theorem etaleUniversalRootReduction_pullback :
    (i)^*[ModuleCat.{u+1} B].map (sheafExtendScalarsUpperStarTateSheafIso ρ X).hom ≫
      (upperStarComp _ i _ _ (comp_toInvertibleExponentBase (Λ := B) i).symm).inv.app _ =
    (sheafExtendScalarsCompUpperStarIso ρ i).hom.app _ ≫ (Sheaf.extendScalars _ ρ).map
      ((upperStarComp _ i _ _ (comp_toInvertibleExponentBase (Λ := A) i).symm).inv.app _) ≫
      (sheafExtendScalarsUpperStarTateSheafIso ρ Z).hom := by
  let E := Sheaf.extendScalars Z.smallEtaleTopology ρ
  have hc : ringChar B ∣ ringChar A := (ringChar.spec _ _).mp (by
    rw [← map_natCast ρ, ringChar.Nat.cast_ringChar, map_zero])
  obtain ⟨d, hd⟩ := hc
  have hg (T : Scheme.{u}) [HasInvertibleExponent A T] [HasInvertibleExponent B T] :
      (Sheaf.extendScalarsAdjunction _ ρ).homEquiv _ _ (sheafExtendScalarsTateSheafIso ρ T).hom =
        kummerRootsReduction ρ T hd := by
    apply ((Sheaf.extendScalarsAdjunction _ ρ).homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, tateSheafReduction_eq_pow hd]
    exact (kummerFirstTranspose_pow (ρ := ρ) (𝟙 T.gmSheaf) hd).symm
  have hp := (etaleSheafScalarSquare_iff ρ i (sheafExtendScalarsTateSheafIso ρ X).hom
    (sheafExtendScalarsTateSheafIso ρ Z).hom (upperStarTateSheafToTateSheaf A i)
    (upperStarTateSheafToTateSheaf B i)).mp (by
      rw [hg X, hg Z]
      exact kummerRootsReduction_pullback ρ i hd)
  have hn := (sheafExtendScalarsCompUpperStarIso ρ i).hom.naturality (upperStarTateSheafIso A X).hom
  dsimp only [Functor.comp_map] at hn
  apply (cancel_mono (upperStarTateSheafIso B Z).hom).mp
  dsimp only [sheafExtendScalarsUpperStarTateSheafIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  erw [← upperStar_rootLine_comp i B, ← Functor.map_comp_assoc _ (upperStarTateSheafIso B X).inv,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, hp, reassoc_of% hn]
  erw [← E.map_comp_assoc, upperStar_rootLine_comp i A, E.map_comp]
  simp only [Category.assoc]
  have cancelTail {T U V W Y Z : Sheaf Z.smallEtaleTopology (ModuleCat.{u+1} B)} (a : T ⟶ U) (b : U ⟶ V)
      (c : V ⟶ W) (d : W ⟶ Y) (e : Z ≅ Y) :
      a ≫ b ≫ c ≫ d = (a ≫ b ≫ c ≫ d ≫ e.inv) ≫ e.hom := by simp
  exact cancelTail _ _ _ _ (upperStarTateSheafIso B Z)

end WeilII
