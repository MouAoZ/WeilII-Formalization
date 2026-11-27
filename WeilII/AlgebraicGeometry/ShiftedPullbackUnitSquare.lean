module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingBaseChange
import WeilConjectures.WeilSheaf.SmoothPurityShiftDatumSquare
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Pullback squares on the shifted tensor unit -/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProEtale.CondensedRing CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace WeilII

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}) [MonObj Λ] [IsCommMonObj Λ]

private theorem shift_square_of_unit_comparison {C A D B : Type*} [Category* C] [Category* A] [Category* D] [Category* B]
    [HasShift C ℤ] [HasShift A ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (F : C ⥤ A) (G : A ⥤ B) (H : C ⥤ D) (I : D ⥤ B)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [I.CommShift ℤ]
    (α : H ⋙ I ⟶ F ⋙ G) [α.CommShift ℤ]
    {x : C} {y : A} {z : D} {w : B} (u : F.obj x ≅ y) (v : I.obj z ≅ w)
    (r : H.obj x ≅ z) (s : G.obj y ≅ w)
    (h : α.app x = I.map r.hom ≫ v.hom ≫ s.inv ≫ G.map u.inv) (n : ℤ) :
    α.app ((shiftFunctor _ n).obj x) ≫
        G.map ((F.commShiftIso n).hom.app x ≫ (shiftFunctor _ n).map u.hom) ≫
        (G.commShiftIso n).hom.app y ≫ (shiftFunctor _ n).map s.hom =
      I.map ((H.commShiftIso n).hom.app x ≫ (shiftFunctor _ n).map r.hom) ≫
        (I.commShiftIso n).hom.app z ≫ (shiftFunctor _ n).map v.hom := by
  apply purity_shift_datum_square
  rw [h]
  simp [Category.assoc, ← G.map_comp_assoc]

/-- For any commutative square of schemes, derived pullback of the shifted tensor unit
identifies with the shifted tensor unit by either path. The unshifted comparison is
`pullbackSquareComparison_hom_app_unit`, and pullback exchange commutes with shifts. -/
theorem pullbackSquare_shiftedUnit {X Y X' Y' : Scheme.{u}}
    {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : CommSq g' p' p g) (n : ℤ) :
    let u {T S : Scheme.{u}} (a : T ⟶ S) :=
      (L((a)^*⟦Λ⟧).commShiftIso n).app _ ≪≫
        (shiftFunctor _ n).mapIso (leftDerivedUpperStarUnitIso Λ a)
    (pullbackSquareComparison Λ sq).hom.app ((shiftFunctor _ n).obj _) ≫
        L((g')^*⟦Λ⟧).map (u p).hom ≫ (u g').hom =
      L((p')^*⟦Λ⟧).map (u g).hom ≫ (u p').hom := by
  intro u
  dsimp only [u, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  exact shift_square_of_unit_comparison _ _ _ _ (pullbackSquareComparison Λ sq).hom
    (leftDerivedUpperStarUnitIso Λ p) (leftDerivedUpperStarUnitIso Λ p')
    (leftDerivedUpperStarUnitIso Λ g) (leftDerivedUpperStarUnitIso Λ g')
    (pullbackSquareComparison_hom_app_unit Λ sq) n

end WeilII
