module

public import WeilII.AlgebraicGeometry.ArithmeticDirectImageFrobeniusExchange
public import WeilII.AlgebraicGeometry.ArithmeticOpenFrobeniusExchange
import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
meta import WeilII.Tactic.SchemeComponentCongruence

/-! # Exact Frobenius exchange for the geometric fibre of an arithmetic compactification -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII
universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)} {f : X ⟶ Y}
  (c : Compactification f) (h : f ≫ t = s)

private theorem pasteExchange {A B : Type*} [Category A] [Category B] (R : A ⥤ B)
    {A₁ A₂ A₃ A₄ : A} {B₁ B₂ : B}
    (y : B₁ ⟶ B₂) (p : B₂ ⟶ R.obj A₂) (p' : B₁ ⟶ R.obj A₁)
    (z : A₁ ⟶ A₂) (j : A₂ ⟶ A₄) (j' : A₁ ⟶ A₃) (x : A₃ ⟶ A₄)
    (hp : y ≫ p = p' ≫ R.map z) (hj : z ≫ j = j' ≫ x) :
    y ≫ p ≫ R.map j = (p' ≫ R.map j') ≫ R.map x := by
  rw [← Category.assoc, hp, Category.assoc, ← R.map_comp, hj, R.map_comp, Category.assoc]

private theorem pasteExchangeComponent {A B D : Type*} [Category A] [Category B] [Category D]
    (J : A ⥤ B) (P : B ⥤ D)
    {X X' : A ⥤ A} {Z Z' : B ⥤ B} {Y Y' : D ⥤ D}
    (x : X ≅ X') (z : Z ≅ Z') (y : Y ≅ Y')
    (ej : J ⋙ Z' ≅ X' ⋙ J) (ep : P ⋙ Y' ≅ Z' ⋙ P)
    (bj : J ⋙ Z ≅ X ⋙ J) (bp : P ⋙ Y ≅ Z ⋙ P)
    (bc : (J ⋙ P) ⋙ Y ≅ X ⋙ (J ⋙ P)) (K : A)
    (hp : y.hom.app (P.obj (J.obj K)) ≫ ep.hom.app (J.obj K) =
      bp.hom.app (J.obj K) ≫ P.map (z.hom.app (J.obj K)))
    (hj : z.hom.app (J.obj K) ≫ ej.hom.app K = bj.hom.app K ≫ J.map (x.hom.app K))
    (hb : bc = Adjunction.compForgetIso bj bp) :
    y.hom.app ((J ⋙ P).obj K) ≫
        (ep.hom.app (J.obj K) ≫ P.map (ej.hom.app K)) =
      bc.hom.app K ≫ (J ⋙ P).map (x.hom.app K) := by
  subst bc
  simp only [Adjunction.compForgetIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  exact pasteExchange P _ _ _ _ _ _ _ hp hj

/-- On the geometric fibre of an arithmetic compactification, paste the Frobenius
exchange for its proper direct image with that for the open extension by zero.
The intermediate Frobenius identification cancels by functoriality of the
proper pushforward. This computes the exchange on every underlying complex. -/
theorem arithmeticExactCompactification (K : DerivedCategory
    (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology s.geometricFiber) Ab.{u+1}) (condensedRingObj Λ s.geometricFiber))) :
    let d := c.geometricFiber h
    let R := CondensedRing.rightDerivedLowerShriekOfCompactification Λ d
    let hi := (Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap c.i (c.i_comp_g_comp h)).flip
    let hg := Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap c.g (rfl : c.g ≫ t = _)
    haveI : @WeaklyEtale d.Z d.Z (c.g ≫ t).geometricGaloisFrobenius.asIso.hom :=
      MorphismProperty.of_isPullback hg.flip (inferInstance : WeaklyEtale t.geometricGaloisFrobenius.asIso.hom)
    (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ t.geometricGaloisFrobenius.asIso)).hom.app (R.obj K) ≫
        ((IsoAlgebra.derivedCommIso (lowerStarGeometricFiberMapCompFrobeniusIso Λ c.g (rfl : c.g ≫ t = _))).hom.app
          ((CondensedRing.openImmersionLowerShriek Λ (Scheme.Hom.geometricFiberMap c.i (c.i_comp_g_comp h))).mapDerivedCategory.obj K) ≫
          (CondensedRing.lowerStar Λ (Scheme.Hom.geometricFiberMap c.g (rfl : c.g ≫ t = _))).rightDerivedFunctor.map
            ((IsoAlgebra.derivedExactCommIso (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
              Λ c.i (c.i_comp_g_comp h))).hom.app K)) =
      (rightDerivedLowerShriekOfCompactificationBaseChangeIso Λ d d hi hg).hom.app K ≫
        R.map ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ s.geometricGaloisFrobenius.asIso)).hom.app K) := by
  intro d R hi hg
  let z := (c.g ≫ t).geometricGaloisFrobenius.asIso
  have : @WeaklyEtale d.Z d.Z z.hom := MorphismProperty.of_isPullback hg.flip
    (inferInstance : WeaklyEtale t.geometricGaloisFrobenius.asIso.hom)
  let J := (CondensedRing.openImmersionLowerShriek Λ (Scheme.Hom.geometricFiberMap c.i (c.i_comp_g_comp h))).mapDerivedCategory
  let P := (CondensedRing.lowerStar Λ (Scheme.Hom.geometricFiberMap c.g (rfl : c.g ≫ t = _))).rightDerivedFunctor
  have hp := arithmeticDirectImageFrobeniusExchange Λ c.g (rfl : c.g ≫ t = _) (J.obj K)
  have hj := arithmeticOpenFrobeniusExchange Λ c.i (c.i_comp_g_comp h) K
  dsimp only at hp hj
  have H := pasteExchangeComponent J P
    (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ s.geometricGaloisFrobenius.asIso))
    (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ (c.g ≫ t).geometricGaloisFrobenius.asIso))
    (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv Λ t.geometricGaloisFrobenius.asIso))
    (IsoAlgebra.derivedExactCommIso (openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso Λ c.i (c.i_comp_g_comp h)))
    (IsoAlgebra.derivedCommIso (lowerStarGeometricFiberMapCompFrobeniusIso Λ c.g (rfl : c.g ≫ t = _)))
    (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ hi) (rightDerivedLowerStarBaseChangeIso Λ hg)
    (rightDerivedLowerShriekOfCompactificationBaseChangeIso Λ d d hi hg) K
    (by scheme_component_exact hp using hp) (by scheme_component_exact hj using hj)
    rfl
  dsimp only [R, CondensedRing.rightDerivedLowerShriekOfCompactification, Functor.comp_obj, Functor.comp_map]
  dsimp only [Functor.comp_obj, Functor.comp_map] at H
  scheme_component_exact H using hp

end WeilII
