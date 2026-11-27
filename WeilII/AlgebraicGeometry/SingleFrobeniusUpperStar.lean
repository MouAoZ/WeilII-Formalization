module

import WeilConjectures.Tactic.TransportExact
public import WeilII.AlgebraicGeometry.FrobeniusPullbackSingleComparison

/-! # The pullback presentation of Frobenius on a degree-zero Weil sheaf -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct
open CompactSupportClasses

universe u
variable {ℓ : ℕ} [Fact ℓ.Prime]
set_option quotPrecheck false
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "U" => CondensedRing.upperStar Λ
local notation "S" X => DerivedCategory.singleFunctor (Coeff ℓ X) 0
local notation "λ₀" f => (U f).singleFunctorCompLeftDerivedFunctorIso.hom

private theorem whiskeredAction {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ C} {G H : D ⥤ D} (E : C ⥤ D) (t : G ≅ H)
    (a : E ⋙ H ≅ F ⋙ E) (W : Endofunctor.IsoAlgebra F) :
    ((Endofunctor.IsoAlgebra.mapOfNatIso (Functor.isoWhiskerLeft E t ≪≫ a)).obj W).str.hom =
      t.hom.app (E.obj W.carrier) ≫ ((Endofunctor.IsoAlgebra.mapOfNatIso a).obj W).str.hom :=
  Category.assoc _ _ _

private theorem changeAction {C D : Type*} [Category* C] [Category* D] (J : C ⥤ D)
    {x y z : C} {w : D} (l : w ⟶ J.obj x) (m : w ⟶ J.obj y)
    (v : x ⟶ y) (s : y ⟶ z) (r : x ⟶ z)
    (hl : m = l ≫ J.map v) (hr : r = v ≫ s) :
    m ≫ J.map s = l ≫ J.map r := by
  rw [hl, hr, J.map_comp, Category.assoc]

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
local notation "γX" => (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
local notation "JX" => S (X ↘ Spec (.of k)).geometricFiber
local notation "EX" => (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
local notation "TX" => ProEtaleWeilSheaf.toCondensedUpperStar k ℓ X
/-- Frobenius on a single in the ordinary geometric pullback presentation. -/
theorem singleFrobenius_upperStar (W : ProEtaleWeilSheaf k ℓ X) :
    singleFrobenius W = (λ₀ (γX).hom).app ((EX).obj W.carrier) ≫ (JX).map
      (((TX).obj W).str.hom) := by
  unfold singleFrobenius
  fo_apply (changeAction (JX)) using
    (λ₀ (γX).hom).app ((EX).obj W.carrier),
    (singleLowerStarIso (k := k) (X := X) (ℓ := ℓ)).hom.app ((EX).obj W.carrier),
    (CondensedRing.upperStarIsoLowerStarInv Λ (γX)).hom.app ((EX).obj W.carrier),
    ((ProEtaleWeilSheaf.toCondensed k ℓ X).obj W).str.hom,
    ((TX).obj W).str.hom,
    fo_late (singleLowerStarIso_hom_app (k := k) (X := X) ((EX).obj W.carrier)),
    fo_late (whiskeredAction (EX) (CondensedRing.upperStarIsoLowerStarInv Λ (γX))
      (ProEtaleWeilSheaf.condensedFrobeniusComparison k ℓ X) W)

end WeilII.ExternalProduct
