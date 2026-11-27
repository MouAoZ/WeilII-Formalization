module

public import WeilII.AlgebraicGeometry.CompactSupportShiftedUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Frobenius on the degree-zero condensed realization of a native Weil sheaf -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Endofunctor
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct

open CompactSupportClasses

universe u

variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
  {X : Scheme.{u}} [X.Over (Spec (.of k))]

set_option quotPrecheck false

local notation "γ" => (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
local notation "U" => CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (γ).hom
local notation "E" => (adicSheafEquivCondensedMod ℓ (X ↘ Spec (.of k)).geometricFiber).functor
local notation "S" => DerivedCategory.singleFunctor (Coeff ℓ (X ↘ Spec (.of k)).geometricFiber) 0
local notation "R" => CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) (γ).inv

/-- Compare derived Frobenius pullback on a single with the single of inverse
pushforward, using exactness and the identification of the two coefficient functors. -/
def singleLowerStarIso :
    (S) ⋙ (pull (ℓ := ℓ) (γ).hom) ≅ (R) ⋙ (S) :=
  Functor.isoWhiskerLeft (S) ((U).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarIsoLowerStarInv _ γ)) ≪≫
    (R).mapDerivedCategorySingleFunctor 0

/-- Geometric Frobenius on the single of a native coefficient module, obtained by
placing its condensed inverse-pushforward structure in degree zero. -/
def singleFrobenius (W : ProEtaleWeilSheaf k ℓ X) :
    (pull (γ).hom).obj ((S).obj ((E).obj W.carrier)) ⟶ (S).obj ((E).obj W.carrier) :=
  (singleLowerStarIso (k := k) (ℓ := ℓ) (X := X)).hom.app ((E).obj W.carrier) ≫
    (S).map (((ProEtaleWeilSheaf.toCondensed k ℓ X).obj W).str.hom)

/-- The condensed single of a morphism of native Weil sheaves commutes with Frobenius
by naturality of the two exact comparisons and the morphism's Weil structure square. -/
theorem singleFrobenius_naturality {V W : ProEtaleWeilSheaf k ℓ X} (j : V ⟶ W) :
    (pull (γ).hom).map ((S).map ((E).map j.hom.f)) ≫ singleFrobenius W =
      singleFrobenius V ≫ (S).map ((E).map j.hom.f) := by
  let T := ProEtaleWeilSheaf.toCondensed k ℓ X
  have nat := (singleLowerStarIso (k := k) (ℓ := ℓ) (X := X)).hom.naturality ((E).map j.hom.f)
  have hj : (R).map ((E).map j.hom.f) ≫ (T.obj W).str.hom =
      (T.obj V).str.hom ≫ (E).map j.hom.f := (T.map j).hom.h
  unfold singleFrobenius
  simp only [Functor.comp_map, Functor.comp_obj] at nat
  rw [← Category.assoc, nat]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) (((S).map_comp _ _).symm.trans
    (((S).congr_map hj).trans ((S).map_comp _ _)))

end WeilII.ExternalProduct
