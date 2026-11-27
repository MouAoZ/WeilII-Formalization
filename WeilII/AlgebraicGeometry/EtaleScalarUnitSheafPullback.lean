module

public import WeilConjectures.SixFunctors.Etale.ScalarExtension.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Pullback of the unit of scalar restriction on étale sheaves -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open AlgebraicGeometry AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace WeilII

/-- Pullback carries the unit for restriction of scalars to the unit on the source. -/
theorem etaleScalarUnitSheafPullback {A B : Type (u+1)} [CommRing A] [CommRing B]
    (ρ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)^*[ModuleCat.{u+1} A].map (ε (Sheaf.restrictScalars Y.smallEtaleTopology ρ)) ≫
        (upperStarRestrictScalarsIso ρ f).hom.app (𝟙_ _) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).map (η (f)^*[ModuleCat.{u+1} B]) =
      η (f)^*[ModuleCat.{u+1} A] ≫ ε (Sheaf.restrictScalars X.smallEtaleTopology ρ) := by
  let a := upperStarLowerStarAdjunction (ModuleCat.{u+1} A) f
  let R := Sheaf.restrictScalars Y.smallEtaleTopology ρ
  apply (a.homEquiv _ _).injective
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right, a.homEquiv_naturality_right,
    upperStarLowerStarAdjunction_homEquiv_η]
  have h := restrictScalars_map_unit_app ρ f (𝟙_ _)
  rw [Adjunction.homEquiv_unit, ← Category.assoc]
  erw [← h, Category.assoc]
  have hm : (f)_*[ModuleCat.{u+1} A].map
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).map (η (f)^*[ModuleCat.{u+1} B])) =
      R.map ((f)_*[ModuleCat.{u+1} B].map (η (f)^*[ModuleCat.{u+1} B])) := rfl
  rw [hm]
  have hb := upperStarLowerStarAdjunction_homEquiv_η (ModuleCat.{u+1} B) f
  rw [Adjunction.homEquiv_unit] at hb
  have hr := R.congr_map hb
  rw [R.map_comp] at hr
  erw [hr]
  have hu := NatTrans.IsMonoidal.unit (τ := (lowerStarCompSheafComposeRestrictScalarsIso ρ f).hom)
  simp only [Functor.LaxMonoidal.comp_ε, lowerStarCompSheafComposeRestrictScalarsIso,
    Iso.refl_hom, NatTrans.id_app] at hu
  exact (Category.comp_id _).symm.trans hu

end WeilII
