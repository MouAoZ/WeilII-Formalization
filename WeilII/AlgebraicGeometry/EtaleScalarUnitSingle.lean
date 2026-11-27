module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionMonoidal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerTranspose
public import WeilConjectures.SixFunctors.Etale.ScalarExtension.Monoidal
import WeilII.CategoryTheory.DerivedUnitFlatSingle
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # The scalar reduction unit on a flat single complex -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal Functor.LaxMonoidal
open AlgebraicGeometry AlgebraicGeometry.Etale

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace WeilII

/-- The derived scalar unit is the transpose of the restriction unit placed in degree zero. -/
theorem etaleScalarUnitSingle {A B : Type (u+1)} [CommRing A] [CommRing B] {ρ : A →+* B}
    (hρ : Function.Surjective ρ) {a : A} (ha : RingHom.ker ρ = Ideal.span {a}) (X : Scheme.{u}) :
    (derivedExtendScalarsConstantComplexEtaIso hρ ha X).hom =
      (derivedExtendScalars hρ ha X).map (singleFunctorObjUnitIso (ModuleCat.{u+1} A) X).inv ≫
      ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars X.smallEtaleTopology ρ)
        (derivedExtendScalarsAdjunction hρ ha X) (ε (Sheaf.restrictScalars X.smallEtaleTopology ρ)) ≫
      (singleFunctorObjUnitIso (ModuleCat.{u+1} B) X).hom := by
  let F := Sheaf.extendScalars X.smallEtaleTopology ρ
  let adj := Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  have hflat : ObjectProperty.flat (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A))) :=
    ObjectProperty.flat_of_tensorIso (MonoidalCategory.leftUnitor _)
  have hmodel := leftDerivedUnit_flatSingle F hflat
  have htranspose := adj.singleTranspose_derivedAdjunctionMapDerivedCategory hflat
    (ε (Sheaf.restrictScalars X.smallEtaleTopology ρ))
  have hB : (singleFunctorObjUnitIso (ModuleCat.{u+1} B) X).hom = 𝟙 _ := by
    have h := (singleFunctorObjUnitIso (ModuleCat.{u+1} B) X).hom_inv_id
    rw [singleFunctorObjUnitIso_inv] at h
    exact (Category.comp_id _).symm.trans h
  have hC (K) : (_root_.DerivedCategory.quotientCompQhIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A))).hom.app K = 𝟙 _ := rfl
  have hD (K) : (_root_.DerivedCategory.quotientCompQhIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} B))).inv.app K = 𝟙 _ := rfl
  erw [hC, hD, F.leftDerivedFunctor.map_id, Category.id_comp, Category.comp_id] at hmodel
  erw [singleFunctorObjUnitIso_inv, CategoryTheory.Functor.map_id, Category.id_comp,
    hB, Category.comp_id]
  exact hmodel.trans htranspose.symm

end WeilII
