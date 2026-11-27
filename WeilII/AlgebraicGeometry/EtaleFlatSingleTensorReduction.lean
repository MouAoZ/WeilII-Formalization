module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionMonoidal
public import WeilConjectures.WeilSheaf.SmoothPuritySingleFlatNaturality
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization
import WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
import all Mathlib.Algebra.Homology.Localization

/-! # The derived tensor comparison on two degree-zero sheaves -/

@[expose] public section
universe u v w
set_option backward.defeqAttrib.useBackward true

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace WeilII

variable {A : Type v} [Category.{u+1} A] [Abelian A] [IsGrothendieckAbelian.{u+1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {B : Type w} [Category.{u+1} B] [Abelian B] [IsGrothendieckAbelian.{u+1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] {X : Scheme.{u}}
  (U : Sheaf X.smallEtaleTopology A ⥤
    Sheaf X.smallEtaleTopology B) [U.Additive] [U.Monoidal]
  [U.IsLeftAdjoint] [U.PreservesFlat] [U.PreservesKFlatQuasiIso]

omit [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] [U.Monoidal] [U.IsLeftAdjoint] [U.PreservesFlat] in
private theorem singleComparison_counit (L : Sheaf X.smallEtaleTopology A) :
    U.puritySingleComparison.app L ≫ (singleFunctorObjIsoQh (U.obj L)).hom =
      L(U).map (singleFunctorObjIsoQh L).hom ≫ U.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj ((HomologicalComplex.single _ (.up ℤ) 0).obj L)) ≫
      _root_.DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app L)) := by
  have qC : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
      (Sheaf X.smallEtaleTopology A)).inv.app K = 𝟙 _ := fun _ ↦ rfl
  have qD : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
      (Sheaf X.smallEtaleTopology B)).hom.app K = 𝟙 _ := fun _ ↦ rfl
  have qDi : ∀ K, (_root_.DerivedCategory.quotientCompQhIso
      (Sheaf X.smallEtaleTopology B)).inv.app K = 𝟙 _ := fun _ ↦ rfl
  have hc : ∀ K, (U.mapHomotopyCategoryFactors (.up ℤ)).hom.app K = 𝟙 _ := fun _ ↦ rfl
  simp only [Functor.puritySingleComparison, singleFunctorObjIsoQh,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc, qC, qD, qDi, hc]
  repeat first
    | erw [Category.comp_id]
    | erw [_root_.DerivedCategory.Qh.map_id]
    | erw [Category.id_comp]
  rfl

/-- For an additive strong monoidal left adjoint preserving flat sheaves and
K-flat quasi-isomorphisms, the tensor comparison on singles is induced by its
ordinary tensor comparison. Flatness of the first factor computes both tensor products. -/
theorem etaleFlatSingleTensor_reduction
    (L M : Sheaf X.smallEtaleTopology A) (hL : ObjectProperty.flat L) :
    U.leftDerivedFunctor.map (singleFunctorObjTensorIso L M hL).hom ≫
        U.puritySingleComparison.app (L ⊗ M) ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map (Functor.OplaxMonoidal.δ U L M) =
      (U.leftDerivedTensorComparison.app ((_root_.DerivedCategory.singleFunctor _ 0).obj L)).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ≫
        (U.puritySingleComparison.app L ⊗ₘ U.puritySingleComparison.app M) ≫
        (singleFunctorObjTensorIso (U.obj L) (U.obj M) (Functor.PreservesFlat.flat_obj hL)).hom := by
  let H := U.mapHomotopyCategory (.up ℤ)
  let F := U.leftDerivedFunctor
  let q := HomotopyCategory.quotient (Sheaf X.smallEtaleTopology A) (.up ℤ)
  let q' := HomotopyCategory.quotient (Sheaf X.smallEtaleTopology B) (.up ℤ)
  let s := HomologicalComplex.single (Sheaf X.smallEtaleTopology A) (.up ℤ) 0
  let s' := HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0
  let c := HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0
  rw [singleFunctorObjTensorIso_homotopy_factorization L M hL,
    singleFunctorObjTensorIso_homotopy_factorization (U.obj L) (U.obj M)
      (Functor.PreservesFlat.flat_obj hL)]
  apply tensor_comparison_transport _root_.DerivedCategory.Qh _root_.DerivedCategory.Qh H F
    U.leftDerivedTensorComparison U.leftDerivedFunctorCounit (q.obj (s.obj L)) (q.obj (s.obj M))
    (q.obj (s.obj (L ⊗ M))) (q'.obj (s'.obj (U.obj L))) (q'.obj (s'.obj (U.obj M)))
    (q'.obj (s'.obj (U.obj L ⊗ U.obj M))) (q.map (singleCochainTensorIso L M).hom)
    (q'.map (singleCochainTensorIso (U.obj L) (U.obj M)).hom)
    (q'.map (c.hom.app L)) (q'.map (c.hom.app M))
    (q'.map (c.hom.app (L ⊗ M)) ≫ q'.map (s'.map (Functor.OplaxMonoidal.δ U L M)))
    (singleHomotopyTensorIso_pullback U L M)
    (U.leftDerivedTensorComparison_app_app_comp_tensorHom _ _)
    (singleFunctorObjIsoQh L) (singleFunctorObjIsoQh M) (singleFunctorObjIsoQh (L ⊗ M))
    (singleFunctorObjIsoQh (U.obj L)) (singleFunctorObjIsoQh (U.obj M))
    (singleFunctorObjIsoQh (U.obj L ⊗ U.obj M)) _ _ _
    (singleComparison_counit U L) (singleComparison_counit U M)
  rw [Category.assoc, single_isoQh_naturality, ← Category.assoc, singleComparison_counit]
  simp only [Category.assoc, Functor.map_comp]
  rfl

end WeilII
