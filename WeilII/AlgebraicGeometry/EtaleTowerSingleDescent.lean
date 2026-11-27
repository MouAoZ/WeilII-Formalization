module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology

/-! # Descent of an ordinary tower of étale sheaves in degree zero -/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open Opposite

namespace WeilII

universe u

/-- The right derived comparison direct image recovers a tower of abelian étale sheaves
in degree zero from its termwise inverse image. Evaluate a K-injective resolution of
the tower. Evaluation preserves K-injectivity by its exact left adjoint. At each vertex
the bounded-below comparison unit is invertible (Bhatt–Scholze, Corollary 5.1.6).
Thus the result has cohomology only in degree zero. Its zeroth cohomology, computed
on the whole tower by left exactness, is the ordinary direct image, whose adjunction
unit identifies it with the original tower including its transition maps. -/
theorem etaleTowerSingleDescent (V : Scheme.{u})
    [IsGrothendieckAbelian.{u+1} (ℕᵒᵖ ⥤ Sheaf V.smallEtaleTopology Ab.{u+1})]
    [IsGrothendieckAbelian.{u+1} (ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology V) Ab.{u+1})]
    (C : ℕᵒᵖ ⥤ Sheaf V.smallEtaleTopology Ab.{u+1}) :
    let L := comparisonUpperStar Ab.{u+1} V
    let R := comparisonLowerStar Ab.{u+1} V
    let G := (Functor.whiskeringRight ℕᵒᵖ _ _).obj R
    Nonempty (G.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj (C ⋙ L)) ≅
      (DerivedCategory.singleFunctor _ 0).obj C) := by
  intro L R G
  let D := (DerivedCategory.singleFunctor _ 0).obj (C ⋙ L)
  let K := G.rightDerivedFunctor.obj D
  have vertex (n : ℕᵒᵖ) :
      Nonempty (((evaluation ℕᵒᵖ _).obj n).mapDerivedCategory.obj K ≅
        (DerivedCategory.singleFunctor _ 0).obj (C.obj n)) := by
    let A := (evaluation ℕᵒᵖ (Sheaf (Scheme.ProEt.topology V) Ab.{u+1})).obj n
    let B := (evaluation ℕᵒᵖ (Sheaf V.smallEtaleTopology Ab.{u+1})).obj n
    let : A.PreservesKInjectiveComplexes :=
      ⟨fun I _ ↦ tower_evaluation_isKInjective _ I n⟩
    let q : G ⋙ B ≅ A ⋙ R := Iso.refl _
    let t := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso G B).symm ≪≫
      Functor.rightDerivedFunctorNatIso q ≪≫ Functor.mapDerivedCategoryCompRightDerivedFunctorIso A R
    let N := (DerivedCategory.singleFunctor _ 0).obj (C.obj n)
    let adj := derivedComparisonAdjunction Ab.{u+1} V
    have := isIso_derivedComparisonAdjunction_unit_app Ab.{u+1} V N ⟨0, inferInstance⟩
    exact ⟨t.app D ≪≫ R.rightDerivedFunctor.mapIso
      ((A.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        ((L.mapDerivedCategorySingleFunctor 0).app _).symm) ≪≫ (asIso (adj.unit.app N)).symm⟩
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
    apply (Functor.isZero_iff _).2
    intro n
    obtain ⟨e⟩ := vertex n
    exact (DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor e hi).of_iso
      ((((evaluation ℕᵒᵖ _).obj n).mapDerivedCategoryHomologyFunctorIso i).app K)
  have : K.IsGE 0 := (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hz i (by omega)
  have : K.IsLE 0 := (DerivedCategory.isLE_iff _ _).2 fun i hi ↦ hz i (by omega)
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  let h := (DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app Y
  let η := (comparisonAdjunction Ab.{u+1} V).unit
  have := isIso_comparisonAdjunction_unit Ab.{u+1} V
  let j : C ≅ (C ⋙ L) ⋙ R := (Functor.rightUnitor C).symm ≪≫
    Functor.isoWhiskerLeft C (asIso η) ≪≫ (Functor.associator C L R).symm
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
    (h.symm ≪≫ G.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso.app _ ≪≫ j.symm)⟩

end WeilII
