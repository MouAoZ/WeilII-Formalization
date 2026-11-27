module

public import WeilII.AlgebraicGeometry.EtaleTateSheafEvaluationReduction
import WeilII.AlgebraicGeometry.EtaleSingleOnefoldEvaluation
import WeilII.AlgebraicGeometry.EtalePullbackUnitSingle
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback

/-! # The evaluation pairing in the degree-zero models of the Tate objects -/

@[expose] public section
universe u v
open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Etale
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Functor
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option maxHeartbeats 70000

namespace WeilII

private noncomputable abbrev onefoldEval {C : Type*} [Category* C] [MonoidalCategory C] {P : C}
    (e : TensorInverse P) : e.zpow 1 ⊗ e.zpow (-1) ⟶ 𝟙_ C :=
  (e.addIso 1 (-1) 0 rfl).hom

private theorem pullSinglePair {B : Type v} [Category.{u+1} B] [Abelian B]
    [IsGrothendieckAbelian.{u+1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M N : Sheaf Y.smallEtaleTopology B) (hM : ObjectProperty.flat M)
    (ev : M ⊗ N ⟶ 𝟙_ _) :
    let F := (p)^*[B]
    let D := L((p)^*[B])
    let S := _root_.DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology B) 0
    let T := _root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology B) 0
    let γ := (singleFunctorCompLeftDerivedUpperStarIso B p).hom
    letI := leftDerivedUpperStarOplaxMonoidal B p
    D.map ((singleFunctorObjTensorIso M N hM).hom ≫ S.map ev ≫ (singleFunctorObjUnitIso B Y).hom) ≫
        η D =
      δ D _ _ ≫ (γ.app M ⊗ₘ γ.app N) ≫
        (singleFunctorObjTensorIso (F.obj M) (F.obj N) (Functor.PreservesFlat.flat_obj hM)).hom ≫
        T.map (μ F M N ≫ F.map ev ≫ η F) ≫ (singleFunctorObjUnitIso B X).hom := by
  let F := (p)^*[B]
  let D := L((p)^*[B])
  let S := _root_.DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology B) 0
  let T := _root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology B) 0
  let γ := (singleFunctorCompLeftDerivedUpperStarIso B p).hom
  let := leftDerivedUpperStarOplaxMonoidal B p
  have hu := etalePullbackUnitSingle B p
  have he : D.map (singleFunctorObjUnitIso B Y).hom ≫ η D =
      γ.app _ ≫ T.map (η F) ≫ (singleFunctorObjUnitIso B X).hom := by
    apply (cancel_epi (D.map (singleFunctorObjUnitIso B Y).inv)).1
    simp only [Iso.inv_hom_id_map_assoc]
    rw [reassoc_of% hu, Iso.inv_hom_id, Category.comp_id]
  have ht := singleFunctorObjTensorIso_pullback p M N hM
  have hn : D.map (S.map ev) ≫ γ.app _ = γ.app _ ≫ T.map (F.map ev) := γ.naturality ev
  dsimp only
  simp only [Functor.map_comp, Category.assoc]
  erw [he, reassoc_of% hn, ← reassoc_of% ht]
  have hc := Functor.Monoidal.δ_μ F M N
  erw [← T.map_comp_assoc (δ F M N) (μ F M N), hc, T.map_id, Category.id_comp]

private theorem copyPullPair {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (P : IntTensorFamily C) (F : C ⥤ D)
    [F.OplaxMonoidal] [IsIso (η F)] [∀ X Y, IsIso (δ F X Y)]
    (T : ℤ → D) (hT : T = (P.map F).obj)
    {S N : C} {S' N' : D} (s : P.obj 1 ⟶ S) (n : P.obj (-1) ⟶ N)
    (i : F.obj S ⟶ S') (j : F.obj N ⟶ N') (e : S ⊗ N ⟶ 𝟙_ C) (e' : S' ⊗ N' ⟶ 𝟙_ D)
    (hb : (P.addIso 1 (-1)).hom ≫ P.zeroIso.hom = (s ⊗ₘ n) ≫ e)
    (hp : F.map e ≫ η F = δ F _ _ ≫ (i ⊗ₘ j) ≫ e') :
    (((P.map F).copy T hT).addIso 1 (-1)).hom ≫ (((P.map F).copy T hT).zeroIso).hom =
      ((eqToHom (congrFun hT 1) ≫ F.map s ≫ i) ⊗ₘ
        (eqToHom (congrFun hT (-1)) ≫ F.map n ≫ j)) ≫ e' := by
  subst T
  change (𝟙 _ ≫ (inv (δ F _ _) ≫ F.map (P.addIso 1 (-1)).hom) ≫ 𝟙 _) ≫
      (𝟙 _ ≫ F.map P.zeroIso.hom ≫ η F) =
    ((𝟙 _ ≫ F.map s ≫ i) ⊗ₘ (𝟙 _ ≫ F.map n ≫ j)) ≫ e'
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  erw [← F.map_comp_assoc, hb, F.map_comp, Category.assoc, hp, ← δ_natural_assoc,
    IsIso.inv_hom_id_assoc, tensorHom_comp_tensorHom_assoc]

private theorem singleFamilyPullEvaluation {B : Type v} [Category.{u+1} B] [Abelian B]
    [IsGrothendieckAbelian.{u+1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] {X Y : Scheme.{u}} (π : X ⟶ Y)
    {P : Sheaf Y.smallEtaleTopology B} (e : TensorInverse P)
    (T : ℤ → _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    (hT : T = (pullbackIntTensorFamily B e.singleFunctor.intTensorFamily π).obj) :
    let F := (π)^*[B]
    let D := L((π)^*[B])
    let Q := (pullbackIntTensorFamily B e.singleFunctor.intTensorFamily π).copy T hT
    let m (k : ℤ) := eqToIso (congrFun hT k) ≪≫ D.mapIso (e.zpowSingleFunctorIso k) ≪≫
      (singleFunctorCompLeftDerivedUpperStarIso B π).app _
    have hf : ObjectProperty.flat (e.zpow 1) :=
      ObjectProperty.prop_tensor e.flat (ObjectProperty.flat_of_tensorIso (λ_ _))
    (Q.derivedTensorAddIso 1 (-1)).hom ≫ Q.zeroIso.hom =
      ((m 1).hom ⊗ₘ (m (-1)).hom) ≫
      (singleFunctorObjTensorIso (F.obj (e.zpow 1)) (F.obj (e.zpow (-1)))
        (Functor.PreservesFlat.flat_obj (F := F) hf)).hom ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map
        (μ F _ _ ≫ F.map (e.intTensorFamily.addIso 1 (-1)).hom ≫ η F) ≫
      (singleFunctorObjUnitIso B X).hom := by
  let D := L((π)^*[B])
  let Q := e.singleFunctor.intTensorFamily
  let S := _root_.DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology B) 0
  let γ := (singleFunctorCompLeftDerivedUpperStarIso B π).hom
  let := leftDerivedUpperStarOplaxMonoidal B π
  have := isIso_leftDerivedUpperStarOplaxMonoidal_η B π
  have := isIso_leftDerivedUpperStarOplaxMonoidal_δ B π
  have hf : ObjectProperty.flat (e.zpow 1) :=
    ObjectProperty.prop_tensor e.flat (ObjectProperty.flat_of_tensorIso (λ_ _))
  let ev := onefoldEval e
  have hb := etaleSingle_onefoldEvaluation e
  have hp := pullSinglePair (B := B) π (e.zpow 1) (e.zpow (-1)) hf ev
  have hb' : (Q.addIso 1 (-1)).hom ≫ Q.zeroIso.hom =
      ((e.zpowSingleFunctorIso 1).hom ⊗ₘ (e.zpowSingleFunctorIso (-1)).hom) ≫
      (singleFunctorObjTensorIso _ _ hf).hom ≫ S.map ev ≫ (singleFunctorObjUnitIso _ _).hom :=
    (Category.comp_id _).trans hb
  exact copyPullPair Q D T hT (e.zpowSingleFunctorIso 1).hom (e.zpowSingleFunctorIso (-1)).hom
    (γ.app _) (γ.app _) _ _ hb' hp

/-- The twist multiplication at one and minus one, followed by the zero-twist
identification, is evaluation of the ordinary sheaf powers in their flat single models. -/
theorem etaleTateEvaluation_singleModel (R : Type (u+1)) [CommRing R] [NeZero (ringChar R)]
    (X : Scheme.{u}) [HasInvertibleExponent R X] :
    (HasTateTwist.twistObjectAddIso (Λ := R) X 1 (-1)).hom ≫
        (HasTateTwist.twistObjectZeroIso (Λ := R) X).hom =
      ((tateTwistObjectIsoSingleFunctor R X 1).hom ⊗ₘ
        (tateTwistObjectIsoSingleFunctor R X (-1)).hom) ≫
      (singleFunctorObjTensorIso _ _ (flat_tateTwistSheaf R X 1)).hom ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map (tateTwistSheafEvaluation R X) ≫
      (singleFunctorObjUnitIso (ModuleCat.{u+1} R) X).hom := by
  exact singleFamilyPullEvaluation (B := ModuleCat.{u+1} R) (toInvertibleExponentBase (Λ := R) X)
    (tateSheafTensorInverse R) (tateTwistObject R X) (tateTwistObject_eq R X)

end WeilII
