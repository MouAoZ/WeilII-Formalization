module

public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleSheafPowers
import WeilII.AlgebraicGeometry.TensorInverseOnefoldEvaluation
import all WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorNaturality
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-! # Evaluation of inverse sheaves placed in degree zero -/

@[expose] public section
universe u v
open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Etale
open Functor.LaxMonoidal
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 90000
set_option Elab.async false

namespace WeilII

variable {B : Type v} [Category.{u+1} B] [Abelian B] [IsGrothendieckAbelian.{u+1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B] {X : Scheme.{u}}

private theorem unitorTransport {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (S G : C ⥤ D) [G.LaxMonoidal] (e : S ≅ G)
    (L : C) (u : 𝟙_ D ⟶ S.obj (𝟙_ C)) (m : S.obj L ⊗ S.obj (𝟙_ C) ⟶ S.obj (L ⊗ 𝟙_ C))
    (hu : ε G ≫ e.inv.app _ = u)
    (hm : (e.hom.app L ⊗ₘ e.hom.app _) ≫ μ G L (𝟙_ C) ≫ e.inv.app _ = m) :
    (S.obj L ◁ u ≫ m) ≫ S.map (ρ_ L).hom = (ρ_ (S.obj L)).hom := by
  let : S.LaxMonoidal := Functor.LaxMonoidal.transport e.symm
  have h := right_unitality S L
  rw [Functor.LaxMonoidal.transport_μ e.symm, Functor.LaxMonoidal.transport_ε e.symm] at h
  simpa only [Category.assoc, ← hm, ← hu, Iso.symm_hom, Iso.symm_inv] using h.symm

private theorem single_onefold_unitor (P : Sheaf X.smallEtaleTopology B)
    (hP : ObjectProperty.flat P) :
    (TensorInverse.tensorPowNatSingleFunctorIso P hP 1).hom ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map (ρ_ P).hom =
      (ρ_ ((_root_.DerivedCategory.singleFunctor _ 0).obj P)).hom := by
  let C := Sheaf X.smallEtaleTopology B
  let S := _root_.DerivedCategory.singleFunctor C 0
  let s := HomologicalComplex.single C (.up ℤ) 0
  let q := HomotopyCategory.quotient C (.up ℤ)
  let F := q ⋙ _root_.DerivedCategory.Qh
  let e : S ≅ s ⋙ F := _root_.DerivedCategory.singleFunctorIsoCompQ C 0 ≪≫
    Functor.isoWhiskerLeft s (_root_.DerivedCategory.quotientCompQhIso C).symm
  let : s.Monoidal := cochainSingleMonoidal
  have eH (T : C) : e.hom.app T = (singleFunctorObjIsoQh T).hom := rfl
  have eI (T : C) : e.inv.app T = (singleFunctorObjIsoQh T).inv := rfl
  apply unitorTransport S (s ⋙ F) e P (singleFunctorObjUnitIso B X).inv
    (singleFunctorObjTensorIso P _ hP).hom
  · change (ε F ≫ F.map (ε s)) ≫ e.inv.app _ = _
    have hs : ε s = 𝟙 _ := rfl
    rw [hs, F.map_id, Category.comp_id, eI]
    simp only [singleFunctorObjUnitIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Functor.Monoidal.εIso_hom, asIso_hom, F, comp_ε, Category.assoc]
    rfl
  · rw [singleFunctorObjTensorIso_factorization, comp_μ s F, Category.assoc (μ F _ _),
      eH, eH, eI]
    rfl

private theorem singleEval_paste {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (S : C ⥤ D) {L M K N : C}
    {P Q I : D} (x : P ⟶ S.obj L) (y : Q ⟶ S.obj M) (a : L ⟶ K) (b : M ⟶ N)
    (p : P ⟶ S.obj K) (q : Q ⟶ S.obj N) (r : K ⊗ N ⟶ 𝟙_ C) (u : S.obj (𝟙_ C) ⟶ I)
    (l : S.obj L ⊗ S.obj M ⟶ S.obj (L ⊗ M)) (k : S.obj K ⊗ S.obj N ⟶ S.obj (K ⊗ N))
    (hx : x ≫ S.map a = p) (hy : y ≫ S.map b = q)
    (hn : (S.map a ⊗ₘ S.map b) ≫ k = l ≫ S.map (a ⊗ₘ b)) :
    (p ⊗ₘ q) ≫ k ≫ S.map r ≫ u =
      (x ⊗ₘ y) ≫ l ≫ S.map ((a ⊗ₘ b) ≫ r) ≫ u := by
  rw [S.map_comp, Category.assoc (S.map _), ← reassoc_of% hn,
    tensorHom_comp_tensorHom_assoc, hx, hy]

/-- Placing inverse sheaves in degree zero takes their onefold evaluation to the
derived evaluation through the two canonical power comparisons and the flat tensorator. -/
theorem etaleSingle_onefoldEvaluation {P : Sheaf X.smallEtaleTopology B}
    (e : TensorInverse P) :
    (e.singleFunctor.intTensorFamily.addIso 1 (-1)).hom =
      ((e.zpowSingleFunctorIso 1).hom ⊗ₘ (e.zpowSingleFunctorIso (-1)).hom) ≫
        (singleFunctorObjTensorIso (e.zpow 1) (e.zpow (-1))
          (ObjectProperty.prop_tensor e.flat (ObjectProperty.flat_of_tensorIso (λ_ _)))).hom ≫
        (_root_.DerivedCategory.singleFunctor _ 0).map (e.intTensorFamily.addIso 1 (-1)).hom ≫
        (singleFunctorObjUnitIso B X).hom := by
  let S := _root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology B) 0
  have hp := single_onefold_unitor P e.flat
  have hn := single_onefold_unitor e.obj e.flat_obj
  have hnat := singleFunctorObjTensorIso_hom_naturality (ρ_ P).hom (ρ_ e.obj).hom
    (ObjectProperty.prop_tensor e.flat (ObjectProperty.flat_of_tensorIso (λ_ _))) e.flat
  rw [tensorInverse_onefoldEvaluation e.singleFunctor, tensorInverse_onefoldEvaluation e]
  exact singleEval_paste S _ _ _ _ _ _ e.rightIso.hom _ _ _ hp hn hnat

end WeilII
