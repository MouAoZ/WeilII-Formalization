module

import WeilConjectures.Tactic.TransportExact

public import WeilII.AlgebraicGeometry.CondensedWeilPullAction
public import WeilConjectures.WeilSheaf.Native.Projection.AdicSheafTensorSquare
public import WeilConjectures.WeilSheaf.TensorHomAdjunction
import all WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationSheafTensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.MonoidalIso

/-! # Frobenius on the condensed relative tensor of native Weil sheaves -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory AlgebraicGeometry.ProEtale
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII.ExternalProduct

universe u
variable {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}}
  [X.Over (Spec (.of k))]
set_option quotPrecheck false
local notation "Λ" => Profinite.padicAlgClRingObj ℓ
local notation "γ" => (X ↘ Spec (.of k)).geometricGaloisFrobenius.asIso
local notation "E" Z => (adicSheafEquivCondensedMod ℓ Z).functor

local instance (priority := 25000) nativeBraiding (Z : Scheme.{u}) :
    BraidedCategory (Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} ℓ)) :=
  (sheafSymmetricCategory Z).toBraidedCategory
local instance {Z : Scheme.{u}} : IsCommMonObj (adicConstantSheaf ℓ Z) :=
  adicConstantSheaf.isCommMonObj Z

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma tensorMapsOnGenerators {C : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] {R : C} [MonObj R] [IsCommMonObj R]
    [Limits.HasColimitsOfShape Limits.WalkingParallelPair C]
    [Limits.PreservesColimitsOfShape Limits.WalkingParallelPair (MonoidalCategory.tensorLeft R)]
    {A B A' B' : Mod C R} (f : A ⟶ A') (g : B ⟶ B') :
    Mod.tensorπ A B ≫ ((Mod.tensorLeftMap g).app A ≫ (Mod.tensorLeft B').map f).hom =
      (f.hom ⊗ₘ g.hom) ≫ Mod.tensorπ A' B' := by
  rw [Mod.comp_hom', Mod.tensorπ_tensorLeftMap_assoc, Mod.tensorπ_map, tensorHom_def',
    Category.assoc]

private lemma quotientComposite {C D : Type*} [Category* C] [Category* D] (J : C ⥤ D)
    {A B T : C} {P Q : D} (i : A ⟶ B) (v : B ⟶ T) (m : Q ≅ P) (q : P ⟶ J.obj A)
    (p : Q ⟶ J.obj B) (w : Q ⟶ J.obj T) (h : q ≫ J.map i = m.inv ≫ p)
    (k : p ≫ J.map v = w) : m.hom ≫ q ≫ J.map (i ≫ v) = w := by
  rw [J.map_comp, reassoc_of% h, m.hom_inv_id_assoc, k]

private lemma pullTensorGenerators {Z Y : Scheme.{u}} (r : Z ⟶ Y)
    (A B : AdicSheaf ℓ Y) {A' B' : AdicSheaf ℓ Z}
    (f : (adicUpperStar ℓ r).obj A ⟶ A') (g : (adicUpperStar ℓ r).obj B ⟶ B') :
    let F := ProEtale.upperStar (WeilCoefficients.{u} ℓ) r
    μ F A.X B.X ≫ F.map (Mod.tensorπ A B) ≫
        ((adicUpperStarTensorLeftIso ℓ r B).hom.app A ≫
        (Mod.tensorLeftMap g).app ((adicUpperStar ℓ r).obj A) ≫ (Mod.tensorLeft B').map f).hom =
      (f.hom ⊗ₘ g.hom) ≫ Mod.tensorπ A' B' := by
  dsimp only
  exact quotientComposite (Mod.forget _) ((adicUpperStarTensorLeftIso ℓ r B).hom.app A)
    ((Mod.tensorLeftMap g).app _ ≫ (Mod.tensorLeft B').map f)
    (Functor.Monoidal.μIso (ProEtale.upperStar (WeilCoefficients.{u} ℓ) r) A.X B.X)
    ((ProEtale.upperStar (WeilCoefficients.{u} ℓ) r).map (Mod.tensorπ A B))
    (Mod.tensorπ ((adicUpperStar ℓ r).obj A) ((adicUpperStar ℓ r).obj B))
    ((f.hom ⊗ₘ g.hom) ≫ Mod.tensorπ A' B')
    (map_tensorπ_adicUpperStarTensorLeftIso_hom ℓ r A B) (tensorMapsOnGenerators f g)

private lemma cancelTensorGenerators {C : Type*} [Category* C] [MonoidalCategory C]
    (F G : C ⥤ C) [F.LaxMonoidal] [G.LaxMonoidal] (t : F ⟶ G) [NatTrans.IsMonoidal t]
    {A B T : C} (q : A ⊗ B ⟶ T) (a : G.obj A ⟶ A) (b : G.obj B ⟶ B)
    (v : G.obj T ⟶ T) (w : F.obj T ⟶ T) [Epi (μ F A B)] [Epi (F.map q)]
    (hv : (a ⊗ₘ b) ≫ q = μ G A B ≫ G.map q ≫ v)
    (hw : μ F A B ≫ F.map q ≫ w = ((t.app A ≫ a) ⊗ₘ (t.app B ≫ b)) ≫ q) :
    t.app T ≫ v = w := by
  apply (cancel_epi (F.map q)).1
  apply (cancel_epi (μ F A B)).1
  rw [t.naturality_assoc, NatTrans.IsMonoidal.tensor_assoc, ← hv, hw,
    ← tensorHom_comp_tensorHom_assoc]

private lemma action_hom (P : ProEtaleWeilSheaf k ℓ X) :
    (nativePullAction P).hom =
      (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} ℓ) γ).hom.app P.carrier.X ≫
        P.str.hom.hom := by
  unfold nativePullAction
  rw [Mod.comp_hom', adicUpperStarIsoLowerStarInv_hom_app_hom]

private lemma nativeTensorAction (P M : ProEtaleWeilSheaf k ℓ X) :
    let V := adicUpperStar ℓ (γ).hom
    nativePullAction (ProEtaleWeilSheaf.tensor k ℓ X M P) =
      (adicUpperStarTensorLeftIso ℓ (γ).hom M.carrier).hom.app P.carrier ≫
        (Mod.tensorLeftMap (nativePullAction M)).app (V.obj P.carrier) ≫
        (Mod.tensorLeft M.carrier).map (nativePullAction P) := by
  intro V
  let U := ProEtale.upperStar (WeilCoefficients.{u} ℓ) (γ).hom
  let R := ProEtale.lowerStar (WeilCoefficients.{u} ℓ) (γ).inv
  let t := ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} ℓ) γ
  let π := Mod.tensorπ P.carrier M.carrier
  let j := ((Mod.relativeTensorRightIso M.carrier).app P.carrier).hom
  have : IsIso j.hom := inferInstanceAs (IsIso ((Mod.forget _).map j))
  have : Epi (π ≫ j.hom) := by
    rw [show π ≫ j.hom = Mod.tensorObjπ P.carrier M.carrier from
      ProEtaleWeilSheaf.tensorπ_relativeTensorRightIso_hom_app _ _]
    infer_instance
  have : Epi π := (epi_comp_iff_of_isIso π j.hom).1 inferInstance
  let z := (adicUpperStarTensorLeftIso ℓ (γ).hom M.carrier).hom.app P.carrier ≫
    (Mod.tensorLeftMap (nativePullAction M)).app (V.obj P.carrier) ≫
    (Mod.tensorLeft M.carrier).map (nativePullAction P)
  have gen := pullTensorGenerators (γ).hom P.carrier M.carrier (nativePullAction P)
    (nativePullAction M)
  rw [action_hom P, action_hom M] at gen
  apply Mod.hom_ext
  rw [action_hom]
  exact cancelTensorGenerators U R t.hom π P.str.hom.hom M.str.hom.hom
    (ProEtaleWeilSheaf.tensor k ℓ X M P).str.hom.hom z.hom
    (ProEtaleWeilSheaf.tensorπ_str P M) gen

private lemma compareTensorMap {C D : Type*} [Category* C] [Category* D] (J : C ⥤ D)
    {A B A' B' : C} {S S' : D} (r : A ≅ B) (r' : A' ≅ B')
    (v : S ≅ J.obj B) (v' : S' ≅ J.obj B') (a : A ⟶ A') (b : B ⟶ B') (s : S ⟶ S')
    (h : a ≫ r'.hom = r.hom ≫ b) (k : s ≫ v'.hom = v.hom ≫ J.map b) :
    (J.mapIso r ≪≫ v.symm).inv ≫ J.map a = s ≫ (J.mapIso r' ≪≫ v'.symm).inv := by
  have hr : r.inv ≫ a = b ≫ r'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, r'.hom_inv_id, Category.comp_id]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
  rw [← J.map_comp, hr, J.map_comp, reassoc_of% k]

private lemma relativeTensorNaturality {Z : Scheme.{u}} {A B A' B' : AdicSheaf ℓ Z}
    (f : A ⟶ A') (g : B ⟶ B') :
    (condensedRelativeTensorIso ℓ Z A B).inv ≫
        (E Z).map ((Mod.tensorLeftMap g).app A ≫ (Mod.tensorLeft B').map f) =
      ((E Z).map f ⊗ₘ (E Z).map g) ≫ (condensedRelativeTensorIso ℓ Z A' B').inv := by
  exact compareTensorMap (E Z) ((Mod.relativeTensorRightIso B).app A)
    ((Mod.relativeTensorRightIso B').app A') (adicSheafEquivCondensedModTensorIso ℓ Z A B)
    (adicSheafEquivCondensedModTensorIso ℓ Z A' B')
    ((Mod.tensorLeftMap g).app A ≫ (Mod.tensorLeft B').map f) (f ⊗ₘ g)
    ((E Z).map f ⊗ₘ (E Z).map g)
    ((Category.assoc _ _ _).trans (ProEtaleWeilSheaf.relativeTensorRightIso_hom_natural f g))
    (adicSheafEquivCondensedModTensorIso_hom_natural ℓ Z f g)

private lemma pasteTensorActions {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    (J : C ⥤ D) (F : D ⥤ D) [F.OplaxMonoidal] {A B T A' B' T' K : C}
    (i : J.obj A ⊗ J.obj B ⟶ J.obj T) (j : J.obj A' ⊗ J.obj B' ⟶ J.obj K)
    (a : F.obj (J.obj A) ⟶ J.obj A') (b : F.obj (J.obj B) ⟶ J.obj B')
    (c : F.obj (J.obj T) ⟶ J.obj T') (r : T' ⟶ K) (m : K ⟶ T)
    (p : A' ⟶ A) (q : B' ⟶ B) (v : T' ⟶ T)
    (s : F.obj (J.obj T) ⟶ J.obj T) (x : F.obj (J.obj A) ⟶ J.obj A)
    (y : F.obj (J.obj B) ⟶ J.obj B)
    (hc : F.map i ≫ c ≫ J.map r = δ F _ _ ≫ (a ⊗ₘ b) ≫ j)
    (hn : j ≫ J.map m = (J.map p ⊗ₘ J.map q) ≫ i)
    (hv : v = r ≫ m) (hs : s = c ≫ J.map v)
    (hx : x = a ≫ J.map p) (hy : y = b ≫ J.map q) :
    F.map i ≫ s = δ F _ _ ≫ (x ⊗ₘ y) ≫ i := by
  rw [hs, hv, J.map_comp, reassoc_of% hc, hn, hx, hy, tensorHom_comp_tensorHom_assoc]

/-- The pullback action on a relative tensor agrees with the tensor of the two ordinary
condensed Weil actions. -/
theorem condensedRelativeTensorWeilSquare (P M : ProEtaleWeilSheaf k ℓ X) :
    let U := CondensedRing.upperStar Λ (γ).hom
    let T := ProEtaleWeilSheaf.tensor k ℓ X M P
    let i := (condensedRelativeTensorIso ℓ _ P.carrier M.carrier).inv
    let W := ProEtaleWeilSheaf.toCondensedUpperStar k ℓ X
    U.map i ≫ (W.obj T).str.hom =
      δ U (W.obj P).carrier (W.obj M).carrier ≫
        ((W.obj P).str.hom ⊗ₘ (W.obj M).str.hom) ≫ i := by
  dsimp only
  fo_apply (pasteTensorActions (E ((X ↘ Spec (.of k)).geometricFiber))
    (CondensedRing.upperStar Λ (γ).hom)) using
      (condensedRelativeTensorIso ℓ _ P.carrier M.carrier).inv,
      (condensedRelativeTensorIso ℓ _ ((adicUpperStar ℓ (γ).hom).obj P.carrier)
        ((adicUpperStar ℓ (γ).hom).obj M.carrier)).inv,
      (adicUpperStarCompCondensedModIso ℓ (γ).hom).inv.app P.carrier,
      (adicUpperStarCompCondensedModIso ℓ (γ).hom).inv.app M.carrier,
      (adicUpperStarCompCondensedModIso ℓ (γ).hom).inv.app ((Mod.tensorLeft M.carrier).obj P.carrier),
      (adicUpperStarTensorLeftIso ℓ (γ).hom M.carrier).hom.app P.carrier,
      ((Mod.tensorLeftMap (nativePullAction M)).app ((adicUpperStar ℓ (γ).hom).obj P.carrier) ≫
        (Mod.tensorLeft M.carrier).map (nativePullAction P)), nativePullAction P, nativePullAction M,
      nativePullAction (ProEtaleWeilSheaf.tensor k ℓ X M P),
      ((ProEtaleWeilSheaf.toCondensedUpperStar k ℓ X).obj (ProEtaleWeilSheaf.tensor k ℓ X M P)).str.hom,
      ((ProEtaleWeilSheaf.toCondensedUpperStar k ℓ X).obj P).str.hom,
      ((ProEtaleWeilSheaf.toCondensedUpperStar k ℓ X).obj M).str.hom,
      fo_late (adicUpperStar_condensedRelativeTensor_square ℓ (γ).hom P.carrier M.carrier),
      fo_late (relativeTensorNaturality (nativePullAction P) (nativePullAction M)),
      fo_late (nativeTensorAction P M),
      fo_late (changeFrobeniusModel (ProEtaleWeilSheaf.tensor k ℓ X M P)),
      fo_late (changeFrobeniusModel P), fo_late (changeFrobeniusModel M)

end WeilII.ExternalProduct
