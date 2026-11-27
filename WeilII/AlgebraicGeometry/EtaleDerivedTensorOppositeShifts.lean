module

public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import all WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation

/-! # Opposite shifts for a derived monoidal functor on étale sheaves -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

attribute [local instance] Functor.postcompose_left_commShift Functor.postcompose_right_commShift
  Functor.precompose_left_commShift Functor.precompose_right_commShift
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  Functor.mapDerivedCategory Functor.mapHomotopyCategory _root_.DerivedCategory.Qh

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilII

private theorem comparison_opposite {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ i : ℤ, (shiftFunctor C i).Additive] [∀ i : ℤ, (shiftFunctor D i).Additive]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) [T.CommShift₂Int] [S.CommShift₂Int]
    (F : C ⥤ D) [F.CommShift ℤ]
    (i : ℤ) (τ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S)
    (left : ∀ K, NatTrans.CommShift (τ.app K) ℤ)
    (right : ∀ M, NatTrans.CommShift (τ.flipApp M) ℤ)
    (δ : ∀ K M, F.obj ((T.obj K).obj M) ⟶ (S.obj (F.obj K)).obj (F.obj M))
    (hδ : ∀ K M, (τ.app K).app M = δ K M)
    (a : ∀ K M, (T.obj (K⟦(-i)⟧)).obj (M⟦i⟧) ⟶ (T.obj K).obj M)
    (b : ∀ K M, (S.obj (K⟦(-i)⟧)).obj (M⟦i⟧) ⟶ (S.obj K).obj M)
    (ha : ∀ K M, Functor.cancelTensor T K M i = a K M)
    (hb : ∀ K M, Functor.cancelTensor S K M i = b K M)
    (K M : C) :
    F.map (a K M) ≫ δ K M = δ _ _ ≫
      ((S.map ((F.commShiftIso (-i)).hom.app K)).app (F.obj (M⟦i⟧)) ≫
       (S.obj ((F.obj K)⟦(-i)⟧)).map ((F.commShiftIso i).hom.app M)) ≫
        b (F.obj K) (F.obj M) := by
  have h := (Functor.comparison_cancellation T S F τ left right K M i).symm
  change F.map (Functor.cancelTensor T K M i) ≫ (τ.app K).app M =
    (τ.app _).app _ ≫ (S.map _).app _ ≫ (S.obj _).map _ ≫ Functor.cancelTensor S _ _ i at h
  simpa only [hδ, ha, hb, Category.assoc] using h

section
variable {C D : Type*} [Category.{u+1} C] [Category.{u+1} D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{u+1} C] [IsGrothendieckAbelian.{u+1} D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (E : C ⥤ D) [E.Additive] [E.PreservesKFlatQuasiIso] [E.PreservesFlat]
  [E.IsLeftAdjoint] [E.Monoidal] [E.leftDerivedFunctor.CommShift ℤ]
  [NatTrans.CommShift E.leftDerivedFunctorCounit ℤ]

private theorem leftComparison (P : _root_.DerivedCategory C) :
    NatTrans.CommShift (E.leftDerivedTensorComparison.app P) ℤ :=
  Functor.nativeLeft_commShift E P

private theorem rightComparison (P : _root_.DerivedCategory C) :
    NatTrans.CommShift (E.leftDerivedTensorComparison.flipApp P) ℤ :=
  Functor.nativeRight_commShift E P

end

private theorem cancelTensor_eq (C : Type*) [Category.{u+1} C] [Abelian C]
    [IsGrothendieckAbelian.{u+1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    {X : Scheme.{u}} (P N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    letI : (derivedTensor C X).CommShift₂Int := _root_.DerivedCategory.commShift₂CurriedTensor _
    Functor.cancelTensor (derivedTensor C X) P N (-2) =
      (derivedTensorShiftIso C P N (2 : ℤ) (-2)).hom ≫
        (shiftFunctorZero' _ ((2 : ℤ) + -2) (by decide)).hom.app _ := by
  simp only [Functor.cancelTensor, derivedTensorShiftIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, shiftFunctorCompIsoId, NatTrans.comp_app,
    shiftFunctorZero', eqToIso_refl, Iso.refl_trans, Category.assoc]
  rfl

section
variable (C D : Type*) [Category.{u+1} C] [Abelian C] [IsGrothendieckAbelian.{u+1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [Category.{u+1} D] [Abelian D]
  [IsGrothendieckAbelian.{u+1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  {X : Scheme.{u}}
local notation "DC(" A ")" => _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)
noncomputable local instance : (derivedTensor C X).CommShift₂Int := _root_.DerivedCategory.commShift₂CurriedTensor _

private theorem sheafComparison (F : DC(C) ⥤ DC(D)) [F.CommShift ℤ]
    (τ : (Functor.postcompose₂.obj F).obj (derivedTensor C X) ⟶
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (derivedTensor D X))
    (left : ∀ K, NatTrans.CommShift (τ.app K) ℤ)
    (right : ∀ M, NatTrans.CommShift (τ.flipApp M) ℤ)
    (δ : ∀ K M, F.obj (((derivedTensor C X).obj K).obj M) ⟶
      ((derivedTensor D X).obj (F.obj K)).obj (F.obj M))
    (hδ : ∀ K M, (τ.app K).app M = δ K M) (K M : DC(C)) :
    F.map ((derivedTensorShiftIso C K M (2 : ℤ) (-2)).hom ≫
      (shiftFunctorZero' _ ((2 : ℤ) + -2) (by decide)).hom.app _) ≫ δ K M =
      δ _ _ ≫ derivedTensorHom D ((F.commShiftIso (2 : ℤ)).hom.app K)
        ((F.commShiftIso (-2 : ℤ)).hom.app M) ≫
        (derivedTensorShiftIso D (F.obj K) (F.obj M) (2 : ℤ) (-2)).hom ≫
          (shiftFunctorZero' _ ((2 : ℤ) + -2) (by decide)).hom.app _ := by
  exact comparison_opposite (derivedTensor C X) (derivedTensor D X) F (-2) τ left right δ hδ
    _ _ (cancelTensor_eq C) (cancelTensor_eq D) K M

/-- A monoidal left adjoint on étale sheaves whose right adjoint is exact and which
preserves flats and K-flat quasi-isomorphisms has a derived tensor comparison
compatible with the cancellation of shifts 2 and −2. The shift on the derived
functor is the one induced by the adjunction to termwise restriction. -/
theorem etaleLeftDerivedTensor_oppositeShifts (E : Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology D)
    (U : Sheaf X.smallEtaleTopology D ⥤ Sheaf X.smallEtaleTopology C)
    [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso] [E.PreservesFlat]
    [E.IsLeftAdjoint] [E.Monoidal] [Limits.PreservesFiniteLimits U]
    [Limits.PreservesFiniteColimits U] (ad : E ⊣ U)
    (K M : DC(C)) :
    let F := E.leftDerivedFunctor
    let := (ad.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
    let δ (K M : DC(C)) := (E.leftDerivedTensorComparison.app K).app M
    F.map ((derivedTensorShiftIso C K M (2 : ℤ) (-2)).hom ≫
      (shiftFunctorZero' _ ((2 : ℤ) + -2) (by decide)).hom.app _) ≫ δ K M =
      δ _ _ ≫ derivedTensorHom D ((F.commShiftIso (2 : ℤ)).hom.app K)
        ((F.commShiftIso (-2 : ℤ)).hom.app M) ≫
        (derivedTensorShiftIso D (F.obj K) (F.obj M) (2 : ℤ) (-2)).hom ≫
          (shiftFunctorZero' _ ((2 : ℤ) + -2) (by decide)).hom.app _ := by
  let := (ad.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory).leftAdjointCommShift ℤ
  have := Functor.derived_counit_commShift E U ad
  exact sheafComparison C D E.leftDerivedFunctor E.leftDerivedTensorComparison
    (leftComparison E) (rightComparison E) _ (fun _ _ ↦ rfl) K M

end

end WeilII
