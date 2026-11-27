module

public import WeilII.AlgebraicGeometry.SemilinearCompactificationExchange
import WeilII.AlgebraicGeometry.ShriekSliceFieldExchange
meta import WeilConjectures.Tactic.FirstOrderApply

/-! # Computing the chosen shriek exchange on a semilinear cartesian compactification -/

public section

open AlgebraicGeometry CategoryTheory Limits AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

set_option maxRecDepth 4096

namespace WeilII

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

local notation "Λ" => Profinite.padicAlgClRingObj ℓ

private theorem dropMapId {A B : Type*} [Category A] [Category B] {P : ObjectProperty B}
    (F : A ⥤ P.FullSubcategory) (K : A) {Z : B} (m : (F.obj K).obj ⟶ Z) :
    (F.map (𝟙 K)).hom ≫ m = m := by rw [F.map_id]; exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- The chosen exchange uses the pullback of the Nagata compactification. On underlying
complexes its final factor compares that pullback with the chosen compactification. -/
private theorem chosenExchange_component
    {x : X.left ⟶ X.left} {y : Y.left ⟶ Y.left} [WeaklyEtale y]
    (d : Compactification f.left) (r : d.Z ⟶ (compactificationOverField f).Z)
    [WeaklyEtale r] (hi : IsPullback d.i x r (compactificationOverField f).i)
    (hg : IsPullback r d.g (compactificationOverField f).g y) (K : Dᵇc(X.left)⟦Λ⟧) :
    let a := compactificationOverField f
    let Q := (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) x).obj K
    ((purityFieldLowerShriekExchange ℓ f f a d hi hg).hom.app K).hom =
      (purityFieldCompactificationAmbientExchange ℓ f f a d hi hg).hom.app K.obj ≫
      (ambientCompactificationComparison ℓ (f := f) d a Q).hom := by
  dsimp only
  rw [fieldShriekExchange_app, boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_refl]
  simp only [Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.comp_hom]
  rw [fieldCompactificationExchange_component, ambientCompactificationComparison_hom]
  apply dropMapId (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y) y)

private theorem composeChosen {C : Type*} [Category C] {P Q R S : C}
    {a : P ⟶ S} {b : P ⟶ Q} {c : Q ⟶ S} {j : Q ⟶ R} {k : R ⟶ S} {e : P ⟶ R}
    (square : a = b ≫ c) (cocycle : j ≫ k = c) (exchange : e = b ≫ j) :
    a = e ≫ k := by rw [square, exchange, Category.assoc, cocycle]

/-- Compute the chosen-to-specified comparison with an arbitrary cartesian
representative for the pullback of the Nagata compactification. -/
private theorem semilinearCartesianSource (e : Spec (.of k) ≅ Spec (.of k))
    (x : X.left ⟶ X.left) (y : Y.left ⟶ Y.left) [WeaklyEtale y]
    (wx : x ≫ X.hom ≫ e.hom = X.hom) (wy : y ≫ Y.hom ≫ e.hom = Y.hom)
    (sq : IsPullback x f.left f.left y)
    (d : Compactification f.left) (z : d.Z ⟶ (compactificationOverField f).Z) [WeaklyEtale z]
    (ai : IsPullback d.i x z (compactificationOverField f).i)
    (ap : IsPullback z d.g (compactificationOverField f).g y) (c : Compactification f.left)
    (r : c.Z ⟶ c.Z) [WeaklyEtale r] (hi : IsPullback c.i x r c.i)
    (hg : IsPullback r c.g c.g y) (K : Dᵇc(X.left)⟦Λ⟧) :
    let a := compactificationOverField f
    let J := ambientCompactificationComparison ℓ (f := f) a c
    L((y)^*⟦Λ⟧).map (J K).hom ≫
        (purityFieldCompactificationAmbientExchange ℓ f f c c hi hg).hom.app K.obj =
      ((purityFieldLowerShriekExchange ℓ f f a d ai ap).hom.app K).hom ≫
        (J ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) x).obj K)).hom := by
  dsimp only
  have square := semilinearCompactificationExchange ℓ (f := f) e x y wx wy sq
    (compactificationOverField f) c d c z r ai ap hi hg K
  have cocycle := ambientCompactificationComparison_trans ℓ (f := f) d (compactificationOverField f) c
    ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) x).obj K)
  have exchange := chosenExchange_component ℓ f d z ai ap K
  dsimp only at exchange
  fo_apply composeChosen using square, cocycle, exchange

/-- Test a property of the chosen base-change isomorphism on its defining cartesian pair. -/
private theorem chosenBaseChange_of_cartesian {x : X.left ⟶ X.left} {y : Y.left ⟶ Y.left}
    [WeaklyEtale y] (sq : IsPullback x f.left f.left y)
    (P : (boundedConstructibleLowerShriek ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y) y ≅
        boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) x ⋙ boundedConstructibleLowerShriek ℓ f) → Prop)
    (h : ∀ (d : Compactification f.left) (z : d.Z ⟶ (compactificationOverField f).Z) [WeaklyEtale z]
      (ai : IsPullback d.i x z (compactificationOverField f).i)
      (ap : IsPullback z d.g (compactificationOverField f).g y),
      P (purityFieldLowerShriekExchange ℓ f f (compactificationOverField f) d ai ap)) :
    P (purityFieldLowerShriekBaseChange ℓ f f sq) := by
  let a := compactificationOverField f
  have hz : WeaklyEtale (pullback.fst a.g y) :=
    MorphismProperty.of_isPullback (a.isPullback_g_ofIsPullback sq) ‹WeaklyEtale y›
  exact @h (a.ofIsPullback sq) (pullback.fst a.g y) hz
    (a.isPullback_i_ofIsPullback sq).flip (a.isPullback_g_ofIsPullback sq).flip

/-- Compute the chosen exchange on a specified compactification with a semilinear
cartesian action. The cocycle for the ambient comparisons removes the pullback
of the chosen Nagata compactification from the resulting formula. -/
theorem semilinearChosenCompactification (e : Spec (.of k) ≅ Spec (.of k))
    (x : X.left ⟶ X.left) (y : Y.left ⟶ Y.left) [WeaklyEtale y]
    (wx : x ≫ X.hom ≫ e.hom = X.hom) (wy : y ≫ Y.hom ≫ e.hom = Y.hom)
    (sq : IsPullback x f.left f.left y) (c : Compactification f.left)
    (r : c.Z ⟶ c.Z) [WeaklyEtale r] (hi : IsPullback c.i x r c.i)
    (hg : IsPullback r c.g c.g y) (K : Dᵇc(X.left)⟦Λ⟧) :
    let a := compactificationOverField f
    let J := ambientCompactificationComparison ℓ (f := f) a c
    L((y)^*⟦Λ⟧).map (J K).hom ≫
        (purityFieldCompactificationAmbientExchange ℓ f f c c hi hg).hom.app K.obj =
      ((purityFieldLowerShriekBaseChange ℓ f f sq).hom.app K).hom ≫
        (J ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) x).obj K)).hom := by
  intro a J
  refine chosenBaseChange_of_cartesian ℓ f sq (fun E ↦
    L((y)^*⟦Λ⟧).map (J K).hom ≫
        (purityFieldCompactificationAmbientExchange ℓ f f c c hi hg).hom.app K.obj =
      (E.hom.app K).hom ≫ (J ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) x).obj K)).hom) ?_
  intro d z _ ai ap
  exact semilinearCartesianSource ℓ f e x y wx wy sq d z ai ap c r hi hg K

end WeilII
