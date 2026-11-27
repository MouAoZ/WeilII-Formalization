module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.OpenImmersionBaseChange
public import WeilII.AlgebraicGeometry.DerivedOpenExtensionExchangeUnit
import WeilII.AlgebraicGeometry.SliceOpenExtensionUnitEquation

/-! # The inverse open exchange on bounded constructible complexes -/

public noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

private theorem unit_of_left_mate {A B A' B' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    {J : A ⥤ B} {R : B ⥤ A} {J' : A' ⥤ B'} {R' : B' ⥤ A'}
    {W : A ⥤ A'} {V : B ⥤ B'} (a : J ⊣ R) (b : J' ⊣ R') (θ : R ⋙ W ≅ V ⋙ R')
    (β : W ⋙ J' ⟶ J ⋙ V) (hβ : β = Adjunction.exchangeLeft a b θ) (K : A) :
    b.unit.app (W.obj K) ≫ R'.map (β.app K) = W.map (a.unit.app K) ≫ θ.hom.app (J.obj K) := by
  subst β
  exact Adjunction.unit_app_comp_map_exchangeLeft_app a b θ K

private theorem openMate_eq_of_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] {X Y X' Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {j : X ⟶ Y} {j' : X' ⟶ Y'} {v : Y' ⟶ Y} {w : X' ⟶ X}
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left] (sq : IsPullback w j' j v)
    (K : Dᵇc(X.left)⟦Λ⟧)
    (m : (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j').obj
          ((boundedConstructibleUpperStar Λ ℓ w).obj K) ⟶
        (boundedConstructibleUpperStar Λ ℓ v).obj ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K))
    (hm :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').unit.app
        ((boundedConstructibleUpperStar Λ ℓ w).obj K) ≫ (boundedConstructibleUpperStar Λ ℓ j').map m =
      (boundedConstructibleUpperStar Λ ℓ w).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit.app K) ≫
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq.toCommSq.flip).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K)) :
    (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).inv.app K = m := by
  let a := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j
  let b := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j'
  let θ := boundedConstructiblePullbackSquareComparison Λ ℓ sq.toCommSq.flip
  have h := unit_of_left_mate a b θ _
    (boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft Λ ℓ sq.toCommSq) K
  apply (b.homEquiv _ _).injective
  exact h.trans hm.symm

/-- The inverse of bounded open base change projects to the inverse levelwise exchange
conjugated by the horizontal pullback comparisons. The ambient exchange satisfies the
unit equation. Restrict that identity and use the unit characterization of the left mate. -/
theorem boundedOpenExchange_inv_app_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] {X Y X' Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {j : X ⟶ Y} {j' : X' ⟶ Y'} {v : Y' ⟶ Y} {w : X' ⟶ X}
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left] (sq : IsPullback w j' j v)
    (K : Dᵇc(X.left)⟦Λ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).inv.app K).hom =
      D((j'.left)_!open⟦Λ⟧).map ((leftDerivedUpperStarIsoMapDerivedCategory Λ w.left).hom.app K.obj) ≫
        (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ sq.overLeft.flip).inv.app K.obj ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ v.left).inv.app
          (D((j.left)_!open⟦Λ⟧).obj K.obj) := by
  have hr := derivedOpenExtensionExchangeUnit Λ sq.overLeft K.obj
  have H := openMate_eq_of_unit Λ ℓ sq K _
    (sliceOpenExtensionUnitEquation Λ ℓ sq K (ObjectProperty.homMk _) hr)
  exact congrArg (fun m ↦ m.hom) H

end WeilII
