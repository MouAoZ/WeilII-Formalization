module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.OpenImmersionBaseChange
public import WeilII.AlgebraicGeometry.DerivedOpenExtensionUnitEquation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperAmbient
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents

/-! # Restriction of the open-extension unit equation in a field slice -/

public noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

private theorem appHEq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (t : F ⟶ G) {X Y : C} (h : X = Y) : HEq (t.app X) (t.app Y) := by
  cases h
  rfl

private theorem mapHEq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'} (hx : X = X') (hy : Y = Y') (h : HEq f f') :
    HEq (F.map f) (F.map f') := by
  subst X' Y'
  cases h
  rfl

private theorem isoAppHEq {C D : Type*} [Category C] [Category D]
    {F G F' G' : C ⥤ D} (a : F ≅ G) (b : F' ≅ G') {X Y : C}
    (hF : F = F') (hG : G = G') (he : HEq a b) (hX : X = Y) :
    HEq (a.hom.app X) (b.hom.app Y) := by
  subst F' G' Y
  cases he
  rfl

private theorem homHEq {D : Type*} [Category D] {P : ObjectProperty D}
    {A B A' B' : P.FullSubcategory} (f : A ⟶ B) (g : A' ⟶ B')
    (hA : A = A') (hB : B = B') (h : HEq f g) : HEq f.hom g.hom := by
  subst A' B'
  cases h
  rfl

/-- For a cartesian square in a field slice, a bounded comparison satisfying the ambient
unit equation satisfies the unit equation for the bounded adjunctions. Project the two
composites to the underlying category. The bounded units, pullbacks and square comparison
have exactly the ambient components. Faithfulness of inclusion gives the equality. -/
theorem sliceOpenExtensionUnitEquation
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
        (boundedConstructibleUpperStar Λ ℓ v).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K))
    (hm : DerivedOpenExtensionUnitEquation Λ sq.overLeft.toCommSq K.obj m.hom) :
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').unit.app
        ((boundedConstructibleUpperStar Λ ℓ w).obj K) ≫ (boundedConstructibleUpperStar Λ ℓ j').map m =
      (boundedConstructibleUpperStar Λ ℓ w).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit.app K) ≫
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq.toCommSq.flip).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K) := by
  have comp_heq {D : Type _} [Category.{_} D] {X Y Z X' Y' Z' : D}
      {u : X ⟶ Y} {v : Y ⟶ Z} {u' : X' ⟶ Y'} {v' : Y' ⟶ Z'} (hx : X = X') (hy : Y = Y')
      (hz : Z = Z') (hu : HEq u u') (hv : HEq v v') : HEq (u ≫ v) (u' ≫ v') := by
    subst X' Y' Z'
    cases hu
    cases hv
    rfl
  have assemble {C : Type _} [Category.{_} C] {X' Y' Z' W' : C}
      {a' : X' ⟶ Y'} {b' : Y' ⟶ W'} {c' : X' ⟶ Z'} {d' : Z' ⟶ W'}
      (h : a' ≫ b' = c' ≫ d') {P : ObjectProperty C} {X Y Z W : P.FullSubcategory}
      (a : X ⟶ Y) (b : Y ⟶ W) (c : X ⟶ Z) (d : Z ⟶ W) (hx : X.obj = X') (hy : Y.obj = Y')
      (hz : Z.obj = Z') (hw : W.obj = W') (ha : HEq a.hom a') (hb : HEq b.hom b')
      (hc : HEq c.hom c') (hd : HEq d.hom d') : a ≫ b = c ≫ d := by
    apply ObjectProperty.hom_ext
    exact eq_of_heq ((comp_heq hx hy hw ha hb).trans (h ▸ (comp_heq hx hz hw hc hd).symm))
  let B := (boundedConstructibleUpperStar Λ ℓ w).obj K
  let E := (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K
  let A := boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j
  dsimp only [DerivedOpenExtensionUnitEquation] at hm
  -- Compare each edge with its own endpoints before composing in the full subcategory.
  have transfer := @assemble _ _ _ _ _ _ _ _ _ _ hm
  apply transfer (P := boundedConstructible (condensedRingObj Λ X'.left))
  · rfl
  · rfl
  · rfl
  · rfl
  · refine (heq_of_eq (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit_app_hom Λ ℓ j' B)).trans ?_
    apply appHEq
    exact boundedConstructibleUpperStar_obj_obj Λ ℓ w K
  · refine (heq_of_eq (boundedConstructibleUpperStar_map_hom Λ ℓ j' m)).trans ?_
    apply mapHEq _ rfl rfl
    rfl
  · refine (heq_of_eq (boundedConstructibleUpperStar_map_hom Λ ℓ w (A.unit.app K))).trans ?_
    apply mapHEq _ rfl rfl
    exact heq_of_eq (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit_app_hom Λ ℓ j K)
  · have h := boundedConstructiblePullbackSquareComparison_hom_app_hom_eq_pullbackSquareComparison ℓ Λ sq.toCommSq.flip E
    refine HEq.trans ?_ ((heq_of_eq h).trans ?_)
    -- The square component has composite functors at both endpoints.
    · apply homHEq
      · dsimp only [Functor.comp_obj, E]
      · dsimp only [Functor.comp_obj, E]
      · apply isoAppHEq <;> rfl
    · apply isoAppHEq
      · rfl
      · rfl
      · rfl
      · exact boundedConstructibleOpenImmersionLowerShriek_obj_obj Λ ℓ j K

end WeilII
