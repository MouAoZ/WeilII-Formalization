module

public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
public import WeilII.AlgebraicGeometry.DerivedOpenExtensionUnitEquation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents
import WeilII.AlgebraicGeometry.UnderlyingPullbackSquareOfMap

/-!
# Restriction of the ambient open-extension unit equation

The horizontal maps may connect schemes over different fields.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

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

/-- The unit equation descends from the ambient derived categories for any bounded
comparison arrow at an object. The vertical maps are open immersions and the horizontal
scheme maps commute with them.

Apply faithfulness of the full subcategory inclusion. By
`boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit_app_hom` the two
unit components project to the transported derived units. The two restricted pullback
functors project on morphisms to their total derived pullbacks. Expand the square from
`SmoothUnitBaseChangeEtale.lean` as the inverse of the first composition comparison,
transport along the square equality, and the second composition comparison. The
comparisons project to `leftDerivedUpperStarComp` by their component construction in
`DualizingFieldChange/GenericPoint.lean`. The inclusion sends the middle transport to
transport on the underlying objects, by equality induction. These three components give
`pullbackSquareComparison_hom_app` for the flipped square. The projected equality is now
the assumed ambient unit equation. -/
public theorem restrictOpenExtensionUnitEquation
    {k k' : Type u} [Field k] [Field k'] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    {U Z : Over (Spec (.of k))} {U' Z' : Over (Spec (.of k'))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    (j : U ⟶ Z) (j' : U' ⟶ Z') {p : U'.left ⟶ U.left} {q : Z'.left ⟶ Z.left}
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left] (sq : CommSq p j'.left j.left q)
    (A : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (s : (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j').obj
        ((boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') p).obj A) ⟶
      (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') q).obj
        ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj A))
    (hs : DerivedOpenExtensionUnitEquation (Profinite.padicAlgClRingObj ℓ) sq A.obj s.hom) :
    let Λ := Profinite.padicAlgClRingObj ℓ
    let FU := boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') p
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').unit.app (FU.obj A) ≫
        (boundedConstructibleUpperStar Λ ℓ j').map s =
      FU.map ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit.app A) ≫
        (boundedConstructibleUpperStarOfMapSquareIso ℓ j j' sq.w).hom.app
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj A) := by
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
  intro Λ FU
  let B := FU.obj A
  let E := (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj A
  let η := (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit.app A
  dsimp only [DerivedOpenExtensionUnitEquation] at hs
  have transfer := @assemble _ _ _ _ _ _ _ _ _ _ hs
  apply transfer (P := boundedConstructible (condensedRingObj Λ U'.left))
  · rfl
  · rfl
  · rfl
  · rfl
  · refine (heq_of_eq (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit_app_hom
      Λ ℓ j' B)).trans ?_
    apply appHEq
    rfl
  · refine (heq_of_eq (boundedConstructibleUpperStar_map_hom Λ ℓ j' s)).trans ?_
    apply mapHEq _ rfl rfl
    rfl
  · have h := congrArg (·.hom) (boundedConstructibleUpperStarOfMap_map ℓ (X := U) (Y := U') p η)
    refine (heq_of_eq h).trans ?_
    apply mapHEq _ rfl rfl
    exact heq_of_eq (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit_app_hom
      Λ ℓ j A)
  · have h := underlyingPullbackSquareOfMap ℓ j j' sq E
    refine HEq.trans ?_ ((heq_of_eq h).trans ?_)
    · apply homHEq
      · rfl
      · rfl
      · apply isoAppHEq <;> rfl
    · apply isoAppHEq
      · rfl
      · rfl
      · rfl
      · exact boundedConstructibleOpenImmersionLowerShriek_obj_obj Λ ℓ j A

end WeilII
