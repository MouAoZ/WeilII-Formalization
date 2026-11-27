module

public import WeilConjectures.WeilSheaf.CondensedModelGeometricFiberPullback
public import WeilConjectures.WeilSheaf.SmoothPurityAmbientOpenExchange
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangePoint
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
import WeilConjectures.CategoryTheory.ObjectProperty.LiftSquareIso
import WeilII.AlgebraicGeometry.RestrictOpenExtensionUnitEquation
import WeilII.AlgebraicGeometry.DerivedOpenExtensionExchangeUnit

/-!
# Base change of the unit for extension by zero

For bounded constructible condensed `ℚ̄_ℓ` complexes, the inverse of the open-extension exchange
transposes to the pullback of the adjunction unit followed by the pullback square comparison.
The exchange is the one in `WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangePoint`, and its
sheaf-level normalization comes from `WeilConjectures.WeilSheaf.SmoothPurityAmbientOpenExchange`.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- For two open immersions related by isomorphisms of the underlying schemes, the unit for the
primed open immersion followed by restriction of the inverse open exchange agrees with pullback
of the unprimed unit followed by the forward pullback comparison.

Proof. Work first with sheaves of modules. The horizontal isomorphisms make the square
cartesian. Apply `purityOpenImmersionLowerShriekUpperStarBaseChangeIso_inv` to the transposed
square. It identifies the inverse open exchange with the left mate of the pullback comparison.
In the transpose of the mate, naturality of the primed unit and the triangle identity cancel
the extra unit and counit. This leaves the pullback of the unit followed by the comparison.

Open extension, open restriction and pullback by a scheme isomorphism are exact. Apply
`mapDerivedCategoryAdjunction_mate` to the sheaf-level identity. Deriving the inverse exchange
gives the inverse of the derived exchange by `mapDerivedCategorySquareIso_symm`. This proves
the formula for the levelwise derived functors.

Now forget to the ambient derived categories. Write `c_f : L(f^*) ≅ D(f^*)` for the comparison
with levelwise pullback. The formula for a restricted adjunction unit identifies each bounded
unit with its levelwise unit followed by the inverse of `c_j` or `c_{j'}` at the extended object.
The definition of the bounded open exchange identifies its inverse with the composite of the
primed extension of `c_{tU}`, the inverse levelwise exchange, and the inverse of `c_{tZ}` at
the unprimed extension. The bounded pullback square forgets to the ambient square since its
composition comparisons forget to `leftDerivedUpperStarComp`. By
`pullbackSquareComparison_eq_leftDerivedFunctorSquareIso` and `leftDerivedFunctorSquareIso_hom_app`,
the comparisons for the two composite pullbacks carry this square to the levelwise square.

Postcompose both paths with the comparison from `L(j'^*) L(tZ^*)` to `D(j'^*) D(tZ^*)`.
On the left, naturality cancels the comparisons for the primed restriction and for `tZ` and
allows `c_{tU}` to move past the primed unit to the source. On the right, the pullback square
comparison just described and naturality of `c_{tU}` cancel the comparison for the unprimed
restriction. These are the two sides of the levelwise unit equation precomposed with `c_{tU}` at `A`.
Cancel the target isomorphism and use faithfulness of the bounded inclusion. -/
public theorem openExtensionExchangeUnit_underSchemeIsomorphisms
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
    [Fact (ringChar Ω ≠ ℓ)] {U Z U' Z' : Over (Spec (.of Ω))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    (j : U ⟶ Z) (j' : U' ⟶ Z') [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (tU : U'.left ≅ U.left) (tZ : Z'.left ≅ Z.left) (sq : CommSq tU.hom j'.left j.left tZ.hom)
    (A : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    let Λ := Profinite.padicAlgClRingObj ℓ
    let FU := boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom
    let O := boundedConstructibleOpenImmersionLowerShriekUpperStarOfMapIso ℓ (j := j) (j' := j')
      (IsPullback.of_horiz_isIso sq)
    let D := boundedConstructibleUpperStarOfMapSquareIso ℓ j j' sq.w
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j').unit.app (FU.obj A) ≫
        (boundedConstructibleUpperStar Λ ℓ j').map (O.inv.app A) =
      FU.map ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit.app A) ≫
        D.hom.app ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj A) := by
  intro Λ FU O D
  let cart := IsPullback.of_horiz_isIso sq
  have hO : (O.inv.app A).hom =
      (openImmersionLowerShriek Λ j'.left).mapDerivedCategory.map
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ tU.hom).hom.app A.obj) ≫
        (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ cart.flip).inv.app A.obj ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ tZ.hom).inv.app
          ((openImmersionLowerShriek Λ j.left).mapDerivedCategory.obj A.obj) := by
    let e₀ := Functor.isoWhiskerLeft (openImmersionLowerShriek Λ j.left).mapDerivedCategory
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ tZ.hom) ≪≫
      openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ cart.flip ≪≫
      Functor.isoWhiskerRight (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ tU.hom).symm
        (openImmersionLowerShriek Λ j'.left).mapDerivedCategory
    calc
      _ = e₀.inv.app A.obj := ObjectProperty.preimageIso_liftSquare_inv_app_hom
        (boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j)
        (boundedConstructible_openImmersionLowerShriek_obj Λ ℓ j')
        (fun B ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ tU.hom B.obj B.property)
        (fun B ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ tZ.hom B.obj B.property)
        e₀ A
      _ = _ := by
        simp only [e₀, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
          Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Iso.symm_inv, Category.assoc]
  apply restrictOpenExtensionUnitEquation ℓ j j' sq A (O.inv.app A)
  rw [hO]
  exact derivedOpenExtensionExchangeUnit Λ cart A.obj

end WeilII

