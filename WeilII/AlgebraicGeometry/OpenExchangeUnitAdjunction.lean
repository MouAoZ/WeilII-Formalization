module

public import WeilII.CategoryTheory.OpenProperProjectionComponents
public import WeilII.AlgebraicGeometry.OpenExtensionExchangeUnit

/-! # The open exchange unit as an equation between adjunctions -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

-- Compare the two presentations of the pullback with the square still a variable.
private theorem withVariableSquare
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
    [Fact (ringChar Ω ≠ ℓ)] {U Z U' Z' : Over (Spec (.of Ω))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    (j : U ⟶ Z) (j' : U' ⟶ Z') [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (tU : U'.left ≅ U.left) (tZ : Z'.left ≅ Z.left)
    (O : boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
      boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') tZ.hom ≅
      boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom ⋙
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j')
    (D : boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := U) j.left ⋙
      boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom ≅
      boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') tZ.hom ⋙
      boundedConstructibleUpperStarOfMap ℓ (X := Z') (Y := U') j'.left)
    (h : ∀ (A : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧),
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j').unit.app
          ((boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom).obj A) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j').map (O.inv.app A) =
      (boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom).map
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
            (Profinite.padicAlgClRingObj ℓ) ℓ j).unit.app A) ≫
        D.hom.app ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj A)) :
    IsOpenExchangeUnit
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j')
      (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') tZ.hom)
      (boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom)
      O D.symm := by
  exact h

/-- In the open base-change unit equation one may take the restriction functors to be the
right adjoints of the two bounded extensions by zero. For a map in the slice the pullback
along the underlying scheme map and the slice pullback both lift the same derived inverse
image. Their preservation proofs agree by proof irrelevance. Read the square comparison
between these identified functors and apply
`WeilII.openExtensionExchangeUnit_underSchemeIsomorphisms` at each object. -/
public theorem isOpenExchangeUnit_underSchemeIsomorphisms
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
    [Fact (ringChar Ω ≠ ℓ)] {U Z U' Z' : Over (Spec (.of Ω))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    (j : U ⟶ Z) (j' : U' ⟶ Z') [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (tU : U'.left ≅ U.left) (tZ : Z'.left ≅ Z.left) (sq : CommSq tU.hom j'.left j.left tZ.hom) :
    IsOpenExchangeUnit
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ j')
      (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') tZ.hom)
      (boundedConstructibleUpperStarOfMap ℓ (X := U) (Y := U') tU.hom)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarOfMapIso ℓ (j := j) (j' := j')
        (IsPullback.of_horiz_isIso sq))
      (boundedConstructibleUpperStarOfMapSquareIso ℓ j j' sq.w).symm := by
  exact withVariableSquare ℓ j j' tU tZ _ _
    (openExtensionExchangeUnit_underSchemeIsomorphisms ℓ j j' tU tZ sq)

end WeilII
