module

public import WeilII.AlgebraicGeometry.BoundedPullbackComparisonLift
public import WeilII.AlgebraicGeometry.UnderlyingSchemePullbackSquareComponent

/-! # Pasting bounded pullback squares along maps of underlying schemes -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Two vertically composable squares of underlying scheme maps induce the outer bounded
pullback square. Eliminate the two factorization equalities and compare inverse components
after the faithful inclusion. Each inverse projects to the ambient square and each vertical
composition comparison projects to its ambient counterpart. This gives
`pullbackSquareComparison_paste_horizontal` in the ambient category. Inverting the equality
recovers the indicated forward components in reverse order. -/
public theorem underlyingSchemePullbackComparison_paste
    {k k' : Type u} [Field k] [Field k'] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    {X Z Y : Over (Spec (.of k))} {X' Z' Y' : Over (Spec (.of k'))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {i : X ⟶ Z} {g : Z ⟶ Y} {i' : X' ⟶ Z'} {g' : Z' ⟶ Y'}
    {p : X'.left ⟶ X.left} {v : Z'.left ⟶ Z.left} {q : Y'.left ⟶ Y.left}
    (sf : CommSq p f'.left f.left q) (si : CommSq p i'.left i.left v)
    (sg : CommSq v g'.left g.left q) (hf : i ≫ g = f) (hf' : i' ≫ g' = f') :
    @IsPullbackComparisonPaste _ _ _ _ _ _ _ _ _ _ _ _
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ i')
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g')
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f')
      (boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') q)
      (boundedConstructibleUpperStarOfMap ℓ (X := Z) (Y := Z') v)
      (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') p)
      (boundedConstructibleUpperStarOfMapSquareIso ℓ i i' si.w).symm
      (boundedConstructibleUpperStarOfMapSquareIso ℓ g g' sg.w).symm
      (boundedConstructibleUpperStarOfMapSquareIso ℓ f f' sf.w).symm
      (boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ hf)
      (boundedConstructibleUpperStarTriangleComparison (Profinite.padicAlgClRingObj ℓ) ℓ hf') := by
  exact boundedPullbackComparison_paste_of_inverse_app ℓ sf si sg hf hf' _
    (underlyingSchemePullbackComparison_inv_app_hom ℓ i i' si) _
    (underlyingSchemePullbackComparison_inv_app_hom ℓ g g' sg) _
    (underlyingSchemePullbackComparison_inv_app_hom ℓ f f' sf)

end WeilII
