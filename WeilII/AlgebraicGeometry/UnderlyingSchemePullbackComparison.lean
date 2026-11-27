module

public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.Tensor

/-! # Comparison of the two bounded pullback squares on underlying schemes -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- The inverse of the square built from composition of bounded pullbacks is the restriction
of the ambient pullback square. Expand both squares into their two composition comparisons
and the transport along commutativity. The composition comparisons are defined componentwise
by restricting the ambient ones. The middle transports agree by equality induction. -/
public theorem underlyingSchemePullbackComparison
    {k k' : Type u} [Field k] [Field k'] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    {X Y : Over (Spec (.of k))} {X' Y' : Over (Spec (.of k'))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (f : X ⟶ Y) (f' : X' ⟶ Y') {p : X'.left ⟶ X.left} {q : Y'.left ⟶ Y.left}
    (s : CommSq p f'.left f.left q) :
    (boundedConstructibleUpperStarOfMapSquareIso ℓ f f' s.w).inv =
      boundedConstructiblePullbackComparisonOfMap ℓ s := by
  ext B
  simp only [boundedConstructibleUpperStarOfMapSquareIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, eqToIso.inv, eqToHom_app, ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleUpperStarOfMapComp_hom_app_hom, ObjectProperty.eqToHom_hom,
    boundedConstructiblePullbackComparisonOfMap, NearbyCyclesModel.liftExchange_app_hom,
    pullbackSquareComparison_hom_app, Category.assoc]
  rfl

end WeilII
