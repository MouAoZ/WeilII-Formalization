module

public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence

/-! # The ambient component of a bounded pullback square -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Under the full-subcategory inclusion the inverse bounded square is the ambient forward
square. Expand the two composition comparisons and the equality transport in the middle.
The inclusion sends each bounded composition component to its ambient component and
the middle equality morphism to the induced equality morphism. -/
public theorem underlyingSchemePullbackComparison_inv_app_hom
    {k k' : Type u} [Field k] [Field k'] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
    {X Y : Over (Spec (.of k))} {X' Y' : Over (Spec (.of k'))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (f : X ⟶ Y) (f' : X' ⟶ Y') {p : X'.left ⟶ X.left} {q : Y'.left ⟶ Y.left}
    (s : CommSq p f'.left f.left q) (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarOfMapSquareIso ℓ f f' s.w).inv.app B).hom =
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) s).hom.app B.obj := by
  simp only [boundedConstructibleUpperStarOfMapSquareIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, eqToIso.inv, eqToHom_app, ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleUpperStarOfMapComp_hom_app_hom, ObjectProperty.eqToHom_hom,
    pullbackSquareComparison_hom_app, Category.assoc]
  rfl

end WeilII
