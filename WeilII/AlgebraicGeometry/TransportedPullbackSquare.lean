module

public import WeilII.AlgebraicGeometry.TransportSchemeSlice
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale

/-! # Components of the underlying-scheme pullback square and transport of the shriek functor -/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilII

universe u

/-- The inverse component of the bounded pullback comparison on a commuting square
of scheme maps restricts the ambient pullback comparison. Evaluating the two
composition constraints and the intervening equality transport gives its formula. -/
public theorem schemePullbackSquare_inv_component {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (f : U ⟶ V) (f' : U' ⟶ V') {i : U'.left ⟶ U.left} {j : V'.left ⟶ V.left}
    (h : CommSq i f'.left f.left j) (K : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperStarOfMapSquareIso ℓ f f' h.w).inv.app K).hom =
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) h).hom.app K.obj := by
  simp only [boundedConstructibleUpperStarOfMapSquareIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, eqToIso.inv, eqToHom_app, ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleUpperStarOfMapComp_hom_app_hom, ObjectProperty.eqToHom_hom,
    pullbackSquareComparison_hom_app, Category.assoc]
  rfl

/-- Changing the field structures on the source and target of the primed edge leaves the
chosen shriek functor equal: Nagata compactification is chosen for its underlying arrow, and
the open extension and proper pushforward are lifts of the same ambient functors. -/
public theorem transportedShriekFunctor {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (f : U ⟶ V) (f' : U' ⟶ V') (i : U'.left ≅ U.left) (j : V'.left ≅ V.left)
    (h : CommSq i.hom f'.left f.left j.hom) :
    boundedConstructibleLowerShriek ℓ (SchemeSlice.map f i j f'.left h) =
      boundedConstructibleLowerShriek ℓ f' := by
  dsimp only [SchemeSlice.map, SchemeSlice.over, boundedConstructibleLowerShriek,
    boundedConstructibleLowerShriekOfCompactification, compactificationOverField,
    boundedConstructibleLowerStarOfIsProper, boundedConstructibleOpenImmersionLowerShriek,
    Compactification.overI, Compactification.overG, Compactification.overObj,
    Over.homMk_left, Over.mk_left]
  rfl

end WeilII
