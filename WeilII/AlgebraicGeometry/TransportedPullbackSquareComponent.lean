module

public import WeilII.AlgebraicGeometry.TransportSchemeSlice
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale
import WeilII.Tactic.SchemeComponentCongruence

/-! # Pullback comparison under transport of the primed field structures -/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Transporting the primed slice structures preserves the pullback-square component.
Both composite pullback constraints lift the ambient constraints on the same
underlying arrows. The intervening transports agree by proof irrelevance. -/
public theorem transportedPullbackSquare_app {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (f : U ⟶ V) (f' : U' ⟶ V') (i : U'.left ≅ U.left) (j : V'.left ≅ V.left)
    (h : CommSq i.hom f'.left f.left j.hom) (K : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarOfMapSquareIso ℓ (U' := SchemeSlice.over U i)
      (V' := SchemeSlice.over V j) f (SchemeSlice.map f i j f'.left h)
      (πU := i.hom) (πV := j.hom) h.w).hom.app K =
      (boundedConstructibleUpperStarOfMapSquareIso ℓ f f' h.w).hom.app K := by
  scheme_pullback_component_rfl

end WeilII
