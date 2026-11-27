module

public import WeilII.AlgebraicGeometry.TransportSchemeSlice
import WeilII.AlgebraicGeometry.ShriekSliceFieldExchange
import WeilII.AlgebraicGeometry.ShriekBaseChangeChangePrimedStructure
meta import WeilConjectures.Tactic.ExactByKernel
public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange

/-! # Compact-support exchange along an isomorphism of underlying arrows -/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilII

universe u

/-- Give the primed schemes the field structures transported along the horizontal
isomorphisms. The ordinary base change in this slice is the original cross-field
exchange. Source: the computation on any cartesian pair in
`LowerShriek/BaseChangeIndependence.lean` and the chosen-pair definition in
`WeilSheaf/SmoothPurityFieldCompactificationExchange.lean` (weil-conjectures 497f33d).
Take the chosen compactification of the unprimed arrow and its pullback along the
underlying square. On this pair the slice exchange is the field exchange, since
both the base isomorphism and its pullback are weakly étale. Forget to the ambient
derived category. The middle exchange depends only on the underlying arrows, and
the inclusion comparisons are identities. The initial comparison is unchanged.
For the final comparison with the chosen primed compactification, use the same
common proper refinement for both structures, giving its middle scheme the structure
induced by its proper projection. Its transition maps coincide: their pullback
constraints and the units and counits defining the open/proper mates have the same
ambient components. This identifies the final comparison, and faithfulness gives
the equality in the bounded constructible category. -/
public theorem transportedShriekEdge_eq_field {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {U V U' V' : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom] [IsSeparated U'.hom]
    [LocallyOfFiniteType V'.hom] [QuasiCompact V'.hom] [IsSeparated V'.hom]
    (f : U ⟶ V) (f' : U' ⟶ V') (i : U'.left ≅ U.left) (j : V'.left ≅ V.left)
    (h : CommSq i.hom f'.left f.left j.hom) (K : Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (SchemeSlice.edge f i j f'.left h)).app K =
      (purityFieldLowerShriekBaseChange ℓ f f' (IsPullback.of_horiz_isIso h)).hom.app K := by
  let ft := SchemeSlice.map f i j f'.left h
  have wy : WeaklyEtale (SchemeSlice.iso V j).hom.left := inferInstanceAs (WeaklyEtale j.hom)
  let E := purityFieldLowerShriekBaseChange ℓ f f' (IsPullback.of_horiz_isIso h)
  have exchange := sliceBaseChange_changePrimedStructure ℓ f f'
    (a := i.hom ≫ U.hom) (b := j.hom ≫ V.hom) (Over.w ft) (p' := ft) rfl
    (SchemeSlice.edge f i j f'.left h)
    E rfl K
  apply eq_of_heq
  exact_by_kernel exchange

end WeilII
