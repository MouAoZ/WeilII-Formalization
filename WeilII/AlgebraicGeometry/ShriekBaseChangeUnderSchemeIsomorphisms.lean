module

public import WeilConjectures.TraceFormula.BaseChangeCoherence
public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedProper
public import WeilConjectures.WeilSheaf.SmoothPurityPointOpenComparison
public import WeilConjectures.WeilSheaf.SmoothUnitBaseChangeEtale

import WeilII.AlgebraicGeometry.ShriekBaseChangeSliceCube
import WeilII.AlgebraicGeometry.TransportedShriekEdge
import WeilII.AlgebraicGeometry.TransportedPullbackSquare
import WeilII.AlgebraicGeometry.TransportedPullbackSquareComponent
import WeilII.Tactic.SchemeComponentCongruence
import WeilII.AlgebraicGeometry.ShriekBaseChangeFieldStructures

/-!
# Transport of compact-support base change along scheme isomorphisms

The two horizontal pastings in `WeilConjectures.TraceFormula.WeilBaseChange` compare base change
for automorphisms over the field. The cube below uses the cross-field shriek comparison for
isomorphisms of the underlying schemes, as needed for the geometric Frobenius in Zhang's
deduction of Theorem 1.1 from Proposition 1.5.
-/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

/-- Compact-support base change for two cartesian squares commutes with transport along
isomorphisms of their underlying schemes, at every bounded constructible coefficient complex.

Proof (horizontal pasting in `TraceFormula/BaseChangeCoherence.lean` and the open–proper formula
in `WeilSheaf/SmoothPurityFieldPastedExchange.lean`, weil-conjectures revision `497f33d`).
Give each primed vertex the structure map obtained by composing its isomorphism with the
unprimed structure map. The four commutations make all primed arrows maps in this slice. Both
original squares are still cartesian there, by the underlying pullback property. The connecting
faces for `g` and `p` are cartesian because their horizontal arrows are invertible.

Compute each slice exchange using the chosen compactification of its right edge and its pullback
on the left. The chosen compactification depends only on the underlying arrow, by proof
irrelevance for existence of a compactification. For the comparison from the pulled-back to the
chosen compactification on the left, take a common proper refinement and use it also in the
new slice by composing its proper projection with the new structure map. The comparison goes
from the first shriek functor to that of the refinement, then to the second by inverse transition.
Each transition inserts the identity direct image, exchanges open extension with proper direct
image, and composes direct images. These maps agree under the two field structures after the
fully faithful bounded inclusion. Indeed, pullback composition has the same ambient comparison,
the direct-image constraints are its adjoint mates, and the open–proper exchange is the right
mate of open base change, whose inverse is itself a mate of the pullback square.

In the proper factor of base change the adjoint transpose is the pullback comparison followed
by pullback of the counit. For the inverse of the open factor the transpose is pullback of the
unit followed by the pullback comparison. These formulas agree in the two slices because the
restricted adjunctions have the same ambient units and counits. Thus the primed exchange equals
the originally specified one. On the connecting faces the base isomorphism and its pullback to
the compactification are weakly étale. The cross-field open–proper formula has these same two
transposes and the same final compactification comparison, so the exchanges there are `Ep` and
`Eg`.

Paste the two faces through `p`, and then paste the two through `g'`. The two outer rectangles
have equal top and bottom arrows by `hs` and `hf`, so their exchanges agree after transport
of the composite pullbacks. Expand both by horizontal pasting. The top pullback composition
comparisons on either side of this transport give `Ds`; the bottom comparisons give `Df`.
Cancel the inverse composition comparisons to obtain the displayed equality. -/
public theorem shriekBaseChangeUnderSchemeIsomorphisms
    {Ω : Type u} [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar Ω).Prime]
    [Fact (ringChar Ω ≠ ℓ)]
    {P X Y S P' X' Y' S' : Over (Spec (.of Ω))}
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom] [IsSeparated S'.hom]
    {s : P ⟶ Y} {p : P ⟶ X} {g : Y ⟶ S} {f : X ⟶ S} (sq : IsPullback s p g f)
    {s' : P' ⟶ Y'} {p' : P' ⟶ X'} {g' : Y' ⟶ S'} {f' : X' ⟶ S'} (sq' : IsPullback s' p' g' f')
    (tP : P'.left ≅ P.left) (tX : X'.left ≅ X.left)
    (tY : Y'.left ≅ Y.left) (tS : S'.left ≅ S.left)
    (hs : CommSq tP.hom s'.left s.left tY.hom) (hp : CommSq tP.hom p'.left p.left tX.hom)
    (hg : CommSq tY.hom g'.left g.left tS.hom) (hf : CommSq tX.hom f'.left f.left tS.hom)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    let FX := boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') tX.hom
    let FY := boundedConstructibleUpperStarOfMap ℓ (X := Y) (Y := Y') tY.hom
    let Ep := purityFieldLowerShriekBaseChange ℓ p p' (IsPullback.of_horiz_isIso hp)
    let Eg := purityFieldLowerShriekBaseChange ℓ g g' (IsPullback.of_horiz_isIso hg)
    let Ds := boundedConstructibleUpperStarOfMapSquareIso ℓ s s' hs.w
    let Df := boundedConstructibleUpperStarOfMapSquareIso ℓ f f' hf.w
    let sStar := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ s
    let fStar' := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f'
    FX.map ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app L) ≫
        Ep.hom.app (sStar.obj L) ≫ (boundedConstructibleLowerShriek ℓ p').map (Ds.hom.app L) =
      Df.hom.app ((boundedConstructibleLowerShriek ℓ g).obj L) ≫
        fStar'.map (Eg.hom.app L) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq').app (FY.obj L) := by
  intro FX FY Ep Eg Ds Df sStar fStar'
  let qP := SchemeSlice.iso P tP
  let qX := SchemeSlice.iso X tX
  let qY := SchemeSlice.iso Y tY
  let qS := SchemeSlice.iso S tS
  let sl := SchemeSlice.map s tP tY s'.left hs
  let pl := SchemeSlice.map p tP tX p'.left hp
  let gl := SchemeSlice.map g tY tS g'.left hg
  let fl := SchemeSlice.map f tX tS f'.left hf
  have sq₁ : IsPullback sl pl gl fl :=
    IsPullback.of_map_of_faithful (Over.forget _) sq'.overLeft
  have sp := SchemeSlice.edge p tP tX p'.left hp
  have sg := SchemeSlice.edge g tY tS g'.left hg
  have ss := (SchemeSlice.edge s tP tY s'.left hs).toCommSq
  have sf := (SchemeSlice.edge f tX tS f'.left hf).toCommSq
  have cube := shriekBaseChange_sliceCube ℓ sq sq₁ qP.hom qX.hom qY.hom qS.hom ss sp sg sf L
  have row := shriekBaseChange_changeStructure ℓ sq'
    (a := tY.hom ≫ Y.hom) (b := tS.hom ≫ S.hom)
    (a' := tP.hom ≫ P.hom) (b' := tX.hom ≫ X.hom) (Over.w sl) (Over.w fl) (Over.w gl)
    (Over.w pl) sq₁ ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ qY.hom).obj L)
  have pp := transportedShriekEdge_eq_field ℓ p p' tP tX hp (sStar.obj L)
  have gg := transportedShriekEdge_eq_field ℓ g g' tY tS hg L
  have ds := transportedPullbackSquare_app ℓ s s' tP tY hs L
  have df := transportedPullbackSquare_app ℓ f f' tX tS hf
    ((boundedConstructibleLowerShriek ℓ g).obj L)
  have pFunctor := transportedShriekFunctor ℓ p p' tP tX hp
  have gFunctor := transportedShriekFunctor ℓ g g' tY tS hg
  have tail := congrArg (boundedConstructibleLowerShriek ℓ p').map ds.symm
  have mapped := congrArg (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ fl).map gg
  have right := congrArg₂ (· ≫ ·) df (congrArg₂ (· ≫ ·) mapped row)
  let h := FX.map ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app L)
  have left := congrArg (h ≫ ·) (congrArg₂ (· ≫ ·) pp.symm tail)
  refine Eq.trans ?_ (Eq.trans cube ?_)
  · scheme_component_exact left using pFunctor, gFunctor
  · scheme_component_exact right using pFunctor, gFunctor

end WeilII
