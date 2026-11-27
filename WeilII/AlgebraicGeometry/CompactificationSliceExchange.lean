module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedExchange
public import WeilII.AlgebraicGeometry.CompactificationExchangeComparison
import WeilII.AlgebraicGeometry.CompactificationOpenFactor
import WeilII.AlgebraicGeometry.BoundedSliceDirectImageExchange
import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedProper
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Comparing the slice and underlying-scheme compactification exchanges -/

public noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (c : Compactification f.left) (d : Compactification f'.left) (r : d.overObj ⟶ c.overObj)
  (hi : IsPullback g' d.overI c.overI r) (hp : IsPullback r d.overG c.overG g)

private theorem paste_hom {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    {I : A ⥤ B} {P : B ⥤ C} {I' : A' ⥤ B'} {P' : B' ⥤ C'}
    {U : A ⥤ A'} {V : B ⥤ B'} {W : C ⥤ C'}
    (o : I ⋙ V ≅ U ⋙ I') (p : P ⋙ W ≅ V ⋙ P') :
    (Adjunction.compForgetIso o p).hom =
      (Functor.associator I P W).hom ≫ Functor.whiskerLeft I p.hom ≫ (Functor.associator I V P').inv ≫
        Functor.whiskerRight o.hom P' ≫ (Functor.associator U I' P').hom := rfl

/-- For one cartesian pair, the bounded slice exchange has the specified underlying-scheme
exchange as its component. Source: BaseChangeIndependence, SmoothPurityFieldPastedExchange,
and SmoothPurityAmbientOpenExchange. Factor the slice exchange as the proper exchange on
the extended complex followed by the proper direct image of the open exchange. The proper
exchange is the right mate of the pullback square. Inclusion preserves its restricted unit,
pullback comparison and counit. In left-derived coordinates this is the ambient proper
exchange, since the levelwise pullback comparisons in its definition cancel in pairs.
For the open factor compare inverses. The bounded inverse is the left mate of the pullback
square for the open adjunctions. Restriction to the full subcategories preserves their units
and counits. All four functors are exact, so the derived left mate is the levelwise image
of the sheaf left mate, under the exact-pullback comparisons. The latter is the inverse of
the specified open exchange. Invert the component equality and apply the proper functor.
Pasting the two component equalities gives the restricted ambient exchange. -/
theorem compactificationSliceExchange_eq_field [@WeaklyEtale d.Z c.Z r.left] [WeaklyEtale g.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c d r hi hp).app K =
      (purityFieldCompactificationExchange ℓ f f' c d (πX := g'.left) (πY := g.left)
        (πZ := r.left) hi.overLeft.flip hp.overLeft).hom.app K := by
  let Λ := Profinite.padicAlgClRingObj ℓ
  let z : d.Z ⟶ c.Z := r.left
  have : WeaklyEtale z := ‹@WeaklyEtale d.Z c.Z r.left›
  let si : IsPullback d.i g'.left z c.i := hi.overLeft.flip
  let sp : IsPullback z d.g c.g g.left := hp.overLeft
  let ef := purityFieldOpenRestrictedExchange ℓ f f' c d si
  let pf := purityFieldProperRestrictedExchange ℓ f f' c d sp
  have hop : (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ hi).hom = ef.hom := by
    exact compactification_open_factor ℓ c d r hi
  have hpr : boundedConstructibleBaseChange ℓ hp.toCommSq = pf.hom := by
    have : WeaklyEtale (show d.overObj.left ⟶ c.overObj.left from r.left) :=
      ‹@WeaklyEtale d.Z c.Z r.left›
    exact (boundedSliceDirectImageExchange_eq_ofMap ℓ hp).trans
      (purityFieldProperRestrictedExchange_hom ℓ f f' c d sp).symm
  let I := boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI
  let I' := boundedConstructibleOpenImmersionLowerShriek Λ ℓ d.overI
  let P := boundedConstructibleLowerStar ℓ c.overG
  let P' := boundedConstructibleLowerStar ℓ d.overG
  let U := boundedConstructibleUpperStar Λ ℓ g'
  let V := boundedConstructibleUpperStar Λ ℓ r
  let W := boundedConstructibleUpperStar Λ ℓ g
  let paste (o : I ⋙ V ⟶ U ⋙ I') (p : P ⋙ W ⟶ V ⋙ P') :=
    (Functor.associator I P W).hom ≫ Functor.whiskerLeft I p ≫ (Functor.associator I V P').inv ≫
      Functor.whiskerRight o P' ≫ (Functor.associator U I' P').hom
  have hpaste : boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c d r hi hp =
      paste (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ hi).hom
        (boundedConstructibleBaseChange ℓ hp.toCommSq) := boundedConstructibleLowerShriekOfCompactificationBaseChange_eq ℓ c d r hi hp
  have hf := purityFieldCompactificationExchange_eq_paste ℓ f f' c d (πZ := r.left) si sp
  have hfield : (purityFieldCompactificationExchange ℓ f f' c d si sp).hom = paste ef.hom pf.hom := (congrArg Iso.hom hf).trans (paste_hom ef pf)
  have hm := congrArg₂ paste hop hpr
  have hn := (hpaste.trans hm).trans hfield.symm
  apply congr_app _ K
  exact hn


/-- On a bounded input the component of the slice exchange is the specified ambient
exchange between the two open/proper factorizations. -/
theorem compactificationSliceExchange_underlying [@WeaklyEtale d.Z c.Z r.left] [WeaklyEtale g.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ c d r hi hp).app K).hom =
      (purityFieldCompactificationAmbientExchange ℓ f f' c d (πX := g'.left) (πY := g.left)
        (πZ := r.left) hi.overLeft.flip hp.overLeft).hom.app K.obj := by
  let P := L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
  let K' := (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X') g'.left).obj K
  let b := (purityFieldCompactificationAmbientExchange ℓ f f' c d (πX := g'.left)
    (πY := g.left) (πZ := r.left) hi.overLeft.flip hp.overLeft).hom.app K.obj
  have hx := congrArg Iso.hom (compactificationCompatibility_component ℓ c K)
  have hy := congrArg Iso.inv (compactificationCompatibility_component ℓ d K')
  change (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ c).hom.app K = 𝟙 _ at hx
  change (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ d).inv.app K' = 𝟙 _ at hy
  have hx' := (congrArg (fun m ↦ P.map m) hx).trans (P.map_id _)
  refine (congrArg (fun v ↦ v.hom) (compactificationSliceExchange_eq_field ℓ c d r hi hp K)).trans ?_
  refine (purityFieldCompactificationExchange_hom_app_hom ℓ f f' c d
    (πZ := r.left) hi.overLeft.flip hp.overLeft K).trans ?_
  exact (congrArg₂ (· ≫ ·) hx' (congrArg (b ≫ ·) hy)).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- The exchange square in ambient coordinates for two cartesian compactifications of
a fixed square over a field. Both vertical comparisons are the bounded comparisons on
the underlying objects. -/
theorem compactificationAmbientExchange_comparison (sq : IsPullback g' f' f g)
    (a b : Compactification f.left) (a' b' : Compactification f'.left)
    (s : a'.overObj ⟶ a.overObj) (t : b'.overObj ⟶ b.overObj)
    (ai : IsPullback g' a'.overI a.overI s) (ap : IsPullback s a'.overG a.overG g)
    (bi : IsPullback g' b'.overI b.overI t) (bp : IsPullback t b'.overG b.overG g)
    [@WeaklyEtale a'.Z a.Z s.left] [@WeaklyEtale b'.Z b.Z t.left] [WeaklyEtale g.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    let P := L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    let Q := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'
    P.map (ambientCompactificationComparison ℓ a b K).hom ≫
      (purityFieldCompactificationAmbientExchange ℓ f f' b b' (πZ := t.left)
        bi.overLeft.flip bp.overLeft).hom.app K.obj =
      (purityFieldCompactificationAmbientExchange ℓ f f' a a' (πZ := s.left)
        ai.overLeft.flip ap.overLeft).hom.app K.obj ≫
        (ambientCompactificationComparison ℓ a' b' (Q.obj K)).hom := by
  intro P Q
  let E₁ := boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ a a' s ai ap
  let E₂ := boundedConstructibleLowerShriekOfCompactificationBaseChange ℓ b b' t bi bp
  let u := ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ a b).hom.app K).hom
  let v := ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ a' b').hom.app (Q.obj K)).hom
  have hc : P.map u ≫ (E₂.app K).hom = (E₁.app K).hom ≫ v :=
    congrArg (fun m ↦ m.hom) (congr_app (compactificationExchange_comparison ℓ sq
      a b a' b' s t ai ap bi bp) K)
  have h₁ := compactificationSliceExchange_underlying ℓ a a' s ai ap K
  have h₂ := compactificationSliceExchange_underlying ℓ b b' t bi bp K
  exact (congrArg₂ (· ≫ ·) (congrArg P.map (ambientCompactificationComparison_hom ℓ a b K))
    h₂.symm).trans (hc.trans (congrArg₂ (· ≫ ·) h₁
    (ambientCompactificationComparison_hom ℓ a' b' (Q.obj K)).symm))

/-- The ambient comparison square in explicitly identified coordinates. -/
theorem compactificationAmbientExchange_comparison_components (sq : IsPullback g' f' f g)
    (a b : Compactification f.left) (a' b' : Compactification f'.left)
    (s : a'.overObj ⟶ a.overObj) (t : b'.overObj ⟶ b.overObj)
    (ai : IsPullback g' a'.overI a.overI s) (ap : IsPullback s a'.overG a.overG g)
    (bi : IsPullback g' b'.overI b.overI t) (bp : IsPullback t b'.overG b.overG g)
    [@WeaklyEtale a'.Z a.Z s.left] [@WeaklyEtale b'.Z b.Z t.left] [WeaklyEtale g.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (u : (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) a).obj K.obj ⟶
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) b).obj K.obj)
    (hu : (ambientCompactificationComparison ℓ a b K).hom = u)
    {E₁ E₂ v}
    (h₁ : (purityFieldCompactificationAmbientExchange ℓ f f' a a' (πZ := s.left)
      ai.overLeft.flip ap.overLeft).hom.app K.obj = E₁)
    (h₂ : (purityFieldCompactificationAmbientExchange ℓ f f' b b' (πZ := t.left)
      bi.overLeft.flip bp.overLeft).hom.app K.obj = E₂)
    (hv : (ambientCompactificationComparison ℓ a' b'
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj K)).hom = v) :
    L((g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map u ≫ E₂ = E₁ ≫ v := by
  subst u E₁ E₂ v
  exact compactificationAmbientExchange_comparison ℓ sq a b a' b' s t ai ap bi bp K

end WeilII
