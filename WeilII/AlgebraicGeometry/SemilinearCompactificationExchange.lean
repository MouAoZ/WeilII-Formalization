module

public import WeilII.AlgebraicGeometry.CompactificationSliceExchange
import WeilII.AlgebraicGeometry.CompactificationComparisonReindex
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
meta import WeilII.AlgebraicGeometry.CompactificationComponentTransport

/-! # The compactification comparison square for semilinear base change -/

public noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilII

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

local notation "Λ" => Profinite.padicAlgClRingObj ℓ

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
/-- The field ambient exchange only uses the underlying scheme maps. Reindexing the
structure map of the original row therefore leaves the very same ambient isomorphism. -/
theorem fieldAmbientExchange_reindex {f : X ⟶ Y} (e : Spec (.of k) ≅ Spec (.of k))
    (a d : Compactification f.left)
    (x : X.left ⟶ X.left) (y : Y.left ⟶ Y.left) (r : d.Z ⟶ a.Z)
    [WeaklyEtale y] [WeaklyEtale r] (hi : IsPullback d.i x r a.i) (hp : IsPullback r d.g a.g y) :
    purityFieldCompactificationAmbientExchange ℓ ((Over.map e.hom).map f) f a d
        (πX := x) (πY := y) (πZ := r) hi hp =
      purityFieldCompactificationAmbientExchange ℓ f f a d hi hp := by
  unfold purityFieldCompactificationAmbientExchange
  congr 1

/-- In a common slice with reindexed original row, the comparison square can be
written using the original compactification comparisons and exchanges.
Source: BaseChangeIndependence, RefinementCoherence and SmoothPurityFieldCompactificationExchange.
Apply the ambient square for the given cartesian pairs in this slice. Its original-row side
is the primed compactification comparison after the boundary identities are removed. Compute
this comparison in the original and reindexed slices using the same pair of proper refinements:
the reindexing theorem gives equality of these components. On each horizontal side, the ambient
exchange uses only the underlying pullback maps and the two underlying scheme squares, so
reindexing leaves its isomorphism unchanged. Evaluate both isomorphism equalities at the
underlying object of K and substitute these components and the reindexed comparison into the
slice square. The output comparison is evaluated at the same restricted pullback object. -/
theorem reindexedSliceCompactificationSquare {f : X ⟶ Y} (e : Spec (.of k) ≅ Spec (.of k))
    [LocallyOfFiniteType ((Over.map e.hom).obj X).hom] [QuasiCompact ((Over.map e.hom).obj X).hom]
    [IsSeparated ((Over.map e.hom).obj X).hom] [LocallyOfFiniteType ((Over.map e.hom).obj Y).hom]
    [QuasiCompact ((Over.map e.hom).obj Y).hom] [IsSeparated ((Over.map e.hom).obj Y).hom]
    {x : X ⟶ (Over.map e.hom).obj X} {y : Y ⟶ (Over.map e.hom).obj Y}
    (sq : IsPullback x f ((Over.map e.hom).map f) y) (a b a' b' : Compactification f.left)
    (s : a'.overObj (f := f) ⟶ a.overObj (f := (Over.map e.hom).map f))
    (t : b'.overObj (f := f) ⟶ b.overObj (f := (Over.map e.hom).map f))
    (ai : IsPullback x (a'.overI (f := f)) (a.overI (f := (Over.map e.hom).map f)) s)
    (ap : IsPullback s (a'.overG (f := f)) (a.overG (f := (Over.map e.hom).map f)) y)
    (bi : IsPullback x (b'.overI (f := f)) (b.overI (f := (Over.map e.hom).map f)) t)
    (bp : IsPullback t (b'.overG (f := f)) (b.overG (f := (Over.map e.hom).map f)) y)
    [@WeaklyEtale a'.Z a.Z s.left] [@WeaklyEtale b'.Z b.Z t.left] [WeaklyEtale y.left]
    (K : Dᵇc(X.left)⟦Λ⟧) :
    L((y.left)^*⟦Λ⟧).map (ambientCompactificationComparison ℓ (f := f) a b K).hom ≫
      (purityFieldCompactificationAmbientExchange ℓ f f b b' (πZ := t.left)
        bi.overLeft.flip bp.overLeft).hom.app K.obj =
      (purityFieldCompactificationAmbientExchange ℓ f f a a' (πZ := s.left)
        ai.overLeft.flip ap.overLeft).hom.app K.obj ≫
      (ambientCompactificationComparison ℓ (f := f) a' b'
        ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) x.left).obj K)).hom := by
  let F := (Over.map e.hom).map f
  have hJ := (ambientCompactificationComparison_hom ℓ (f := F) a b K).trans
    ((compactificationComparison_reindex ℓ (f := f) e a b K).trans
      (ambientCompactificationComparison_hom ℓ (f := f) a b K).symm)
  have ha := congr_app (congrArg Iso.hom (fieldAmbientExchange_reindex ℓ (f := f) e a a'
    x.left y.left s.left ai.overLeft.flip ap.overLeft)) K.obj
  have hb := congr_app (congrArg Iso.hom (fieldAmbientExchange_reindex ℓ (f := f) e b b'
    x.left y.left t.left bi.overLeft.flip bp.overLeft)) K.obj
  let E₁ := (purityFieldCompactificationAmbientExchange ℓ f f a a' (πZ := s.left)
    ai.overLeft.flip ap.overLeft).hom.app K.obj
  let E₂ := (purityFieldCompactificationAmbientExchange ℓ f f b b' (πZ := t.left)
    bi.overLeft.flip bp.overLeft).hom.app K.obj
  let V := (ambientCompactificationComparison ℓ (f := f) a' b'
    ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) x.left).obj K)).hom
  have step := compactificationAmbientExchange_comparison_components ℓ sq a b a' b' s t ai ap bi bp
    K _ hJ (E₁ := E₁) (E₂ := E₂) (v := V)
  have step₁ := step (by transport_compactification_component ha)
  have step₂ := step₁ (by transport_compactification_component hb)
  have step₃ := step₂ (by rfl)
  transport_compactification_component step₃

set_option maxHeartbeats 450000 in
/-- Base change along a semilinear cartesian square commutes with compactification comparison.
Postcompose the original structure maps with the base automorphism. This gives an ordinary
cartesian square over the field, and reindexing preserves its original comparison. -/
theorem semilinearCompactificationExchange {f : X ⟶ Y} (e : Spec (.of k) ≅ Spec (.of k))
    (x₀ : X.left ⟶ X.left) (y₀ : Y.left ⟶ Y.left) [WeaklyEtale y₀]
    (wx : x₀ ≫ X.hom ≫ e.hom = X.hom) (wy : y₀ ≫ Y.hom ≫ e.hom = Y.hom)
    (sq₀ : IsPullback x₀ f.left f.left y₀) (a b a' b' : Compactification f.left)
    (s₀ : a'.Z ⟶ a.Z) (t₀ : b'.Z ⟶ b.Z)
    (hi : IsPullback a'.i x₀ s₀ a.i) (hp : IsPullback s₀ a'.g a.g y₀)
    (ji : IsPullback b'.i x₀ t₀ b.i) (jp : IsPullback t₀ b'.g b.g y₀)
    [WeaklyEtale s₀] [WeaklyEtale t₀] (K : Dᵇc(X.left)⟦Λ⟧) :
    L((y₀)^*⟦Λ⟧).map (ambientCompactificationComparison ℓ (f := f) a b K).hom ≫
      (purityFieldCompactificationAmbientExchange ℓ f f b b' ji jp).hom.app K.obj =
    (purityFieldCompactificationAmbientExchange ℓ f f a a' hi hp).hom.app K.obj ≫
      (ambientCompactificationComparison ℓ (f := f) a' b'
        ((boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) x₀).obj K)).hom := by
  let T := Over.map e.hom
  let F := T.map f
  have : LocallyOfFiniteType (T.obj X).hom := inferInstanceAs (LocallyOfFiniteType (X.hom ≫ e.hom))
  have : IsSeparated (T.obj X).hom := inferInstanceAs (IsSeparated (X.hom ≫ e.hom))
  have : QuasiCompact (T.obj X).hom := inferInstanceAs (QuasiCompact (X.hom ≫ e.hom))
  have : LocallyOfFiniteType (T.obj Y).hom := inferInstanceAs (LocallyOfFiniteType (Y.hom ≫ e.hom))
  have : IsSeparated (T.obj Y).hom := inferInstanceAs (IsSeparated (Y.hom ≫ e.hom))
  have : QuasiCompact (T.obj Y).hom := inferInstanceAs (QuasiCompact (Y.hom ≫ e.hom))
  let x : X ⟶ T.obj X := Over.homMk x₀ wx
  let y : Y ⟶ T.obj Y := Over.homMk y₀ wy
  have sq : IsPullback x f F y :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext sq₀.w) sq₀
  let mid (c d : Compactification f.left) (r : d.Z ⟶ c.Z)
      (h : IsPullback r d.g c.g y₀) : d.overObj (f := f) ⟶ c.overObj (f := F) :=
    Over.homMk r (by
      change r ≫ c.g ≫ Y.hom ≫ e.hom = d.g ≫ Y.hom
      rw [h.w_assoc, wy])
  let s := mid a a' s₀ hp
  let t := mid b b' t₀ jp
  have ai : IsPullback x (a'.overI (f := f)) (a.overI (f := F)) s :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext hi.w.symm) hi.flip
  have ap : IsPullback s (a'.overG (f := f)) (a.overG (f := F)) y :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext hp.w) hp
  have bi : IsPullback x (b'.overI (f := f)) (b.overI (f := F)) t :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext ji.w.symm) ji.flip
  have bp : IsPullback t (b'.overG (f := f)) (b.overG (f := F)) y :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext jp.w) jp
  have : WeaklyEtale y.left := ‹WeaklyEtale y₀›
  have : @WeaklyEtale a'.Z a.Z s.left := ‹WeaklyEtale s₀›
  have : @WeaklyEtale b'.Z b.Z t.left := ‹WeaklyEtale t₀›
  have result := reindexedSliceCompactificationSquare ℓ (f := f) e sq a b a' b'
    s t ai ap bi bp K
  transport_compactification_component result

/-- Both the cartesian and normalized comparison equations, in inclusion coordinates. -/
theorem semilinearCompactificationExchange_normalized {f : X ⟶ Y} (e : Spec (.of k) ≅ Spec (.of k))
    (x₀ : X.left ⟶ X.left) (y₀ : Y.left ⟶ Y.left) [WeaklyEtale y₀]
    (wx : x₀ ≫ X.hom ≫ e.hom = X.hom) (wy : y₀ ≫ Y.hom ≫ e.hom = Y.hom)
    (sq₀ : IsPullback x₀ f.left f.left y₀) (a b a' b' : Compactification f.left)
    (s₀ : a'.Z ⟶ a.Z) (t₀ : b'.Z ⟶ b.Z)
    (hi : IsPullback a'.i x₀ s₀ a.i) (hp : IsPullback s₀ a'.g a.g y₀)
    (ji : IsPullback b'.i x₀ t₀ b.i) (jp : IsPullback t₀ b'.g b.g y₀)
    [WeaklyEtale s₀] [WeaklyEtale t₀] (K : Dᵇc(X.left)⟦Λ⟧) :
    let Q := (boundedConstructibleUpperStarOfMap ℓ (X := X) (Y := X) x₀).obj K
    let J (c d : Compactification f.left) (A : Dᵇc(X.left)⟦Λ⟧) :=
      (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ (f := f) c).inv.app A ≫
        (boundedConstructible _).ι.map
          ((boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ (f := f) c d).hom.app A) ≫
        (boundedConstructibleLowerShriekOfCompactificationCompatibility ℓ (f := f) d).hom.app A
    let B₁ := (purityFieldCompactificationAmbientExchange ℓ f f a a' hi hp).hom.app K.obj
    let B₂ := (purityFieldCompactificationAmbientExchange ℓ f f b b' ji jp).hom.app K.obj
    let τ₁ := B₁ ≫ J a' a Q
    let τ₂ := B₂ ≫ J b' b Q
    let U := L((y₀)^*⟦Λ⟧).map (J a b K)
    (U ≫ B₂ = B₁ ≫ J a' b' Q) ∧ (U ≫ τ₂ = τ₁ ≫ J a b Q) := by
  intro Q J B₁ B₂ τ₁ τ₂ U
  have hc (c d z : Compactification f.left) : J c d Q ≫ J d z Q = J c z Q := by
    have h := ambientCompactificationComparison_trans ℓ (f := f) c d z Q
    simpa only [ambientCompactificationComparison_formula] using h
  have hr := semilinearCompactificationExchange ℓ (f := f) e x₀ y₀ wx wy sq₀ a b a' b'
    s₀ t₀ hi hp ji jp K
  simp only [ambientCompactificationComparison_formula] at hr
  have raw : U ≫ B₂ = B₁ ≫ J a' b' Q := hr
  refine ⟨raw, ?_⟩
  calc
    _ = (U ≫ B₂) ≫ J b' b Q := (Category.assoc _ _ _).symm
    _ = (B₁ ≫ J a' b' Q) ≫ J b' b Q := congrArg (· ≫ J b' b Q) raw
    _ = B₁ ≫ J a' b Q := (Category.assoc _ _ _).trans (congrArg (B₁ ≫ ·) (hc _ _ _))
    _ = _ := ((Category.assoc _ _ _).trans (congrArg (B₁ ≫ ·) (hc _ _ _))).symm

end WeilII

