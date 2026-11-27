module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence
meta import WeilConjectures.Tactic.RflByKernel

/-! # Reindexing a compactification comparison along a base automorphism -/

public noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilII

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}
  (e : Spec (.of k) ≅ Spec (.of k))

/-- The same proper refinement over the postcomposed structure morphisms. -/
def reindexCompactificationRefinement {d a : Compactification f.left}
    (r : Compactification.OverRefinement d a) :
    Compactification.OverRefinement (f := (Over.map e.hom).map f) d a :=
  Compactification.overRefinementOfRefinement r.toRefinement r.isPullback_left

variable [LocallyOfFiniteType ((Over.map e.hom).obj X).hom] [QuasiCompact ((Over.map e.hom).obj X).hom]
  [IsSeparated ((Over.map e.hom).obj X).hom] [LocallyOfFiniteType ((Over.map e.hom).obj Y).hom]
  [QuasiCompact ((Over.map e.hom).obj Y).hom] [IsSeparated ((Over.map e.hom).obj Y).hom]

/-- A refinement component with its underlying source and target fixed. -/
def compactificationRefinementComponent {d a : Compactification f.left}
    (r : Compactification.OverRefinement d a)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) a).obj K.obj ≅
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) d).obj K.obj :=
  (boundedConstructible _).ι.mapIso ((boundedConstructibleLowerShriekOverRefinementIso ℓ r).app K)

/-- Reindexing one proper refinement leaves its comparison unchanged.
Source: LowerShriekIndependence and OpenLowerShriekBaseChange. The same underlying
proper map refines the same two opens after reindexing. Expand the refinement comparison
as identity direct image, the open/proper exchange, and composition of proper direct images.
Identity and composition of direct images are the right adjoints of the pullback constraints
on the same underlying scheme maps. The mixed exchange is the right mate of the open exchange,
whose inverse is the left mate of the pullback square. Restricting the adjunctions to the
full subcategories preserves their units and counits, so every one of these factors has
the same components before and after reindexing. Their composites agree. -/
theorem refinementIso_reindex {d a : Compactification f.left}
    (r : Compactification.OverRefinement d a) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    compactificationRefinementComponent ℓ (reindexCompactificationRefinement e r) K =
      compactificationRefinementComponent ℓ r K := by
  let reindexed := reindexCompactificationRefinement e r
  have := r.isProper
  have := reindexed.isProper
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    r.isPullback
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    reindexed.isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    r.isPullback
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
    reindexed.isPullback
  have original := boundedConstructibleLowerShriekRefinementIso_eq' ℓ r.isPullback r.hom_overG
  have transported := boundedConstructibleLowerShriekRefinementIso_eq' ℓ
    reindexed.isPullback reindexed.hom_overG
  have left := congrArg (fun η ↦ (boundedConstructible _).ι.mapIso (Iso.app η K)) transported.symm
  have right := congrArg (fun η ↦ (boundedConstructible _).ι.mapIso (Iso.app η K)) original
  refine left.trans (Eq.trans ?_ right)
  -- The unprimed construction uses the same underlying open and proper maps in both slices.
  rfl_by_kernel

private theorem comparisonComponent_refinement {a b d : Compactification f.left}
    (r : Compactification.OverRefinement d a) (s : Compactification.OverRefinement d b)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ a b).hom.app K).hom =
      (compactificationRefinementComponent ℓ r K).hom ≫ (compactificationRefinementComponent ℓ s K).inv :=
  congrArg (fun η ↦ ((Iso.hom η).app K).hom)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_trans_symm ℓ r s)

/-- The comparison between two compactifications is independent of postcomposition of
the structure maps with a base automorphism. Compute both sides from the same
underlying proper refinement using the refinement formula. -/
theorem compactificationComparison_reindex (a b : Compactification f.left)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
        (f := (Over.map e.hom).map f) a b).hom.app K).hom =
      ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ a b).hom.app K).hom := by
  obtain ⟨d, ⟨r⟩, ⟨s⟩⟩ := Compactification.exists_overRefinement a b
  have h := comparisonComponent_refinement ℓ
    (reindexCompactificationRefinement e r) (reindexCompactificationRefinement e s) K
  rw [refinementIso_reindex, refinementIso_reindex] at h
  exact h.trans (comparisonComponent_refinement ℓ r s K).symm

end WeilII
