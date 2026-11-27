module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.BaseChangeIndependence

/-! # Compactification comparisons under a change of field structure on the same schemes -/

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) {a : X.left ⟶ Spec (.of k)} {b : Y.left ⟶ Spec (.of k)}
    [LocallyOfFiniteType (Over.mk a).hom] [QuasiCompact (Over.mk a).hom] [IsSeparated (Over.mk a).hom]
    [LocallyOfFiniteType (Over.mk b).hom] [QuasiCompact (Over.mk b).hom] [IsSeparated (Over.mk b).hom] (w : f.left ≫ b = a)

local notation "f₁" => Over.homMk (U := Over.mk a) (V := Over.mk b) f.left w

private noncomputable abbrev component {f : X ⟶ Y} {e c : Compactification f.left}
    (r : Compactification.OverRefinement e c) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) c).obj K.obj ≅
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ) e).obj K.obj :=
  (boundedConstructible _).ι.mapIso ((boundedConstructibleLowerShriekOverRefinementIso ℓ r).app K)

private theorem comparison_via {f : X ⟶ Y} {e c d : Compactification f.left}
    (r : Compactification.OverRefinement e c) (s : Compactification.OverRefinement e d)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c d).hom.app K).hom =
      (component ℓ r K).hom ≫ (component ℓ s K).inv :=
  congrArg (fun η ↦ ((Iso.hom η).app K).hom)
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_trans_symm ℓ r s)

/-- For a fixed proper refinement, its component in the underlying derived category
is independent of the two structure maps to the field. In the definition of the
refinement isomorphism (LowerShriekIndependence, refinement formula), the identity,
open/proper exchange and composition all have the same underlying scheme arrows. The
pullback constraints restrict the ambient ones, and the pushforward constraints
and the open exchange are their mates under the restricted adjunctions. Units and
counits of the latter are the restrictions of the ambient units and counits. This
identifies each of the three factors for the same refinement in the second slice. -/
public theorem refinementIso_changeStructure {c d : Compactification f.left}
    (r : Compactification.OverRefinement c d) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructible _).ι.mapIso ((boundedConstructibleLowerShriekOverRefinementIso ℓ
      (Compactification.overRefinementOfRefinement (f := f₁) r.toRefinement r.isPullback_left)).app K) =
        (boundedConstructible _).ι.mapIso ((boundedConstructibleLowerShriekOverRefinementIso ℓ r).app K) := by
  let r₁ := Compactification.overRefinementOfRefinement (f := f₁) r.toRefinement r.isPullback_left
  let unprime := fun {U V : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
      [IsSeparated U.hom] [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
      {g : U ⟶ V} {e d : Compactification g.left} (s : Compactification.OverRefinement e d) ↦
    haveI := s.isProper
    haveI := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
      s.isPullback
    haveI := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicAlgCl ℓ
      s.isPullback
    boundedConstructibleLowerShriekRefinementIso_eq' ℓ s.isPullback s.hom_overG
  have h := unprime (g := f) r
  have h₁ := unprime (g := f₁) r₁
  have left := congrArg (fun η ↦ (boundedConstructible _).ι.mapIso (Iso.app η K)) h₁.symm
  have right := congrArg (fun η ↦ (boundedConstructible _).ι.mapIso (Iso.app η K)) h
  refine left.trans (Eq.trans ?_ right)
  -- The unprimed comparisons use the same open immersions and proper scheme maps.
  -- Let the kernel compare the components without elaborator unfolding of their functors.
  open Lean Meta Elab Tactic in
  run_tac
    let goal ← getMainGoal
    let some (_, lhs, _) := (← goal.getType).eq? | throwError "expected an equality"
    goal.assign (← mkEqRefl lhs)
    replaceMainGoal []

/-- Compare two chosen compactifications using the same common refinement in both
field structures. The two factors agree by invariance of one refinement component. -/
public theorem compactificationComparison_changeStructure (c d : Compactification f.left)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (f := f₁) c d).hom.app K).hom =
      ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ c d).hom.app K).hom := by
  obtain ⟨e, ⟨r⟩, ⟨s⟩⟩ := Compactification.exists_overRefinement c d
  let r₁ := Compactification.overRefinementOfRefinement (f := f₁) r.toRefinement r.isPullback_left
  let s₁ := Compactification.overRefinementOfRefinement (f := f₁) s.toRefinement s.isPullback_left
  have hr : component ℓ r₁ K = component ℓ r K := refinementIso_changeStructure ℓ f w r K
  have hs : component ℓ s₁ K = component ℓ s K := refinementIso_changeStructure ℓ f w s K
  exact (comparison_via ℓ r₁ s₁ K).trans (((congrArg₂ (· ≫ ·) (congrArg Iso.hom hr)
    (congrArg Iso.inv hs))).trans (comparison_via ℓ r s K).symm)

end WeilII
