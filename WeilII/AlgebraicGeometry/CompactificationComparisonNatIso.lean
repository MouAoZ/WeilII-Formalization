module

public import WeilII.AlgebraicGeometry.ProperRefinementNaturalIso
meta import WeilConjectures.Tactic.ExactByKernel

/-! # Compactification comparison isomorphisms under a change of field structure -/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilII

universe u

variable {k : Type u} [Field k] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    {a : X.left ⟶ Spec (.of k)} {b : Y.left ⟶ Spec (.of k)}
    [LocallyOfFiniteType (Over.mk a).hom] [QuasiCompact (Over.mk a).hom] [IsSeparated (Over.mk a).hom]
    [LocallyOfFiniteType (Over.mk b).hom] [QuasiCompact (Over.mk b).hom] [IsSeparated (Over.mk b).hom]
    (wf : f.left ≫ b = a)

local notation "f₁" => Over.homMk (U := Over.mk a) (V := Over.mk b) f.left wf

/-- Changing the field structures preserves the full natural comparison isomorphism. Compute
both comparisons on the same two proper refinements. The formula for each refinement in
`LowerShriek/ExchangeFormalism.lean` uses the same underlying pullback constraints and
restricted adjunctions, hence gives the same natural transformation for both structures. -/
public theorem compactificationComparisonIso_changeStructure (p q : Compactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (f := f₁) p q =
      boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (f := f) p q := by
  obtain ⟨d, ⟨r⟩, ⟨s⟩⟩ := Compactification.exists_overRefinement p q
  let lift {v : Compactification f.left} (t : Compactification.OverRefinement d v) :=
    Compactification.overRefinementOfRefinement (f := f₁) t.toRefinement t.isPullback_left
  have left := boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_trans_symm ℓ
    (lift r) (lift s)
  have right := boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl_eq_trans_symm ℓ r s
  let F (v : Compactification f.left) := boundedConstructibleLowerShriekOfCompactification ℓ (f := f) v
  let join (i : F p ≅ F d) (j : F q ≅ F d) := i ≪≫ j.symm
  let R : F p ≅ F d := boundedConstructibleLowerShriekOverRefinementIso ℓ r
  let S : F q ≅ F d := boundedConstructibleLowerShriekOverRefinementIso ℓ s
  let R₁ : F p ≅ F d := by exact_by_kernel (boundedConstructibleLowerShriekOverRefinementIso ℓ (lift r))
  let S₁ : F q ≅ F d := by exact_by_kernel (boundedConstructibleLowerShriekOverRefinementIso ℓ (lift s))
  have hr : R₁ = R := by exact_by_kernel (properRefinementIso_changeStructure ℓ f wf r)
  have hs : S₁ = S := by exact_by_kernel (properRefinementIso_changeStructure ℓ f wf s)
  let L₁ : F p ≅ F q := by
    exact_by_kernel (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ (f := f₁) p q)
  let L : F p ≅ F q := boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ p q
  have step₁ : L₁ = join R₁ S₁ := by exact_by_kernel left
  have step₂ : join R S = L := right.symm
  have conclusion := step₁.trans ((congrArg₂ join hr hs).trans step₂)
  exact_by_kernel conclusion

end WeilII
