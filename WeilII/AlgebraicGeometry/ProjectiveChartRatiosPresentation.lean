module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination

/-! # Presenting a morphism on a projective chart by its coordinate ratios -/

namespace WeilII

open AlgebraicGeometry CategoryTheory ProjectiveSpace

universe u

/-- On a single standard chart the pulled-back ratios present the original morphism
by a tuple whose chart coordinate is one. -/
public theorem homOfChartRatios {I : Type u} {S X : Scheme.{u}} [IsAffine S]
    (y : X ⟶ ℙ(I; S)) (b : I) (hb : ⊤ ≤ y ⁻¹ᵁ standardOpen I S b) :
    let s (j : I) := y.appLE _ ⊤ hb (coordRatio I S b j)
    ∃ hs : Ideal.span (Set.range s) = ⊤, y = homOfSections (y ≫ ℙ(I; S) ↘ S) s hs := by
  intro s
  have h : s b = 1 := by simp [s]
  have hs := (Ideal.eq_top_iff_one (Ideal.span (Set.range s))).mpr
    (Ideal.subset_span (show 1 ∈ Set.range s from ⟨b, h⟩))
  refine ⟨hs, hom_ext_of_preimage_standardOpen_eq_top b (top_unique hb) ?_ (by simp) ?_⟩
  · simp [homOfSections_preimage_standardOpen, h]
  · intro j
    exact (homOfSections_appLE_coordRatio _ _ hs h j _).symm

end WeilII
