module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.WeilSheaf.Cohomology

open AlgebraicGeometry

namespace WeilII

/-- Zhang's Theorem 1.1 as a proof target. The size of the ground field is
recovered by `HasWeightsAtMostOver`; the stalk bounds use residue-field sizes. -/
public def AffineLineWeightBound (k : Type*) [Field k] [Finite k]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] (ι : PadicAlgCl ℓ →+* ℂ) : Prop :=
  ∀ (E : WeilSheaf k ℓ (affineLine k)) (w : ℝ), E.IsLisse → E.HasWeightsAtMost ι w →
    (E.compactlySupportedCohomology 1).HasWeightsAtMostOver k ι (w + 1)

end WeilII
