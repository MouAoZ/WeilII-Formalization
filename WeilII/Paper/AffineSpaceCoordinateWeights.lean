module

public import WeilII.Paper.ExternalTensorPowerConstantFieldExtension
public import WeilII.AlgebraicGeometry.WeilSheafBaseChangeFieldWeights
import WeilConjectures.WeilSheaf.UpperStarPointwise

open AlgebraicGeometry

namespace WeilII

universe u

/-- Zhang, §2, change of constants. Extending a pointwise upper weight bound to affine
space in coordinates first restricts the Weil sheaf to the fiber product. Pullback
along the canonical coordinate isomorphism preserves the pointwise bound. -/
public theorem affineSpace_baseChangeField_hasWeightsAtMost
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar K ≠ ℓ)]
    {I : Type u} [Finite I] (F : WeilSheaf k ℓ 𝔸(I; Spec (CommRingCat.of k)))
    (ι : PadicAlgCl ℓ →+* ℂ) (w : ℝ) (hw : F.HasWeightsAtMost ι w) :
    (affineSpaceWeilSheafBaseChangeField K F).HasWeightsAtMost ι w := by
  have h : ((WeilSheaf.baseChangeField K).obj F).HasWeightsAtMost ι w :=
    weilSheaf_hasWeightsAtMost_baseChangeField (X := 𝔸(I; Spec (CommRingCat.of k))) K (E := F) (ι := ι) (w := w) hw
  exact WeilSheaf.HasWeightsAtMost.upperStar (k₀ := K) (l := ℓ) (ι := ι) (w := w)
    (X := 𝔸(I; Spec (CommRingCat.of K))) (Y := (𝔸(I; Spec (CommRingCat.of k))).baseChangeField k K)
    (F := (WeilSheaf.baseChangeField K).obj F) h (affineSpaceBaseChangeFieldIso k K I).hom

end WeilII
