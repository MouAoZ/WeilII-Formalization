module

import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCreatesLimits
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Tensor
import WeilII.LinearAlgebra.PositiveTensorPowerEigenvalue
import WeilII.Paper.AffineLineCompactSupportKunnethInjection
import WeilII.Targets.ExternalTensorPowerWeightBound

/-!
# The weight bound for the affine line

Dingxin Zhang, *On an elementary proof of Weil II*, Theorem 1.1 (pp. 1–2).
-/

open AlgebraicGeometry

namespace WeilII

/-- Zhang, Theorem 1.1. Let `q` be the size of the finite field `k`. If a lisse
sheaf `E` on the affine line over `k` has pointwise weight at most `w`, then every
geometric Frobenius eigenvalue on its geometric `H¹_c` has weight at most `w + 1`.

Proof (Zhang, p. 2). Fix an eigenvalue α on this cohomology group and a nonzero
eigenvector v. For every n ≥ 2, the compactly supported Künneth isomorphism identifies
the tensor product of n copies of H¹_c with the (1,…,1) summand in degree n for the
external tensor power of E. The inclusion is Frobenius-equivariant. The pure tensor
of n copies of v is nonzero, since a linear functional taking v to 1 has tensor power
taking this tensor to 1. Frobenius acts on it by αⁿ. Proposition 1.5 therefore gives
|ι(α)|ⁿ ≤ q^((n(w+1)+3)/2). Taking the positive integer n-th root gives
|ι(α)| ≤ q^((w+1)/2 + 3/(2n)). As n tends to infinity, continuity of the real power
at positive base q gives the bound |ι(α)| ≤ q^((w+1)/2). -/
public theorem affineLine_h1c_hasWeightsAtMost (k : Type*) [Field k] [Finite k]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] (ι : PadicAlgCl ℓ →+* ℂ)
    (E : ProEtale.AdicSheaf ℓ (affineLine k)) (hE : ProEtale.IsAdicLisseSheaf E) (w : ℝ)
    (hw : WeilSheaf.HasWeightsAtMost ι
      (WeilSheaf.geometricFiberPullback hE : WeilSheaf k ℓ (affineLine k)) w) :
    FrobeniusModule.HasWeightsAtMostOver k ι
      (WeilSheaf.compactlySupportedCohomology
        (WeilSheaf.geometricFiberPullback hE : WeilSheaf k ℓ (affineLine k)) 1) (w + 1) :=
    open Filter in by
  let F := WeilSheaf.geometricFiberPullback (k₀ := k) hE
  let V := WeilSheaf.compactlySupportedCohomology F 1
  let q : ℝ := Nat.card k
  have hq : 0 < q := Nat.cast_pos.mpr Nat.card_pos
  let b := (w + 1) / 2
  change V.HasWeightsAtMost ι (Nat.card k) (w + 1)
  intro α hα
  have hlim : Tendsto (fun n : ℕ ↦ b + (3 / 2 : ℝ) / n) atTop (nhds b) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := b)).add (tendsto_const_div_atTop_nhds_zero_nat (3 / 2 : ℝ))
  apply ge_of_tendsto ((Real.continuous_const_rpow hq.ne').continuousAt.tendsto.comp hlim)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn₀ : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hn
  obtain ⟨u, hu, hcomm⟩ := affineLineCompactSupportKunnethInjection F
    (WeilSheaf.isLisse_geometricFiberPullback hE) n hn
  have hW := affineLineExternalTensorPower_hnc_hasWeightsAtMost k ℓ ι E hE w hw n hn
  have hpow := FrobeniusModule.HasWeightsAtMost.of_injective
    (M := V.positiveTensorPower n hn₀) u hcomm hu hW (α ^ n)
    (FrobeniusModule.hasEigenvalue_positiveTensorPower hα n hn₀)
  rw [map_pow, norm_pow] at hpow
  apply le_of_pow_le_pow_left₀ hn₀.ne' (Real.rpow_nonneg hq.le _)
  rw [← Real.rpow_mul_natCast hq.le]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn₀.ne'
  have hexp : (b + (3 / 2 : ℝ) / n) * n = ((n : ℝ) * (w + 1) + 3) / 2 := by
    rw [add_mul, div_mul_cancel₀ _ hnR]
    dsimp [b]
    ring
  rw [hexp]
  exact hpow

end WeilII
