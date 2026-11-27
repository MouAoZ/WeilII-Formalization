module

public import WeilII.Paper.RationalLefschetzChainSection
public import WeilII.Targets.Lemma21
import WeilII.Targets.Lemma22
import WeilII.Paper.ChainSectionFrequencyBound
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import WeilConjectures.Mathlib.LinearAlgebra.Trace
import WeilConjectures.WeilSheaf.TraceFunction
import WeilConjectures.ZetaSeries

open AlgebraicGeometry CategoryTheory
open scoped Classical

namespace WeilII

universe u

/-- Zhang, Proposition 1.5, p. 4, over a field of definition of a smooth Lefschetz
chain section. Bound every stalk rank by one integer R. Degree concentration reduces
the alternating trace in Lemma 2.2 to the middle trace up to sign. The pointwise
weight bound controls the coordinate trace by R times the extension cardinality to
the power w/2. Sum Lemma 2.6 over the nonzero frequencies and apply Lemma 2.1 with
the same section and the positive constant max(1,R^n) for all positive powers. -/
public theorem externalTensorPower_weightBound_of_rationalChainSection
    (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ι : PadicAlgCl ℓ →+* ℂ) (E : ProEtale.AdicSheaf ℓ (affineLine k))
    (hE : ProEtale.IsAdicLisseSheaf E) (w : ℝ)
    (hw : WeilSheaf.HasWeightsAtMost ι (WeilSheaf.geometricFiberPullback (k₀ := k) hE) w)
    (n : ℕ) (hn : 2 ≤ n) :
    let F := WeilSheaf.geometricFiberPullback (k₀ := k) hE
    let G := affineLineExternalTensorPower F (WeilSheaf.isLisse_geometricFiberPullback hE) n
    HasRationalLefschetzChainSection G →
      FrobeniusModule.HasWeightsAtMostOver k ι (G.compactlySupportedCohomology (n : ℤ))
        ((n : ℝ) * (w + 1) + 3) := by
  intro F G hsec
  obtain ⟨a, c, h⟩ := hsec
  extract_lets S X coeff p i D at h
  obtain ⟨hi, hvan⟩ := h
  let hF : F.IsLisse := WeilSheaf.isLisse_geometricFiberPullback hE
  obtain ⟨R, hR⟩ := hF.exists_forall_finrank_stalk_le
  obtain ⟨ψ, hψ₁⟩ := AddChar.exists_apply_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0)
  have hψ : ψ ≠ 1 := fun he ↦ hψ₁ (by simp [he])
  apply affineLineExternalTensorPower_hnc_hasWeightsAtMost_of_trace_bound k ℓ ι E hE w hw n hn
  refine ⟨_, i, hi, max 1 ((R : ℝ) ^ n), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro W m hm
  let L := FiniteField.galoisExtension k m
  let : Finite L := Module.finite_of_finite k
  let := Fintype.ofFinite L
  let t := fun u : L ↦ ι (F.traceFunction m ((AffineSpace.fieldPointsEquiv k L).symm u))
  let tr := fun e : ℤ ↦ ι (LinearMap.trace (PadicAlgCl ℓ) _
    ((D.compactlySupportedCohomology e).frobeniusEnd ^ m))
  have single := finsum_eq_single (fun e : ℤ ↦ (e.negOnePow : ℤ) • tr e) (n : ℤ) (by
    intro e he
    have := hvan e he
    simp only [tr, LinearMap.trace_eq_zero_of_subsingleton, map_zero, smul_zero])
  have trace := affineLineExternalTensorPower_alternatingTrace_eq_neg_sum k ℓ ι E hE w hw
    n hn (chainSectionPolynomial a c) ψ hψ hi m hm
  have card : (Fintype.card L : ℝ) = (Nat.card k : ℝ) ^ m := by
    rw [← Nat.card_eq_fintype_card, FiniteField.nat_card_galoisExtension k m (by omega), Nat.cast_pow]
  have ht (u : L) : ‖t u‖ ≤ R * (Fintype.card L : ℝ) ^ (w / 2) := by
    rw [card, ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
    refine (WeilSheaf.norm_map_traceFunction_le hw m _).trans ?_
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hR _)) (by positivity)
  have bound := chainSection_frequencySum_norm_le hn a c (ψ.compTrace L)
    (AddChar.compTrace_ne_one hψ) t R w (Nat.cast_nonneg _) ht
  rw [card] at bound
  have sign : ‖((n : ℤ).negOnePow : ℤ) • tr n‖ = ‖tr n‖ := by
    rcases Int.units_eq_one_or (n : ℤ).negOnePow with h | h <;> simp [h]
  change ‖tr n‖ ≤ _
  rw [← sign, ← single, trace, norm_neg]
  exact bound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end WeilII
