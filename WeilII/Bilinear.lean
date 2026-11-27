module

public import WeilConjectures.FourierTransform.Classical
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.GCongr

namespace WeilII

private theorem countingL2_le {K : Type*} [Fintype K] (f : K → ℂ) :
    Real.sqrt (∑ x, ‖f x‖ ^ 2) ≤ Real.sqrt (Fintype.card K) * ‖f‖ := by
  calc
    _ ≤ Real.sqrt (∑ _x : K, ‖f‖ ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum fun x _ ↦ pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm f x) 2
    _ = _ := by simp [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg f)]

/-- The two-variable case of Zhang's Lemma 2.6 (Remark 2.7), with counting measure. -/
public theorem bilinearSum_bound {K : Type*} [Field K] [Fintype K]
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (f g : K → ℂ) :
    ‖∑ y, ∑ x, f x * g y * ψ (x * y)‖ ≤
      (Fintype.card K : ℝ) * Real.sqrt (Fintype.card K) * ‖f‖ * ‖g‖ := by
  let F := FiniteField.fourierTransform ψ f
  have hsum (y : K) : ∑ x, f x * g y * ψ (x * y) = F y * g y := by
    simp [F, FiniteField.fourierTransform, Finset.sum_mul, mul_right_comm]
  have hparseval : ∑ y, ‖F y‖ ^ 2 = (Fintype.card K : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
    simpa [F] using FiniteField.sum_norm_sq_fourierTransform (RingHom.id ℂ) hψ f
  calc
    _ = ‖∑ y, F y * g y‖ := by simp_rw [hsum]
    _ ≤ ∑ y, ‖F y‖ * ‖g y‖ := by
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun y ↦ F y * g y)
    _ ≤ Real.sqrt (∑ y, ‖F y‖ ^ 2) * Real.sqrt (∑ y, ‖g y‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ ≤ (Real.sqrt (Fintype.card K) * (Real.sqrt (Fintype.card K) * ‖f‖)) *
          (Real.sqrt (Fintype.card K) * ‖g‖) := by
      rw [hparseval, Real.sqrt_mul (Nat.cast_nonneg _)]
      gcongr <;> apply countingL2_le
    _ = _ := by
      rw [← mul_assoc (Real.sqrt (Fintype.card K)) _ ‖f‖, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      ring

end WeilII
