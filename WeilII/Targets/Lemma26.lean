module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import WeilII.Paper.ChainSectionPolynomial
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.FourierTransform.Classical

/-!
# Zhang's bound for the chain exponential sum

Lemma 2.6 of Dingxin Zhang, *On an Elementary Proof of Weil II*, pp. 4–5,
bounds a complete sum over a finite field with one weight function per coordinate.
-/

public section

namespace WeilII

/-- The chain phase of Lemma 2.6 with one extra edge to the fixed coordinate `y`. -/
private def chainPhase {K : Type*} [Field K] {m : ℕ} (x : Fin m → K) (y : K) : K :=
  ∑ i, x i * Fin.snoc (α := fun _ ↦ K) x y i.succ

/-- Zhang's iterated Fourier sum, with its terminal coordinate held fixed. -/
private noncomputable def chainTransform {K : Type*} [Field K] [Fintype K]
    (ψ : AddChar K ℂ) {m : ℕ} (t : Fin m → K → ℂ) (y : K) : ℂ :=
  ∑ x : Fin m → K, (∏ i, t i (x i)) * ψ (chainPhase x y)

/-- Appending a coordinate multiplies by its weight and takes one Fourier transform. -/
private theorem chainTransform_succ {K : Type*} [Field K] [Fintype K]
    (ψ : AddChar K ℂ) {m : ℕ} (t : Fin (m + 1) → K → ℂ) :
    chainTransform ψ t = FiniteField.fourierTransform ψ
      (fun z ↦ chainTransform ψ (fun i ↦ t (Fin.castSucc i)) z * t (Fin.last m) z) := by
  classical
  funext y
  have phase (x : Fin m → K) (z : K) :
      chainPhase (Fin.snoc (α := fun _ ↦ K) x z) y = chainPhase x z + z * y := by
    unfold chainPhase
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last]
  rw [chainTransform, ← (Fin.snocEquiv (fun _ : Fin (m + 1) ↦ K)).sum_comp,
    Fintype.sum_prod_type]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, FiniteField.fourierTransform, Algebra.trace_self_apply]
  apply Finset.sum_congr rfl
  intro z _
  simp only [chainTransform, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fin.prod_univ_castSucc, phase, ψ.map_add_eq_mul]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ac_rfl

/-- The squared counting norm after `m` transforms, by Zhang's Plancherel induction. -/
private theorem chainTransform_energy {K : Type*} [Field K] [Fintype K]
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) {m : ℕ} (t : Fin m → K → ℂ) :
    ∑ y, ‖chainTransform ψ t y‖ ^ 2 ≤
      (Fintype.card K : ℝ) ^ (m + 1) * (∏ i, ‖t i‖) ^ 2 := by
  classical
  induction m with
  | zero => simp [chainTransform, chainPhase]
  | succ m ih =>
    let a := chainTransform ψ (fun i : Fin m ↦ t i.castSucc)
    let g := t (Fin.last m)
    have parseval := FiniteField.sum_norm_sq_fourierTransform (RingHom.id ℂ) hψ
      (fun z ↦ a z * g z)
    rw [chainTransform_succ]
    simp only [RingHom.id_apply] at parseval
    rw [parseval]
    calc
      _ ≤ (Fintype.card K : ℝ) * ∑ z, ‖a z‖ ^ 2 * ‖g‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro z _
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm g z) 2) (sq_nonneg _)
      _ ≤ (Fintype.card K : ℝ) *
          (((Fintype.card K : ℝ) ^ (m + 1) * (∏ i : Fin m, ‖t i.castSucc‖) ^ 2) *
            ‖g‖ ^ 2) := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (ih _) (sq_nonneg _)) (Nat.cast_nonneg _)
      _ = _ := by
        rw [Fin.prod_univ_castSucc, pow_succ (Fintype.card K : ℝ) (m + 1), mul_pow]
        dsimp [g]
        ring

/-- Zhang, *On an Elementary Proof of Weil II*, Lemma 2.6, pp. 4–5.
The phase is the sum of the products of consecutive coordinates. Each function norm on
the right is the maximum of its pointwise absolute values over the field.

Write `Aₘ(y)` for the weighted sum on the first `m` coordinates with an extra edge
from the final coordinate to `y`. The empty chain gives the constant function one,
whose squared counting norm is `q = #K`. Splitting off the last coordinate shows
that appending a weight `g` sends `Aₘ` to the Fourier transform of `Aₘ · g`.
Pointwise multiplication increases the squared counting norm by at most the factor
`‖g‖²`, and Plancherel multiplies it by `q`. After all `n` steps the squared
counting norm is at most `q^(n+1) ∏ᵢ ‖tᵢ‖²`. At `y = 0` the extra edge vanishes,
so the desired squared modulus is one summand in this bound. Taking square roots
gives the stated exponent. -/
theorem chainExponentialSum_bound {K : Type*} [Field K] [Fintype K] {n : ℕ} (hn : 2 ≤ n)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (t : Fin n → K → ℂ) :
    ‖∑ x : Fin n → K, (∏ i, t i (x i)) *
        ψ (MvPolynomial.eval x (chainSectionPolynomial (0 : Fin n → K) 0))‖ ≤
      (Fintype.card K : ℝ) ^ (((n : ℝ) + 1) / 2) * ∏ i, ‖t i‖ := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have phase (x : Fin (m + 1) → K) :
      MvPolynomial.eval x (chainSectionPolynomial (0 : Fin (m + 1) → K) 0) =
        chainPhase x 0 := by
    simp only [chainSectionPolynomial, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero,
      add_zero, map_sum, map_mul, MvPolynomial.eval_X]
    unfold chainPhase
    rw [Fin.sum_univ_castSucc (n := m)]
    simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last,
      mul_zero, add_zero]
  simp_rw [phase]
  change ‖chainTransform ψ t 0‖ ≤ _
  have pointwise : ‖chainTransform ψ t 0‖ ^ 2 ≤ ∑ y, ‖chainTransform ψ t y‖ ^ 2 :=
    Finset.single_le_sum (fun y _ ↦ sq_nonneg ‖chainTransform ψ t y‖) (Finset.mem_univ 0)
  calc
    _ ≤ √((Fintype.card K : ℝ) ^ (m.succ + 1) * (∏ i, ‖t i‖) ^ 2) :=
      Real.le_sqrt_of_sq_le (pointwise.trans (chainTransform_energy ψ hψ t))
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow,
        ← Real.rpow_natCast_mul (Nat.cast_nonneg _), Nat.cast_add_one, mul_one_div]

end WeilII
