module

public import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-! # Nonzero frequencies in the indicator of a zero set

Zhang, *On an elementary proof of Weil II*, last step of Lemma 2.2, p. 3. -/

open scoped Classical

namespace WeilII

/-- In a weighted sum, subtracting the field cardinality times the contribution on a zero
set leaves the negative sum over nonzero frequencies. This is the last step of Zhang's
Lemma 2.2. Orthogonality evaluates the full frequency sum pointwise. Its zero frequency
contributes the unrestricted sum of the weights. -/
public theorem sub_card_mul_sum_zeros_eq_neg_sum_units
    {k L α : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    [Algebra.IsSeparable k L] [Fintype L] [Fintype α]
    (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (T : α → ℂ) (P : α → L) :
    (∑ x, T x) - (Fintype.card L : ℂ) * (∑ x : {x // P x = 0}, T x) =
      -(∑ h : Lˣ, ∑ x, T x * ψ.compTrace L ((h : L) * P x)) := by
  classical
  let freq := fun h : L ↦ ∑ x, T x * ψ.compTrace L (h * P x)
  have full : ∑ h, freq h = (Fintype.card L : ℂ) * ∑ x : {x // P x = 0}, T x := by
    dsimp only [freq]
    rw [Finset.sum_comm, Finset.mul_sum]
    simp_rw [← Finset.mul_sum]
    have orth (x : α) := AddChar.sum_compTrace_sub_mul hψ (P x) 0
    simp only [sub_zero, mul_comm (P _) _] at orth
    simp_rw [orth]
    rw [← Finset.sum_subtype (Finset.univ.filter fun x ↦ P x = 0) (by simp) T,
      Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : P x = 0 <;> simp [hx, mul_comm]
  have split := Fintype.sum_eq_add_sum_subtype_ne freq 0
  have units : (∑ h : Lˣ, freq h) = ∑ h : {h : L // h ≠ 0}, freq h :=
    unitsEquivNeZero.sum_comp (fun h : {h : L // h ≠ 0} ↦ freq h)
  have zero : freq 0 = ∑ x, T x := by simp [freq]
  rw [← full, split, zero, ← units]
  abel

end WeilII
