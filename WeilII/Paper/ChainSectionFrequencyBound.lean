module

public import WeilII.Targets.Lemma26
public import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Normed.Ring.Finite

/-! # The finite-field estimate in Proposition 1.5

Zhang, *On an elementary proof of Weil II*, p. 4, proof of Proposition 1.5. -/

open scoped Classical

namespace WeilII

/-- Sum the chain estimates over all nonzero frequencies. The affine-linear part of
the phase twists each coordinate weight by a character of modulus one. The constant
term is another such factor. The nonzero frequency preserves nontriviality of the
additive character acting on the chain quadratic form. Lemma 2.6 bounds each twisted chain and there are at most #L
frequencies. Source: Zhang, p. 4, proof of Proposition 1.5. -/
public theorem chainSection_frequencySum_norm_le
    {k L : Type*} [Field k] [Field L] [Algebra k L] [Fintype L]
    {n : ℕ} (hn : 2 ≤ n) (a : Fin n → k) (c : k)
    (ψ : AddChar L ℂ) (hψ : ψ ≠ 1) (t : L → ℂ) (R w : ℝ) (hR : 0 ≤ R)
    (ht : ∀ u, ‖t u‖ ≤ R * (Fintype.card L : ℝ) ^ (w / 2)) :
    ‖∑ h : Lˣ, ∑ x : Fin n → L, (∏ i, t (x i)) *
      ψ ((h : L) * MvPolynomial.eval₂ (algebraMap k L) x (chainSectionPolynomial a c))‖ ≤
      R ^ n * (Fintype.card L : ℝ) ^ (((n : ℝ) * (w + 1) + 3) / 2) := by
  classical
  let N : ℝ := Fintype.card L
  have hN : 0 < N := by dsimp [N]; positivity
  let M := R * N ^ (w / 2)
  have hM : 0 ≤ M := mul_nonneg hR (Real.rpow_nonneg hN.le _)
  let B := fun x : Fin n → L ↦ MvPolynomial.eval x (chainSectionPolynomial (0 : Fin n → L) 0)
  have eval (x : Fin n → L) :
      MvPolynomial.eval₂ (algebraMap k L) x (chainSectionPolynomial a c) =
        B x + (∑ i, algebraMap k L (a i) * x i) + algebraMap k L c := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    change MvPolynomial.eval₂Hom (algebraMap k L) x _ = _
    simp [B, chainSectionPolynomial]
  let S := fun h : Lˣ ↦ ∑ x : Fin n → L, (∏ i, t (x i)) *
    ψ ((h : L) * MvPolynomial.eval₂ (algebraMap k L) x (chainSectionPolynomial a c))
  have term (h : Lˣ) : ‖S h‖ ≤ N ^ (((n : ℝ) + 1) / 2) * M ^ n := by
    let χ := ψ.mulShift (h : L)
    have hχ : χ ≠ 1 := AddChar.IsPrimitive.of_ne_one hψ h.ne_zero
    let g := fun (i : Fin n) (u : L) ↦ t u * χ (algebraMap k L (a i) * u)
    have hg (i : Fin n) : ‖g i‖ ≤ M := by
      apply (pi_norm_le_iff_of_nonneg hM).mpr
      intro u
      simpa [g, norm_mul] using ht u
    have sumPhase (f : Fin n → L) (s : Finset (Fin n)) :
        χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => simp [hi, χ.map_add_eq_mul, ih]
    have factor : S h = χ (algebraMap k L c) * ∑ x : Fin n → L,
        (∏ i, g i (x i)) * χ (B x) := by
      dsimp only [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      change (∏ i, t (x i)) * χ _ = _
      rw [eval, χ.map_add_eq_mul, χ.map_add_eq_mul, sumPhase]
      simp only [g, Finset.prod_mul_distrib]
      ac_rfl
    rw [factor, norm_mul, AddChar.norm_apply, one_mul]
    refine (chainExponentialSum_bound hn χ hχ g).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.le _)
    simpa using Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) ↦ norm_nonneg (g i))
      (fun i (_ : i ∈ Finset.univ) ↦ hg i)
  change ‖∑ h, S h‖ ≤ _
  calc
    _ ≤ ∑ h : Lˣ, ‖S h‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Lˣ, N ^ (((n : ℝ) + 1) / 2) * M ^ n := Finset.sum_le_sum (fun h _ ↦ term h)
    _ ≤ N * (N ^ (((n : ℝ) + 1) / 2) * M ^ n) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.rpow_nonneg hN.le _) (pow_nonneg hM _))
      dsimp only [N]
      exact_mod_cast Fintype.card_le_of_injective ((↑) : Lˣ → L) Units.val_injective
    _ = _ := by
      change N * (N ^ (((n : ℝ) + 1) / 2) * (R * N ^ (w / 2)) ^ n) = R ^ n * N ^ _
      rw [mul_pow, ← Real.rpow_mul_natCast hN.le]
      rw [show ((n : ℝ) * (w + 1) + 3) / 2 = 1 + (((n : ℝ) + 1) / 2) + (w / 2) * n by ring,
        Real.rpow_add hN, Real.rpow_add hN, Real.rpow_one]
      ring

end WeilII
