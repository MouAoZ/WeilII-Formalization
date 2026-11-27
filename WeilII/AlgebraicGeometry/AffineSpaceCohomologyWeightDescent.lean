module

public import WeilII.Paper.ExternalTensorPowerConstantFieldExtension
public import WeilConjectures.WeilSheaf.Cohomology
import WeilII.AlgebraicGeometry.CompactSupportSchemeIso
import WeilConjectures.WeilSheaf.BaseChangeField.CompactSupport
import WeilConjectures.WeilSheaf.TateTwistCohomology
import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact

open AlgebraicGeometry CategoryTheory

namespace WeilII

universe u

private theorem descend {k K : Type*} [Field k] [Field K] [Finite k] [Finite K] [Algebra k K]
    {A : Type*} [Field A] (V W : FrobeniusModule.{u} A)
    (e : W.Equiv (V.powFrobenius (Module.finrank k K))) (ι : A →+* ℂ) (s : ℝ)
    (h : FrobeniusModule.HasWeightsAtMostOver K ι W s) :
    FrobeniusModule.HasWeightsAtMostOver k ι V s := by
  apply FrobeniusModule.HasWeightsAtMost.of_powFrobenius (m := Module.finrank k K)
    (ne_of_gt Module.finrank_pos)
  rw [← Module.natCard_eq_pow_finrank (K := k) (V := K)]
  exact FrobeniusModule.HasWeightsAtMost.of_equiv e.symm h

private theorem weight_of_coordinateIso
    {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))] [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (model : X ≅ Y) [model.hom.IsOver (Spec (CommRingCat.of k))]
    (H : WeilSheaf k ℓ Y) (G : WeilSheaf k ℓ X) (e : (WeilSheaf.upperStar model.hom).obj H ≅ G)
    (ι : PadicAlgCl ℓ →+* ℂ) (r : ℤ) (s : ℝ)
    (hw : FrobeniusModule.HasWeightsAtMostOver k ι (G.compactlySupportedCohomology r) s) :
    FrobeniusModule.HasWeightsAtMostOver k ι (H.compactlySupportedCohomology r) s := by
  obtain ⟨p⟩ := compactSupportEquiv_of_schemeIso model H r
  let q := WeilSheaf.compactlySupportedCohomologyEquivOfIso e r
  exact FrobeniusModule.HasWeightsAtMost.of_equiv (p.symm.trans q) hw

private theorem weight_of_fieldExtension
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar K ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    (G : WeilSheaf k ℓ X) (ι : PadicAlgCl ℓ →+* ℂ) (r : ℤ) (s : ℝ)
    (hw : FrobeniusModule.HasWeightsAtMostOver K ι
      (((WeilSheaf.baseChangeField K).obj G).compactlySupportedCohomology r) s) :
    FrobeniusModule.HasWeightsAtMostOver k ι (G.compactlySupportedCohomology r) s := by
  obtain ⟨p⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_baseChangeField K G r
  exact descend (k := k) (K := K) _ _ p ι s hw

/-- Descent of a compact-support weight bound through a finite extension of constants,
in affine-space coordinates. Source: Zhang, §2, p. 2 and proof of Proposition 1.5,
p. 4. Use the cohomology isomorphisms for the given coefficients, the affine-space
identification and constant field extension. Under their composite the new Frobenius
is the d-th power of the old one, where d is the field degree. The field cardinality
also acquires the d-th power. Taking positive d-th roots descends the eigenvalue bound. -/
public theorem affineSpace_weightBound_of_baseChangeField
    {k : Type u} [Field k] [Finite k] (K : Type u) [Field K] [Finite K] [Algebra k K]
    {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] {I : Type u} [Finite I]
    (G : WeilSheaf k ℓ 𝔸(I; Spec (CommRingCat.of k))) (ι : PadicAlgCl ℓ →+* ℂ)
    (r : ℤ) (s : ℝ) :
    letI : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
    ∀ (G' : WeilSheaf K ℓ 𝔸(I; Spec (CommRingCat.of K))),
      (affineSpaceWeilSheafBaseChangeField K G ≅ G') →
      FrobeniusModule.HasWeightsAtMostOver K ι (G'.compactlySupportedCohomology r) s →
      FrobeniusModule.HasWeightsAtMostOver k ι (G.compactlySupportedCohomology r) s := by
  intro G' e hw
  let : Fact (ringChar K ≠ ℓ) := ⟨(Algebra.ringChar_eq k K) ▸ Fact.out⟩
  apply weight_of_fieldExtension K G ι r s
  exact weight_of_coordinateIso (X := 𝔸(I; Spec (CommRingCat.of K)))
    (Y := (𝔸(I; Spec (CommRingCat.of k))).baseChangeField k K) (affineSpaceBaseChangeFieldIso k K I)
    ((WeilSheaf.baseChangeField K).obj G) G' e ι r s hw

end WeilII
